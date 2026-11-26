import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.Final50ActiveCyclePrice
import ProximityPrize.SubmissionLower.LibraryMathlib_Algebra_MvPolynomial_Coeff
import ProximityPrize.SubmissionLower.Low48BentCyclePrice
import ProximityPrize.SubmissionLower.Low6966ActiveCycleCaps
import ProximityPrize.SubmissionLower.R6960ExceptionalStage
import ProximityPrize.SubmissionLower.R6960Low6960ActiveCyclePrice

section Merged6967_Final50ActiveCycleMixed
set_option Elab.async false


set_option Elab.async false

-- merged module Shared50BentCaps
section Merged_Shared50BentCaps

-- merged module Final50ActiveCycleChart
section Merged_Final50ActiveCycleChart

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle

noncomputable section

open Polynomial
open P3 (K)
open Final50Price (physicalDegree taylorLength)
open K1_13 (Row shape extend InBox Shape)
open Low48BentCycle (Family rawFamily)
open K1_13_6 (GeoField toGeneric)
open K1_13_6_2 (GeoJets5 actualPoint)
open K1_13_6_2_2 (generic5 rawGraph numerator denominator padded padded_last)
open Final50GeometryCut_2 (Branch branch_box)
open MvPolynomial








end

end Final50ActiveCycle

end Merged_Final50ActiveCycleChart

-- merged module Shared50BentCaps
section Merged_Shared50BentCaps
set_option Elab.async false
namespace Shared50BentCaps
noncomputable section

open K1_13 (Shape Row shape)
open K1_13_6 (GeoField)
open Final50Price (taylorLength)
open Low48BentLattice (Cap Allowed Chamber latticePoints)
open Low48BentSupport (graph lifted)
open Low48BentCycle (Family rawFamily capFamily capSum ambient_cap integral mixedDegree)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators
open Low48BentCycle (slots ambient_list)














end
end Shared50BentCaps

end Merged_Shared50BentCaps

end Merged_Shared50BentCaps

-- merged module Final50ActiveCycleMixed
section Merged_Final50ActiveCycleMixed

set_option autoImplicit false
set_option Elab.async false

namespace Final50ActiveCycle

noncomputable section

open Polynomial MvPolynomial
open P3 (K)
open Final50GeometryCut ( CutInput )
open Final50GeometryCut_2 (Branch )
open Final50Price (primaryBox tiltedSurface)
open K1_13 (Row extend embed shape)
open Low48BentCycle (Family mixedDegree rawFamily capFamily)
open K1_13_6 (Pieces CurveSections toGeneric)
open K1_13_6_2 (JetPoint actualPoint actualPoint_injective Demand maximal_demand)
open K1_13_6_2_4 (oldEmbedding)
open scoped BigOperators





end

end Final50ActiveCycle


end Merged_Final50ActiveCycleMixed

end Merged6967_Final50ActiveCycleMixed

section Merged6967_Shared50CycleBound
set_option Elab.async false


set_option Elab.async false

set_option autoImplicit false
set_option Elab.async false

namespace Shared50CycleBound

noncomputable section

open Low48BentCycle (Family mixedDegree properCut cycleComparison divisorBound diagonalExponents)

open Final50Price (SmallFactor)
open Final50GeometryCut_2 (Branch)
open P0_9_6_2_3 (cylinder_comparison)
open K1_13 (Row)
open K1_13_6 (GeoJets GeoField toGeneric intersectionIdeal cycleLength)
open K1_13_6_2 (JetPoint GeoJets5)
open K1_13_6_2_4 (Exponent Component DimLE OfDim LengthAt ambient_dim cylinder cylinder_injective
  dim_le_after_section oldEmbedding pointIdeal sectionIdeal)
open K1_13_6_2_4_1 (positiveDiagonal)
open MvPolynomial
open scoped BigOperators Pointwise




end

end Shared50CycleBound

end Merged6967_Shared50CycleBound

section Merged6967_Shared50CycleFour
set_option Elab.async false

set_option Elab.async false

namespace Shared50CycleFour
noncomputable section
open Final50Price (SmallFactor primaryBox taylorLength)
open Final50GeometryCut (membershipTest)
open Final50GeometryCut_2 (Branch Slice4 )
open K1_13 (Row Shape shape InBox chart mixed32 volume32 difference)
open K1_13_6 (GeoJets GeoField toGeneric divisorIdeal cycleLength intersectionIdeal separant)
open K1_13_6_2 (JetPoint Box4)
open K1_13_6_2_3 (ChamberBox dimension capCoeff polarize mixedDegree localWeight pointIdeal
  chart_box generic_box regular_cut cut_dimension dimension_bot pair_regular intersection_eq
  surface_dimension weight_cast weight_pos point_injective point_prime point_degree point_proper_section)
open scoped BigOperators


end
end Shared50CycleFour

end Merged6967_Shared50CycleFour

section Merged6967_High6966RescueData
set_option Elab.async false


set_option Elab.async false
namespace Lower6960.Rescue6966Source
open K1_14 (Shape)
open P1_7 (Bank)
open K1_14_2_2_4 (pairCap)
structure Step where
  source : Bank
  order : ℕ
  safe : 0<source.shape.J ∧ source.shape.J≤source.shape.B ∧ source.shape.B<K1.p ∧
    source.shape.U<K1.p ∧ source.shape.m*179759<K1.p
  small : order<K1.p
  room : 2*2522*order<source.shape.m*179759
structure Route where
  degree : ℕ
  upper : ℕ
  stages : Fin 17 → Step
  pos : 1≤degree
  zero : (stages 0).order=0
  small : ∀ k : Fin 4, pairCap (⟨0,degree,1,upper⟩:Shape) ((stages 0).source.shape) k<K1.p
  pivot : Fin 2 → Fin 17
  bound : Fin 2 → ℕ
  tight : ∀ k : Fin 2, pairCap (⟨0,degree,1,upper⟩:Shape) ((stages (pivot k)).source.shape)
      (Fin.castLE (by decide : 2≤4) k) < ((stages (pivot k)).order+1)*(bound k+1)
  degree_cap : bound 0≤157

private def s0 : Step := ⟨⟨⟨913,1274,274,70667⟩,22869055897600,72278016338⟩,0,by decide,by decide,by decide⟩
private def s1 : Step := ⟨⟨⟨1007,1405,302,77045⟩,30653695393792,106799856912⟩,1,by decide,by decide,by decide⟩
private def s2 : Step := ⟨⟨⟨1156,1613,347,81404⟩,46376998666240,185502762679⟩,2,by decide,by decide,by decide⟩
private def s3 : Step := ⟨⟨⟨1482,2068,445,85215⟩,97653165391872,500730734846⟩,3,by decide,by decide,by decide⟩
private def s4 : Step := ⟨⟨⟨1704,2378,511,104484⟩,148231870742528,874078075528⟩,6,by decide,by decide,by decide⟩
private def s5 : Step := ⟨⟨⟨2093,2921,628,116994⟩,274660672143360,1989358623137⟩,8,by decide,by decide,by decide⟩
private def s6 : Step := ⟨⟨⟨2093,2921,628,146327⟩,274660672143360,1989358623137⟩,12,by decide,by decide,by decide⟩
private def s7 : Step := ⟨⟨⟨2538,3542,761,179489⟩,489286602588160,4296679719083⟩,17,by decide,by decide,by decide⟩
private def s8 : Step := ⟨⟨⟨1940,2707,582,219253⟩,218735576350720,1467723847114⟩,16,by decide,by decide,by decide⟩
private def s9 : Step := ⟨⟨⟨3028,4226,908,173742⟩,830714806272000,8703717248479⟩,17,by decide,by decide,by decide⟩
private def s10 : Step := ⟨⟨⟨3877,5411,1163,224258⟩,1743568608690176,23389476977098⟩,25,by decide,by decide,by decide⟩
private def s11 : Step := ⟨⟨⟨1948,2719,584,277594⟩,221335049994240,1492745996263⟩,18,by decide,by decide,by decide⟩
private def s12 : Step := ⟨⟨⟨2251,3141,675,343663⟩,341464862162944,2658401808400⟩,23,by decide,by decide,by decide⟩
private def s13 : Step := ⟨⟨⟨4135,5771,1240,280759⟩,2114656146554880,30253081279145⟩,33,by decide,by decide,by decide⟩
private def s14 : Step := ⟨⟨⟨4774,6663,1432,274830⟩,3254472040251392,53757553058289⟩,33,by decide,by decide,by decide⟩
private def s15 : Step := ⟨⟨⟨2768,3863,803,307658⟩,618805432156160,5922866008688⟩,24,by decide,by decide,by decide⟩
private def s16 : Step := ⟨⟨⟨3578,4993,1073,448025⟩,1370321365237760,16957563831998⟩,40,by decide,by decide,by decide⟩
private def s17 : Step := ⟨⟨⟨898,1253,269,68441⟩,21731605217280,67542002002⟩,0,by decide,by decide,by decide⟩
private def s18 : Step := ⟨⟨⟨1007,1405,302,73764⟩,30653695393792,106799856912⟩,1,by decide,by decide,by decide⟩
private def s19 : Step := ⟨⟨⟨1217,1698,365,85182⟩,54066727616512,227606727472⟩,3,by decide,by decide,by decide⟩
private def s20 : Step := ⟨⟨⟨1663,2321,499,93728⟩,137859039232000,793615206921⟩,5,by decide,by decide,by decide⟩
private def s21 : Step := ⟨⟨⟨1838,2565,551,99806⟩,185938796871680,1182570018933⟩,6,by decide,by decide,by decide⟩
private def s22 : Step := ⟨⟨⟨2032,2836,610,111856⟩,251451338391552,1768487180381⟩,8,by decide,by decide,by decide⟩
private def s23 : Step := ⟨⟨⟨2093,2921,628,140098⟩,274660672143360,1989358623137⟩,12,by decide,by decide,by decide⟩
private def s24 : Step := ⟨⟨⟨2558,3570,767,148437⟩,500939249156096,4434008324066⟩,14,by decide,by decide,by decide⟩
private def s25 : Step := ⟨⟨⟨2589,3613,777,179361⟩,519720973893632,4654956318519⟩,18,by decide,by decide,by decide⟩
private def s26 : Step := ⟨⟨⟨2013,2809,604,218012⟩,244377702891520,1701721319759⟩,17,by decide,by decide,by decide⟩
private def s27 : Step := ⟨⟨⟨3700,5164,1110,215130⟩,1515691726602240,19405049205455⟩,25,by decide,by decide,by decide⟩
private def s28 : Step := ⟨⟨⟨4271,5961,1281,238935⟩,2330461376872448,34440377265092⟩,29,by decide,by decide,by decide⟩
private def s29 : Step := ⟨⟨⟨2276,3176,683,318055⟩,353158876889088,2780324254692⟩,23,by decide,by decide,by decide⟩
private def s30 : Step := ⟨⟨⟨5426,7573,1628,332558⟩,4778673736777728,89712770855631⟩,44,by decide,by decide,by decide⟩
private def s31 : Step := ⟨⟨⟨2273,3172,682,363472⟩,351726004862976,2765910980015⟩,24,by decide,by decide,by decide⟩
private def s32 : Step := ⟨⟨⟨4270,5959,1281,466848⟩,2329241279791104,34403208852529⟩,48,by decide,by decide,by decide⟩
private def s33 : Step := ⟨⟨⟨3393,4735,1018,497020⟩,1169070071480320,13720983207995⟩,40,by decide,by decide,by decide⟩
private def s34 : Step := ⟨⟨⟨913,1274,274,62076⟩,22869055897600,72278016338⟩,0,by decide,by decide,by decide⟩
private def s35 : Step := ⟨⟨⟨1007,1405,302,67675⟩,30653695393792,106799856912⟩,1,by decide,by decide,by decide⟩
private def s36 : Step := ⟨⟨⟨1214,1694,364,70229⟩,53657153044480,225404613013⟩,2,by decide,by decide,by decide⟩
private def s37 : Step := ⟨⟨⟨1396,1948,419,74914⟩,81610237542400,394206147308⟩,3,by decide,by decide,by decide⟩
private def s38 : Step := ⟨⟨⟨1704,2378,511,85815⟩,148231870742528,874078075528⟩,5,by decide,by decide,by decide⟩
private def s39 : Step := ⟨⟨⟨1883,2628,565,96916⟩,200058078756864,1303840388938⟩,7,by decide,by decide,by decide⟩
private def s40 : Step := ⟨⟨⟨2093,2921,628,128474⟩,274660672143360,1989358623137⟩,12,by decide,by decide,by decide⟩
private def s41 : Step := ⟨⟨⟨2535,3538,760,157760⟩,487505563484160,4276697639028⟩,17,by decide,by decide,by decide⟩
private def s42 : Step := ⟨⟨⟨2972,4148,892,152318⟩,786027838963712,8084380042177⟩,17,by decide,by decide,by decide⟩
private def s43 : Step := ⟨⟨⟨1995,2784,598,204645⟩,237704260878336,1640652401644⟩,17,by decide,by decide,by decide⟩
private def s44 : Step := ⟨⟨⟨3702,5167,1111,224981⟩,1518566705725440,19455018383557⟩,29,by decide,by decide,by decide⟩
private def s45 : Step := ⟨⟨⟨4652,6493,1396,235446⟩,3012346810204160,48493835261734⟩,32,by decide,by decide,by decide⟩
private def s46 : Step := ⟨⟨⟨2276,3176,683,294186⟩,353158876889088,2780324254692⟩,23,by decide,by decide,by decide⟩
private def s47 : Step := ⟨⟨⟨2273,3172,682,337055⟩,351726004862976,2765910980015⟩,24,by decide,by decide,by decide⟩
private def s48 : Step := ⟨⟨⟨3393,4735,1018,460156⟩,1169070071480320,13720983207995⟩,40,by decide,by decide,by decide⟩
private def s49 : Step := ⟨⟨⟨2940,4103,882,207556⟩,760663600005120,7737192065011⟩,24,by decide,by decide,by decide⟩
private def s50 : Step := ⟨⟨⟨4726,6596,1418,287816⟩,3157997854916608,51639732701187⟩,40,by decide,by decide,by decide⟩
private def s51 : Step := ⟨⟨⟨873,1218,262,49772⟩,19998066343936,60409680278⟩,0,by decide,by decide,by decide⟩
private def s52 : Step := ⟨⟨⟨1007,1405,302,52325⟩,30653695393792,106799856912⟩,1,by decide,by decide,by decide⟩
private def s53 : Step := ⟨⟨⟨1216,1697,365,54129⟩,53967472820224,227175932601⟩,2,by decide,by decide,by decide⟩
private def s54 : Step := ⟨⟨⟨1396,1948,419,57702⟩,81610237542400,394206147308⟩,3,by decide,by decide,by decide⟩
private def s55 : Step := ⟨⟨⟨1542,2152,463,61828⟩,109983842697216,587011804740⟩,4,by decide,by decide,by decide⟩
private def s56 : Step := ⟨⟨⟨1885,2631,566,74633⟩,200803738189824,1310440503210⟩,7,by decide,by decide,by decide⟩
private def s57 : Step := ⟨⟨⟨2093,2921,628,87928⟩,274660672143360,1989358623137⟩,10,by decide,by decide,by decide⟩
private def s58 : Step := ⟨⟨⟨2539,3544,762,104936⟩,490208099827712,4308903409784⟩,14,by decide,by decide,by decide⟩
private def s59 : Step := ⟨⟨⟨2589,3613,777,127137⟩,519720973893632,4654956318519⟩,18,by decide,by decide,by decide⟩
private def s60 : Step := ⟨⟨⟨1998,2788,599,159761⟩,238807967334400,1650397239853⟩,17,by decide,by decide,by decide⟩
private def s61 : Step := ⟨⟨⟨3700,5164,1110,151973⟩,1515691726602240,19405049205455⟩,25,by decide,by decide,by decide⟩
private def s62 : Step := ⟨⟨⟨3922,5474,1177,170521⟩,1805549010419712,24504963564053⟩,29,by decide,by decide,by decide⟩
private def s63 : Step := ⟨⟨⟨2276,3176,683,232730⟩,353158876889088,2780324254692⟩,23,by decide,by decide,by decide⟩
private def s64 : Step := ⟨⟨⟨5426,7573,1628,240649⟩,4778673736777728,89712770855631⟩,45,by decide,by decide,by decide⟩
private def s65 : Step := ⟨⟨⟨3396,4739,1019,363819⟩,1172259956326400,13768862603305⟩,40,by decide,by decide,by decide⟩
private def s66 : Step := ⟨⟨⟨3218,4491,965,461838⟩,997035472584704,11100167661469⟩,40,by decide,by decide,by decide⟩
private def s67 : Step := ⟨⟨⟨3396,4739,1019,499378⟩,1172259956326400,13768862603305⟩,43,by decide,by decide,by decide⟩
private def s68 : Step := ⟨⟨⟨856,1193,258,30079⟩,18915833151488,55840695568⟩,0,by decide,by decide,by decide⟩
private def s69 : Step := ⟨⟨⟨964,1344,291,31994⟩,27031739301888,89958515582⟩,1,by decide,by decide,by decide⟩
private def s70 : Step := ⟨⟨⟨964,1344,291,38688⟩,27031739301888,89958515582⟩,2,by decide,by decide,by decide⟩
private def s71 : Step := ⟨⟨⟨1100,1533,332,38729⟩,40133103452160,152180262044⟩,3,by decide,by decide,by decide⟩
private def s72 : Step := ⟨⟨⟨1178,1642,355,41803⟩,49219016065024,199962033930⟩,4,by decide,by decide,by decide⟩
private def s73 : Step := ⟨⟨⟨1284,1790,388,43673⟩,63847970897920,282850970408⟩,5,by decide,by decide,by decide⟩
private def s74 : Step := ⟨⟨⟨1486,2073,450,48266⟩,99081982050304,509047443130⟩,7,by decide,by decide,by decide⟩
private def s75 : Step := ⟨⟨⟨1753,2445,531,56148⟩,162615950049280,984841184209⟩,10,by decide,by decide,by decide⟩
private def s76 : Step := ⟨⟨⟨2141,2987,646,77203⟩,295231974801408,2185262053254⟩,16,by decide,by decide,by decide⟩
private def s77 : Step := ⟨⟨⟨2502,3490,757,87096⟩,472001932951552,4080189315429⟩,20,by decide,by decide,by decide⟩
private def s78 : Step := ⟨⟨⟨3501,4884,1059,120899⟩,1292239765504000,15633823672100⟩,32,by decide,by decide,by decide⟩
private def s79 : Step := ⟨⟨⟨3211,4480,969,128562⟩,995323137228800,11048521718737⟩,31,by decide,by decide,by decide⟩
private def s80 : Step := ⟨⟨⟨4562,6365,1386,152858⟩,2867772810854400,45229349013351⟩,44,by decide,by decide,by decide⟩
private def s81 : Step := ⟨⟨⟨7056,9847,2145,232545⟩,10611908411654144,259037889725205⟩,73,by decide,by decide,by decide⟩
private def s82 : Step := ⟨⟨⟨7057,9848,2145,243853⟩,10615275058102272,259122589187366⟩,75,by decide,by decide,by decide⟩
private def s83 : Step := ⟨⟨⟨9664,13486,2939,313868⟩,27267301577850880,911445503719857⟩,103,by decide,by decide,by decide⟩
private def s84 : Step := ⟨⟨⟨675,941,205,8990⟩,9342557880320,21779095054⟩,0,by decide,by decide,by decide⟩
private def s85 : Step := ⟨⟨⟨676,941,207,11464⟩,9442668052480,21943713466⟩,1,by decide,by decide,by decide⟩
private def s86 : Step := ⟨⟨⟨804,1120,244,10682⟩,15761397514240,43645689751⟩,2,by decide,by decide,by decide⟩
private def s87 : Step := ⟨⟨⟨804,1120,246,12942⟩,15859176439808,43923164154⟩,3,by decide,by decide,by decide⟩
private def s88 : Step := ⟨⟨⟨900,1254,274,12880⟩,22147439001600,68692217088⟩,4,by decide,by decide,by decide⟩
private def s89 : Step := ⟨⟨⟨964,1344,297,13438⟩,27453212065792,91396221297⟩,5,by decide,by decide,by decide⟩
private def s90 : Step := ⟨⟨⟨1100,1533,339,14841⟩,40773245992960,154668202561⟩,7,by decide,by decide,by decide⟩
private def s91 : Step := ⟨⟨⟨1178,1642,363,17981⟩,50058265886720,203456716276⟩,9,by decide,by decide,by decide⟩
private def s92 : Step := ⟨⟨⟨1446,2016,445,24680⟩,92425607184384,461335336752⟩,14,by decide,by decide,by decide⟩
private def s93 : Step := ⟨⟨⟨1901,2651,587,26483⟩,210380694487040,1381399446512⟩,20,by decide,by decide,by decide⟩
private def s94 : Step := ⟨⟨⟨2676,3733,827,36515⟩,586790189137920,5428588938227⟩,32,by decide,by decide,by decide⟩
private def s95 : Step := ⟨⟨⟨2676,3733,810,36987⟩,577605596872704,5341514957697⟩,31,by decide,by decide,by decide⟩
private def s96 : Step := ⟨⟨⟨3211,4480,993,47919⟩,1014000328900608,11261061813694⟩,42,by decide,by decide,by decide⟩
private def s97 : Step := ⟨⟨⟨316,439,97,3526⟩,973976371200,1053621943⟩,0,by decide,by decide,by decide⟩
private def s98 : Step := ⟨⟨⟨350,486,108,3675⟩,1326705278976,1586684409⟩,1,by decide,by decide,by decide⟩
private def s99 : Step := ⟨⟨⟨375,522,116,4260⟩,1633365786624,2109199468⟩,2,by decide,by decide,by decide⟩
private def s100 : Step := ⟨⟨⟨420,584,129,4227⟩,2279474462720,3283524462⟩,3,by decide,by decide,by decide⟩
private def s101 : Step := ⟨⟨⟨451,627,138,4608⟩,2812213198848,4346358834⟩,4,by decide,by decide,by decide⟩
private def s102 : Step := ⟨⟨⟨495,689,151,4844⟩,3706185580544,6309269027⟩,5,by decide,by decide,by decide⟩
private def s103 : Step := ⟨⟨⟨557,776,172,5362⟩,5323788910592,10227269032⟩,7,by decide,by decide,by decide⟩
private def s104 : Step := ⟨⟨⟨631,878,195,6528⟩,7736885510144,16765904450⟩,10,by decide,by decide,by decide⟩
private def s105 : Step := ⟨⟨⟨803,1119,250,8882⟩,16009083224064,44348152608⟩,16,by decide,by decide,by decide⟩
private def s106 : Step := ⟨⟨⟨965,1344,299,9371⟩,27657057075200,91873250596⟩,20,by decide,by decide,by decide⟩
private def s107 : Step := ⟨⟨⟨1350,1881,410,14048⟩,74478966538240,346324061737⟩,32,by decide,by decide,by decide⟩
private def s108 : Step := ⟨⟨⟨1284,1789,399,13195⟩,65215712460800,288543907994⟩,31,by decide,by decide,by decide⟩
private def s109 : Step := ⟨⟨⟨1651,2301,514,17131⟩,138726224691200,789804210292⟩,43,by decide,by decide,by decide⟩
private def s110 : Step := ⟨⟨⟨2676,3732,810,28255⟩,577605596872704,5336911331606⟩,73,by decide,by decide,by decide⟩
private def s111 : Step := ⟨⟨⟨2677,3732,831,27821⟩,589433174753280,5444287982368⟩,76,by decide,by decide,by decide⟩
private def s112 : Step := ⟨⟨⟨3502,4883,1087,36879⟩,1318952739274752,15944199479922⟩,103,by decide,by decide,by decide⟩
private def s113 : Step := ⟨⟨⟨251,348,78,2578⟩,494498480128,422716393⟩,0,by decide,by decide,by decide⟩
private def s114 : Step := ⟨⟨⟨269,373,83,3119⟩,604708536320,553942033⟩,1,by decide,by decide,by decide⟩
private def s115 : Step := ⟨⟨⟨295,409,91,3258⟩,796182708224,799166465⟩,2,by decide,by decide,by decide⟩
private def s116 : Step := ⟨⟨⟨316,439,99,3670⟩,989003776000,1070296326⟩,3,by decide,by decide,by decide⟩
private def s117 : Step := ⟨⟨⟨350,486,108,3574⟩,1326705278976,1586684409⟩,4,by decide,by decide,by decide⟩
private def s118 : Step := ⟨⟨⟨376,522,115,3885⟩,1632445661184,2095158739⟩,5,by decide,by decide,by decide⟩
private def s119 : Step := ⟨⟨⟨421,585,130,4381⟩,2304993132544,3321371304⟩,7,by decide,by decide,by decide⟩
private def s120 : Step := ⟨⟨⟨495,689,153,5178⟩,3743163088896,6373806108⟩,10,by decide,by decide,by decide⟩
private def s121 : Step := ⟨⟨⟨632,879,197,6796⟩,7824354312192,16960777224⟩,16,by decide,by decide,by decide⟩
private def s122 : Step := ⟨⟨⟨750,1044,228,7945⟩,12816073097216,33031832783⟩,20,by decide,by decide,by decide⟩
private def s123 : Step := ⟨⟨⟨1046,1457,317,11461⟩,34623417221120,124655308417⟩,32,by decide,by decide,by decide⟩
private def s124 : Step := ⟨⟨⟨991,1381,309,10969⟩,30092702515200,102855435469⟩,31,by decide,by decide,by decide⟩
private def s125 : Step := ⟨⟨⟨1350,1881,410,14340⟩,74478966538240,346324061737⟩,44,by decide,by decide,by decide⟩
private def s126 : Step := ⟨⟨⟨2141,2985,648,21237⟩,295927164960768,2185816928972⟩,73,by decide,by decide,by decide⟩
private def s127 : Step := ⟨⟨⟨2141,2984,663,21306⟩,301113171509248,2222687573359⟩,76,by decide,by decide,by decide⟩
private def s128 : Step := ⟨⟨⟨2676,3731,831,29591⟩,588939932991488,5439590961728⟩,101,by decide,by decide,by decide⟩
private def s129 : Step := ⟨⟨⟨190,264,58,2115⟩,212911783936,138919245⟩,0,by decide,by decide,by decide⟩
private def s130 : Step := ⟨⟨⟨210,291,65,2213⟩,289785774080,207093695⟩,1,by decide,by decide,by decide⟩
private def s131 : Step := ⟨⟨⟨226,314,70,2482⟩,360816574464,279745237⟩,2,by decide,by decide,by decide⟩
private def s132 : Step := ⟨⟨⟨249,346,76,2646⟩,476388261888,406778496⟩,3,by decide,by decide,by decide⟩
private def s133 : Step := ⟨⟨⟨268,372,81,2935⟩,588823920640,538985674⟩,4,by decide,by decide,by decide⟩
private def s134 : Step := ⟨⟨⟨281,390,87,3076⟩,690560696320,662678389⟩,5,by decide,by decide,by decide⟩
private def s135 : Step := ⟨⟨⟨316,439,97,3618⟩,973976371200,1053621943⟩,7,by decide,by decide,by decide⟩
private def s136 : Step := ⟨⟨⟨376,522,116,4017⟩,1643119116288,2109199468⟩,10,by decide,by decide,by decide⟩
private def s137 : Step := ⟨⟨⟨495,689,148,5919⟩,3650340519936,6211915218⟩,16,by decide,by decide,by decide⟩
private def s138 : Step := ⟨⟨⟨558,776,172,6133⟩,5345194541056,10227269032⟩,20,by decide,by decide,by decide⟩
private def s139 : Step := ⟨⟨⟨752,1046,232,8644⟩,13063450263552,33687112323⟩,31,by decide,by decide,by decide⟩
private def s140 : Step := ⟨⟨⟨992,1381,301,11260⟩,29567671336960,100782684488⟩,43,by decide,by decide,by decide⟩
private def s141 : Step := ⟨⟨⟨1487,2071,461,16691⟩,101065726361600,517086467983⟩,71,by decide,by decide,by decide⟩
private def s142 : Step := ⟨⟨⟨1569,2186,475,18256⟩,116584333967360,629804346601⟩,74,by decide,by decide,by decide⟩
private def s143 : Step := ⟨⟨⟨2000,2786,622,24513⟩,246290709217280,1695588737377⟩,101,by decide,by decide,by decide⟩
private def s144 : Step := ⟨⟨⟨675,941,201,35929⟩,9203935084544,21448202127⟩,0,by decide,by decide,by decide⟩
private def s145 : Step := ⟨⟨⟨676,941,205,41117⟩,9373527834624,21779095054⟩,1,by decide,by decide,by decide⟩
private def s146 : Step := ⟨⟨⟨900,1254,272,40402⟩,22024701870080,68302247306⟩,2,by decide,by decide,by decide⟩
private def s147 : Step := ⟨⟨⟨804,1120,242,47793⟩,15663288287232,43367437240⟩,3,by decide,by decide,by decide⟩
private def s148 : Step := ⟨⟨⟨964,1344,287,49048⟩,26748766912512,88994405278⟩,4,by decide,by decide,by decide⟩
private def s149 : Step := ⟨⟨⟨964,1344,291,53212⟩,27031739301888,89958515582⟩,5,by decide,by decide,by decide⟩
private def s150 : Step := ⟨⟨⟨1178,1642,357,57717⟩,49429552562176,200838207675⟩,7,by decide,by decide,by decide⟩
private def s151 : Step := ⟨⟨⟨1178,1642,357,75382⟩,49429552562176,200838207675⟩,10,by decide,by decide,by decide⟩
private def s152 : Step := ⟨⟨⟨1767,2464,524,91130⟩,163868966912000,999276440686⟩,16,by decide,by decide,by decide⟩
private def s153 : Step := ⟨⟨⟨2141,2986,635,103054⟩,291392422150144,2153848876645⟩,20,by decide,by decide,by decide⟩
private def s154 : Step := ⟨⟨⟨2676,3733,794,145339⟩,568888308531200,5258988361047⟩,31,by decide,by decide,by decide⟩
private def s155 : Step := ⟨⟨⟨3211,4480,971,183061⟩,996886805741568,11066301769580⟩,42,by decide,by decide,by decide⟩
private def s156 : Step := ⟨⟨⟨675,941,201,34531⟩,9203935084544,21448202127⟩,0,by decide,by decide,by decide⟩
private def s157 : Step := ⟨⟨⟨804,1120,242,35921⟩,15663288287232,43367437240⟩,1,by decide,by decide,by decide⟩
private def s158 : Step := ⟨⟨⟨804,1120,239,41292⟩,15515495956480,42948576600⟩,2,by decide,by decide,by decide⟩
private def s159 : Step := ⟨⟨⟨804,1120,239,47169⟩,15515495956480,42948576600⟩,3,by decide,by decide,by decide⟩
private def s160 : Step := ⟨⟨⟨964,1344,291,46146⟩,27031739301888,89958515582⟩,4,by decide,by decide,by decide⟩
private def s161 : Step := ⟨⟨⟨964,1344,287,52310⟩,26748766912512,88994405278⟩,5,by decide,by decide,by decide⟩
private def s162 : Step := ⟨⟨⟨1178,1642,351,56525⟩,48796469821440,198204588222⟩,7,by decide,by decide,by decide⟩
private def s163 : Step := ⟨⟨⟨1446,2016,437,64070⟩,91161654722560,454871172326⟩,10,by decide,by decide,by decide⟩
private def s164 : Step := ⟨⟨⟨1926,2677,582,81718⟩,215221251604480,1416029540274⟩,16,by decide,by decide,by decide⟩
private def s165 : Step := ⟨⟨⟨1767,2464,535,100205⟩,166482728189952,1015598734021⟩,19,by decide,by decide,by decide⟩
private def s166 : Step := ⟨⟨⟨3001,4186,908,133054⟩,814237843980288,8441390295919⟩,32,by decide,by decide,by decide⟩
private def s167 : Step := ⟨⟨⟨2676,3733,810,134330⟩,577605596872704,5341514957697⟩,31,by decide,by decide,by decide⟩
private def s168 : Step := ⟨⟨⟨3210,4480,952,184212⟩,981294413250560,10896877796527⟩,42,by decide,by decide,by decide⟩
private def s169 : Step := ⟨⟨⟨675,941,201,31751⟩,9203935084544,21448202127⟩,0,by decide,by decide,by decide⟩
private def s170 : Step := ⟨⟨⟨676,941,201,37168⟩,9234409586688,21448202127⟩,1,by decide,by decide,by decide⟩
private def s171 : Step := ⟨⟨⟨804,1120,242,36990⟩,15663288287232,43367437240⟩,2,by decide,by decide,by decide⟩
private def s172 : Step := ⟨⟨⟨804,1120,242,42123⟩,15663288287232,43367437240⟩,3,by decide,by decide,by decide⟩
private def s173 : Step := ⟨⟨⟨998,1387,302,41452⟩,30044628975616,102461756220⟩,4,by decide,by decide,by decide⟩
private def s174 : Step := ⟨⟨⟨964,1344,291,46894⟩,27031739301888,89958515582⟩,5,by decide,by decide,by decide⟩
private def s175 : Step := ⟨⟨⟨1178,1642,357,50825⟩,49429552562176,200838207675⟩,7,by decide,by decide,by decide⟩
private def s176 : Step := ⟨⟨⟨1178,1642,351,68212⟩,48796469821440,198204588222⟩,10,by decide,by decide,by decide⟩
private def s177 : Step := ⟨⟨⟨1767,2464,524,80653⟩,163868966912000,999276440686⟩,16,by decide,by decide,by decide⟩
private def s178 : Step := ⟨⟨⟨2141,2986,635,91219⟩,291392422150144,2153848876645⟩,20,by decide,by decide,by decide⟩
private def s179 : Step := ⟨⟨⟨2676,3733,794,128641⟩,568888308531200,5258988361047⟩,31,by decide,by decide,by decide⟩
private def s180 : Step := ⟨⟨⟨2895,4023,876,118319⟩,731057167007744,7223575584596⟩,31,by decide,by decide,by decide⟩
private def s181 : Step := ⟨⟨⟨3211,4480,971,161364⟩,996886805741568,11066301769580⟩,42,by decide,by decide,by decide⟩
private def s182 : Step := ⟨⟨⟨675,941,201,24914⟩,9203935084544,21448202127⟩,0,by decide,by decide,by decide⟩
private def s183 : Step := ⟨⟨⟨676,941,201,29115⟩,9234409586688,21448202127⟩,1,by decide,by decide,by decide⟩
private def s184 : Step := ⟨⟨⟨804,1120,244,28711⟩,15761397514240,43645689751⟩,2,by decide,by decide,by decide⟩
private def s185 : Step := ⟨⟨⟨804,1120,244,32674⟩,15761397514240,43645689751⟩,3,by decide,by decide,by decide⟩
private def s186 : Step := ⟨⟨⟨804,1120,244,37918⟩,15761397514240,43645689751⟩,4,by decide,by decide,by decide⟩
private def s187 : Step := ⟨⟨⟨964,1344,293,36491⟩,27172624138240,90438866290⟩,5,by decide,by decide,by decide⟩
private def s188 : Step := ⟨⟨⟨964,1344,291,46464⟩,27031739301888,89958515582⟩,7,by decide,by decide,by decide⟩
private def s189 : Step := ⟨⟨⟨1178,1642,351,53465⟩,48796469821440,198204588222⟩,10,by decide,by decide,by decide⟩
private def s190 : Step := ⟨⟨⟨1446,2016,430,62865⟩,90047847071744,449181681065⟩,14,by decide,by decide,by decide⟩
private def s191 : Step := ⟨⟨⟨1767,2464,535,71561⟩,166482728189952,1015598734021⟩,19,by decide,by decide,by decide⟩
private def s192 : Step := ⟨⟨⟨2676,3733,794,105262⟩,568888308531200,5258988361047⟩,32,by decide,by decide,by decide⟩
private def s193 : Step := ⟨⟨⟨2141,2986,648,107614⟩,295927164960768,2188174228719⟩,29,by decide,by decide,by decide⟩
private def s194 : Step := ⟨⟨⟨3211,4480,971,125830⟩,996886805741568,11066301769580⟩,42,by decide,by decide,by decide⟩
private def s195 : Step := ⟨⟨⟨600,835,182,16190⟩,6561258536960,13523494720⟩,0,by decide,by decide,by decide⟩
private def s196 : Step := ⟨⟨⟨630,877,192,18636⟩,7619678044160,16505144473⟩,1,by decide,by decide,by decide⟩
private def s197 : Step := ⟨⟨⟨676,941,205,20650⟩,9373527834624,21779095054⟩,2,by decide,by decide,by decide⟩
private def s198 : Step := ⟨⟨⟨752,1047,228,21519⟩,12892612591616,33338030973⟩,3,by decide,by decide,by decide⟩
private def s199 : Step := ⟨⟨⟨804,1120,244,23318⟩,15761397514240,43645689751⟩,4,by decide,by decide,by decide⟩
private def s200 : Step := ⟨⟨⟨901,1255,274,23680⟩,22202515456000,68868567988⟩,5,by decide,by decide,by decide⟩
private def s201 : Step := ⟨⟨⟨964,1344,293,28553⟩,27172624138240,90438866290⟩,7,by decide,by decide,by decide⟩
private def s202 : Step := ⟨⟨⟨1178,1642,357,31981⟩,49429552562176,200838207675⟩,10,by decide,by decide,by decide⟩
private def s203 : Step := ⟨⟨⟨1446,2016,430,47356⟩,90047847071744,449181681065⟩,16,by decide,by decide,by decide⟩
private def s204 : Step := ⟨⟨⟨1801,2512,546,46714⟩,176443510489088,1097912637494⟩,20,by decide,by decide,by decide⟩
private def s205 : Step := ⟨⟨⟨2377,3315,719,68915⟩,404696963481600,3321608618830⟩,32,by decide,by decide,by decide⟩
private def s206 : Step := ⟨⟨⟨2141,2986,648,70942⟩,295927164960768,2188174228719⟩,30,by decide,by decide,by decide⟩
private def s207 : Step := ⟨⟨⟨3002,4187,908,90149⟩,814845004087296,8447882058193⟩,44,by decide,by decide,by decide⟩
private def s208 : Step := ⟨⟨⟨451,627,139,8081⟩,2827563827200,4370677984⟩,0,by decide,by decide,by decide⟩
private def s209 : Step := ⟨⟨⟨522,726,161,7770⟩,4380469493760,7844248211⟩,1,by decide,by decide,by decide⟩
private def s210 : Step := ⟨⟨⟨558,777,172,8868⟩,5345194541056,10269709565⟩,2,by decide,by decide,by decide⟩
private def s211 : Step := ⟨⟨⟨630,877,193,8923⟩,7649673609216,16571733118⟩,3,by decide,by decide,by decide⟩
private def s212 : Step := ⟨⟨⟨676,941,209,9507⟩,9511534592000,22107791483⟩,4,by decide,by decide,by decide⟩
private def s213 : Step := ⟨⟨⟨676,941,205,12137⟩,9373527834624,21779095054⟩,5,by decide,by decide,by decide⟩
private def s214 : Step := ⟨⟨⟨804,1120,248,11861⟩,15956629258240,44199870802⟩,7,by decide,by decide,by decide⟩
private def s215 : Step := ⟨⟨⟨964,1344,297,13614⟩,27453212065792,91396221297⟩,10,by decide,by decide,by decide⟩
private def s216 : Step := ⟨⟨⟨1178,1642,357,20437⟩,49429552562176,200838207675⟩,16,by decide,by decide,by decide⟩
private def s217 : Step := ⟨⟨⟨1446,2016,439,20921⟩,91478530457600,456490982233⟩,20,by decide,by decide,by decide⟩
private def s218 : Step := ⟨⟨⟨2001,2790,618,28207⟩,245364623147008,1694924397901⟩,32,by decide,by decide,by decide⟩
private def s219 : Step := ⟨⟨⟨1766,2463,546,28795⟩,168860183953408,1030458733529⟩,29,by decide,by decide,by decide⟩
private def s220 : Step := ⟨⟨⟨2502,3489,773,37631⟩,479559999553536,4143342061277⟩,44,by decide,by decide,by decide⟩
private def s221 : Step := ⟨⟨⟨3746,5226,1133,60579⟩,1582704237477888,20490123698665⟩,71,by decide,by decide,by decide⟩
private def s222 : Step := ⟨⟨⟨3747,5226,1159,62907⟩,1611188456652800,20855394628791⟩,74,by decide,by decide,by decide⟩
private def s223 : Step := ⟨⟨⟨4817,6719,1491,90072⟩,3423993242583040,56991083890579⟩,101,by decide,by decide,by decide⟩
private def s224 : Step := ⟨⟨⟨294,408,91,3098⟩,790165454848,792909453⟩,0,by decide,by decide,by decide⟩
private def s225 : Step := ⟨⟨⟨316,439,97,3644⟩,973976371200,1053621943⟩,1,by decide,by decide,by decide⟩
private def s226 : Step := ⟨⟨⟨350,486,108,3736⟩,1326705278976,1586684409⟩,2,by decide,by decide,by decide⟩
private def s227 : Step := ⟨⟨⟨375,522,116,4189⟩,1633365786624,2109199468⟩,3,by decide,by decide,by decide⟩
private def s228 : Step := ⟨⟨⟨401,557,123,4570⟩,1982954733568,2718384649⟩,4,by decide,by decide,by decide⟩
private def s229 : Step := ⟨⟨⟨451,627,138,4532⟩,2812213198848,4346358834⟩,5,by decide,by decide,by decide⟩
private def s230 : Step := ⟨⟨⟨495,689,151,5487⟩,3706185580544,6309269027⟩,7,by decide,by decide,by decide⟩
private def s231 : Step := ⟨⟨⟨558,776,174,6736⟩,5391987507200,10319091253⟩,10,by decide,by decide,by decide⟩
private def s232 : Step := ⟨⟨⟨750,1044,232,8001⟩,12985818152960,33480320163⟩,16,by decide,by decide,by decide⟩
private def s233 : Step := ⟨⟨⟨857,1193,267,9254⟩,19464104968192,57346492132⟩,20,by decide,by decide,by decide⟩
private def s234 : Step := ⟨⟨⟨1178,1641,367,13506⟩,50475036573696,204792136984⟩,32,by decide,by decide,by decide⟩
private def s235 : Step := ⟨⟨⟨1178,1641,357,13887⟩,49429552562176,200444998912⟩,31,by decide,by decide,by decide⟩
private def s236 : Step := ⟨⟨⟨1569,2187,486,16296⟩,118626912043008,642060661475⟩,44,by decide,by decide,by decide⟩
private def s237 : Step := ⟨⟨⟨2500,3486,757,25829⟩,471158230876160,4065158762879⟩,73,by decide,by decide,by decide⟩
private def s238 : Step := ⟨⟨⟨2502,3488,777,25657⟩,481439418417152,4156157567519⟩,76,by decide,by decide,by decide⟩
private def s239 : Step := ⟨⟨⟨3212,4478,997,34970⟩,1017804935135232,11280078823729⟩,103,by decide,by decide,by decide⟩
private def s240 : Step := ⟨⟨⟨239,332,74,2477⟩,426141286400,349077659⟩,0,by decide,by decide,by decide⟩
private def s241 : Step := ⟨⟨⟨269,373,83,2619⟩,604708536320,553942033⟩,1,by decide,by decide,by decide⟩
private def s242 : Step := ⟨⟨⟨281,390,87,3036⟩,690560696320,662678389⟩,2,by decide,by decide,by decide⟩
private def s243 : Step := ⟨⟨⟨316,439,97,3128⟩,973976371200,1053621943⟩,3,by decide,by decide,by decide⟩
private def s244 : Step := ⟨⟨⟨334,464,103,3412⟩,1153155727360,1318278333⟩,4,by decide,by decide,by decide⟩
private def s245 : Step := ⟨⟨⟨350,486,108,3785⟩,1326705278976,1586684409⟩,5,by decide,by decide,by decide⟩
private def s246 : Step := ⟨⟨⟨401,557,123,4227⟩,1982954733568,2718384649⟩,7,by decide,by decide,by decide⟩
private def s247 : Step := ⟨⟨⟨469,652,143,5128⟩,3152837345280,5065784484⟩,10,by decide,by decide,by decide⟩
private def s248 : Step := ⟨⟨⟨600,835,185,6642⟩,6642856099840,13695877387⟩,16,by decide,by decide,by decide⟩
private def s249 : Step := ⟨⟨⟨675,939,211,8066⟩,9548426379264,22119378957⟩,20,by decide,by decide,by decide⟩
private def s250 : Step := ⟨⟨⟨964,1343,299,10649⟩,27592923545600,91653421946⟩,32,by decide,by decide,by decide⟩
private def s251 : Step := ⟨⟨⟨964,1343,297,10040⟩,27453212065792,91177576164⟩,31,by decide,by decide,by decide⟩
private def s252 : Step := ⟨⟨⟨1217,1695,378,13247⟩,55521299398656,232557160904⟩,43,by decide,by decide,by decide⟩
private def s253 : Step := ⟨⟨⟨1901,2650,589,21021⟩,210923565875200,1383373535668⟩,73,by decide,by decide,by decide⟩
private def s254 : Step := ⟨⟨⟨2000,2787,606,23022⟩,241468805218304,1663490943357⟩,76,by decide,by decide,by decide⟩
private def s255 : Step := ⟨⟨⟨2502,3487,777,29171⟩,481439418417152,4152321171330⟩,101,by decide,by decide,by decide⟩
private def s256 : Step := ⟨⟨⟨183,254,57,2073⟩,193292926976,121131076⟩,0,by decide,by decide,by decide⟩
private def s257 : Step := ⟨⟨⟨200,278,61,2403⟩,247865278464,170383811⟩,1,by decide,by decide,by decide⟩
private def s258 : Step := ⟨⟨⟨226,314,68,2489⟩,353070481408,273591980⟩,2,by decide,by decide,by decide⟩
private def s259 : Step := ⟨⟨⟨239,331,74,2610⟩,426141286400,345715284⟩,3,by decide,by decide,by decide⟩
private def s260 : Step := ⟨⟨⟨251,348,78,2987⟩,494498480128,422716393⟩,4,by decide,by decide,by decide⟩
private def s261 : Step := ⟨⟨⟨268,372,83,3236⟩,599698964480,549189173⟩,5,by decide,by decide,by decide⟩
private def s262 : Step := ⟨⟨⟨316,439,97,3334⟩,973976371200,1053621943⟩,7,by decide,by decide,by decide⟩
private def s263 : Step := ⟨⟨⟨376,522,114,3949⟩,1621734195200,2081076603⟩,10,by decide,by decide,by decide⟩
private def s264 : Step := ⟨⟨⟨469,652,145,5271⟩,3186037882880,5120467320⟩,16,by decide,by decide,by decide⟩
private def s265 : Step := ⟨⟨⟨558,776,170,5906⟩,5298178228224,10135084168⟩,20,by decide,by decide,by decide⟩
private def s266 : Step := ⟨⟨⟨752,1046,232,8604⟩,13063450263552,33687112323⟩,32,by decide,by decide,by decide⟩
private def s267 : Step := ⟨⟨⟨750,1044,228,8418⟩,12816073097216,33031832783⟩,31,by decide,by decide,by decide⟩
private def s268 : Step := ⟨⟨⟨965,1343,299,10977⟩,27657057075200,91653421946⟩,44,by decide,by decide,by decide⟩
private def s269 : Step := ⟨⟨⟨1487,2071,459,16872⟩,100733524377600,515343711922⟩,73,by decide,by decide,by decide⟩
private def s270 : Step := ⟨⟨⟨1569,2186,475,18079⟩,116584333967360,629804346601⟩,76,by decide,by decide,by decide⟩
private def s271 : Step := ⟨⟨⟨2000,2786,620,23515⟩,245690786119680,1691352972155⟩,103,by decide,by decide,by decide⟩
private def s272 : Step := ⟨⟨⟨451,627,138,15973⟩,2812213198848,4346358834⟩,0,by decide,by decide,by decide⟩
private def s273 : Step := ⟨⟨⟨451,627,138,18735⟩,2812213198848,4346358834⟩,1,by decide,by decide,by decide⟩
private def s274 : Step := ⟨⟨⟨600,835,182,18424⟩,6561258536960,13523494720⟩,2,by decide,by decide,by decide⟩
private def s275 : Step := ⟨⟨⟨630,877,192,19988⟩,7619678044160,16505144473⟩,3,by decide,by decide,by decide⟩
private def s276 : Step := ⟨⟨⟨675,941,201,22552⟩,9203935084544,21448202127⟩,4,by decide,by decide,by decide⟩
private def s277 : Step := ⟨⟨⟨751,1046,228,22881⟩,12854312828928,33235751329⟩,5,by decide,by decide,by decide⟩
private def s278 : Step := ⟨⟨⟨804,1120,244,26210⟩,15761397514240,43645689751⟩,7,by decide,by decide,by decide⟩
private def s279 : Step := ⟨⟨⟨803,1119,246,33811⟩,15815081984000,43797141543⟩,10,by decide,by decide,by decide⟩
private def s280 : Step := ⟨⟨⟨1178,1642,351,42158⟩,48796469821440,198204588222⟩,16,by decide,by decide,by decide⟩
private def s281 : Step := ⟨⟨⟨1446,2016,439,45489⟩,91478530457600,456490982233⟩,20,by decide,by decide,by decide⟩
private def s282 : Step := ⟨⟨⟨1766,2463,535,62578⟩,166272034668544,1014273068001⟩,30,by decide,by decide,by decide⟩
private def s283 : Step := ⟨⟨⟨2675,3733,794,85703⟩,568413354721280,5258988361047⟩,44,by decide,by decide,by decide⟩
private def s284 : Step := ⟨⟨⟨3745,5226,1111,131188⟩,1558282831396864,20178795342277⟩,71,by decide,by decide,by decide⟩
private def s285 : Step := ⟨⟨⟨3747,5226,1133,130110⟩,1583649708834816,20490123698665⟩,74,by decide,by decide,by decide⟩
private def s286 : Step := ⟨⟨⟨4816,6719,1427,186489⟩,3309978934312960,55074003757013⟩,101,by decide,by decide,by decide⟩
private def s287 : Step := ⟨⟨⟨451,627,135,15875⟩,2765885538304,4273039343⟩,0,by decide,by decide,by decide⟩
private def s288 : Step := ⟨⟨⟨522,726,159,16545⟩,4339322060800,7768738896⟩,1,by decide,by decide,by decide⟩
private def s289 : Step := ⟨⟨⟨558,777,170,18176⟩,5298178228224,10177127881⟩,2,by decide,by decide,by decide⟩
private def s290 : Step := ⟨⟨⟨557,776,170,20538⟩,5276975235072,10135084168⟩,3,by decide,by decide,by decide⟩
private def s291 : Step := ⟨⟨⟨676,941,207,20746⟩,9442668052480,21943713466⟩,4,by decide,by decide,by decide⟩
private def s292 : Step := ⟨⟨⟨676,941,205,22872⟩,9373527834624,21779095054⟩,5,by decide,by decide,by decide⟩
private def s293 : Step := ⟨⟨⟨804,1120,244,25351⟩,15761397514240,43645689751⟩,7,by decide,by decide,by decide⟩
private def s294 : Step := ⟨⟨⟨964,1344,293,29566⟩,27172624138240,90438866290⟩,10,by decide,by decide,by decide⟩
private def s295 : Step := ⟨⟨⟨1178,1642,351,40812⟩,48796469821440,198204588222⟩,16,by decide,by decide,by decide⟩
private def s296 : Step := ⟨⟨⟨1446,2016,430,46240⟩,90047847071744,449181681065⟩,20,by decide,by decide,by decide⟩
private def s297 : Step := ⟨⟨⟨1766,2463,535,62892⟩,166272034668544,1014273068001⟩,31,by decide,by decide,by decide⟩
private def s298 : Step := ⟨⟨⟨2000,2789,606,59904⟩,241468805218304,1667335508969⟩,31,by decide,by decide,by decide⟩
private def s299 : Step := ⟨⟨⟨2675,3733,794,82998⟩,568413354721280,5258988361047⟩,44,by decide,by decide,by decide⟩
private def s300 : Step := ⟨⟨⟨3747,5226,1159,120492⟩,1611188456652800,20855394628791⟩,72,by decide,by decide,by decide⟩
private def s301 : Step := ⟨⟨⟨3746,5226,1111,134038⟩,1559212875317248,20178795342277⟩,74,by decide,by decide,by decide⟩
private def s302 : Step := ⟨⟨⟨4817,6719,1456,168563⟩,3362734500741120,55946262102391⟩,101,by decide,by decide,by decide⟩
private def s303 : Step := ⟨⟨⟨451,627,138,14381⟩,2812213198848,4346358834⟩,0,by decide,by decide,by decide⟩
private def s304 : Step := ⟨⟨⟨520,724,156,15856⟩,4240694575104,7587328278⟩,1,by decide,by decide,by decide⟩
private def s305 : Step := ⟨⟨⟨558,777,167,17465⟩,5227225808896,10037556307⟩,2,by decide,by decide,by decide⟩
private def s306 : Step := ⟨⟨⟨630,877,192,18017⟩,7619678044160,16505144473⟩,3,by decide,by decide,by decide⟩
private def s307 : Step := ⟨⟨⟨630,877,188,20744⟩,7499048288256,16237597096⟩,4,by decide,by decide,by decide⟩
private def s308 : Step := ⟨⟨⟨714,995,217,20911⟩,11059077578752,27235199262⟩,5,by decide,by decide,by decide⟩
private def s309 : Step := ⟨⟨⟨811,1130,247,23523⟩,16219446968320,45339607027⟩,7,by decide,by decide,by decide⟩
private def s310 : Step := ⟨⟨⟨964,1344,287,28907⟩,26748766912512,88994405278⟩,10,by decide,by decide,by decide⟩
private def s311 : Step := ⟨⟨⟨1178,1642,357,36481⟩,49429552562176,200838207675⟩,16,by decide,by decide,by decide⟩
private def s312 : Step := ⟨⟨⟨1446,2016,439,41057⟩,91478530457600,456490982233⟩,20,by decide,by decide,by decide⟩
private def s313 : Step := ⟨⟨⟨1766,2463,546,58254⟩,168860183953408,1030458733529⟩,31,by decide,by decide,by decide⟩
private def s314 : Step := ⟨⟨⟨1766,2463,535,58690⟩,166272034668544,1014273068001⟩,31,by decide,by decide,by decide⟩
private def s315 : Step := ⟨⟨⟨2500,3487,757,74562⟩,471158230876160,4068912864757⟩,44,by decide,by decide,by decide⟩
private def s316 : Step := ⟨⟨⟨3745,5226,1111,118823⟩,1558282831396864,20178795342277⟩,71,by decide,by decide,by decide⟩
private def s317 : Step := ⟨⟨⟨3747,5226,1133,117518⟩,1583649708834816,20490123698665⟩,74,by decide,by decide,by decide⟩
private def s318 : Step := ⟨⟨⟨4816,6719,1427,168914⟩,3309978934312960,55074003757013⟩,101,by decide,by decide,by decide⟩
private def s319 : Step := ⟨⟨⟨469,653,143,11669⟩,3152837345280,5090794644⟩,0,by decide,by decide,by decide⟩
private def s320 : Step := ⟨⟨⟨469,653,143,13455⟩,3152837345280,5090794644⟩,1,by decide,by decide,by decide⟩
private def s321 : Step := ⟨⟨⟨496,690,151,14939⟩,3722940776448,6338745703⟩,2,by decide,by decide,by decide⟩
private def s322 : Step := ⟨⟨⟨521,725,159,16581⟩,4320762265600,7734396896⟩,3,by decide,by decide,by decide⟩
private def s323 : Step := ⟨⟨⟨568,791,173,17642⟩,5586192957440,10925512348⟩,4,by decide,by decide,by decide⟩
private def s324 : Step := ⟨⟨⟨631,878,192,18203⟩,7646745722880,16565729682⟩,5,by decide,by decide,by decide⟩
private def s325 : Step := ⟨⟨⟨676,942,202,22839⟩,9269295185920,21604752243⟩,7,by decide,by decide,by decide⟩
private def s326 : Step := ⟨⟨⟨811,1130,247,24843⟩,16219446968320,45339607027⟩,10,by decide,by decide,by decide⟩
private def s327 : Step := ⟨⟨⟨1046,1458,322,32128⟩,35036638740480,126459036040⟩,16,by decide,by decide,by decide⟩
private def s328 : Step := ⟨⟨⟨1178,1642,363,37831⟩,50058265886720,203456716276⟩,20,by decide,by decide,by decide⟩
private def s329 : Step := ⟨⟨⟨1802,2512,546,49548⟩,176662758031360,1097912637494⟩,32,by decide,by decide,by decide⟩
private def s330 : Step := ⟨⟨⟨1650,2300,510,50114⟩,137721075466240,783929501777⟩,31,by decide,by decide,by decide⟩
private def s331 : Step := ⟨⟨⟨2252,3140,695,63777⟩,349474858729472,2716762503457⟩,44,by decide,by decide,by decide⟩
private def s332 : Step := ⟨⟨⟨3327,4640,1006,102945⟩,1108754070241280,12736275646546⟩,73,by decide,by decide,by decide⟩
private def s333 : Step := ⟨⟨⟨4052,5652,1254,95707⟩,2038148503961600,28538967628557⟩,76,by decide,by decide,by decide⟩
private def s334 : Step := ⟨⟨⟨4500,6277,1361,140686⟩,2743020468568064,42637702003194⟩,103,by decide,by decide,by decide⟩
private def s335 : Step := ⟨⟨⟨375,522,115,10034⟩,1622760488960,2095158739⟩,0,by decide,by decide,by decide⟩
private def s336 : Step := ⟨⟨⟨451,627,138,9782⟩,2812213198848,4346358834⟩,1,by decide,by decide,by decide⟩
private def s337 : Step := ⟨⟨⟨522,726,159,10246⟩,4339322060800,7768738896⟩,2,by decide,by decide,by decide⟩
private def s338 : Step := ⟨⟨⟨557,776,170,11230⟩,5276975235072,10135084168⟩,3,by decide,by decide,by decide⟩
private def s339 : Step := ⟨⟨⟨557,776,170,12795⟩,5276975235072,10135084168⟩,4,by decide,by decide,by decide⟩
private def s340 : Step := ⟨⟨⟨557,776,170,14895⟩,5276975235072,10135084168⟩,5,by decide,by decide,by decide⟩
private def s341 : Step := ⟨⟨⟨676,941,205,15498⟩,9373527834624,21779095054⟩,7,by decide,by decide,by decide⟩
private def s342 : Step := ⟨⟨⟨803,1119,244,17981⟩,15717595873280,43520493281⟩,10,by decide,by decide,by decide⟩
private def s343 : Step := ⟨⟨⟨965,1344,293,25327⟩,27235706208256,90438866290⟩,16,by decide,by decide,by decide⟩
private def s344 : Step := ⟨⟨⟨1178,1642,351,29396⟩,48796469821440,198204588222⟩,20,by decide,by decide,by decide⟩
private def s345 : Step := ⟨⟨⟨1766,2463,535,36229⟩,166272034668544,1014273068001⟩,32,by decide,by decide,by decide⟩
private def s346 : Step := ⟨⟨⟨1446,2015,439,37713⟩,91478530457600,455762809733⟩,29,by decide,by decide,by decide⟩
private def s347 : Step := ⟨⟨⟨2141,2986,661,47263⟩,300424516599808,2222264150943⟩,44,by decide,by decide,by decide⟩
private def s348 : Step := ⟨⟨⟨3211,4479,971,72983⟩,996886805741568,11058353878994⟩,71,by decide,by decide,by decide⟩
private def s349 : Step := ⟨⟨⟨3212,4479,971,78467⟩,997581528760320,11058353878994⟩,74,by decide,by decide,by decide⟩
private def s350 : Step := ⟨⟨⟨4817,6719,1456,96462⟩,3362734500741120,55946262102391⟩,103,by decide,by decide,by decide⟩
private def s351 : Step := ⟨⟨⟨350,486,108,5523⟩,1326705278976,1586684409⟩,0,by decide,by decide,by decide⟩
private def s352 : Step := ⟨⟨⟨375,522,116,6404⟩,1633365786624,2109199468⟩,1,by decide,by decide,by decide⟩
private def s353 : Step := ⟨⟨⟨421,585,130,6511⟩,2304993132544,3321371304⟩,2,by decide,by decide,by decide⟩
private def s354 : Step := ⟨⟨⟨469,652,145,6770⟩,3186037882880,5120467320⟩,3,by decide,by decide,by decide⟩
private def s355 : Step := ⟨⟨⟨495,689,153,7509⟩,3743163088896,6373806108⟩,4,by decide,by decide,by decide⟩
private def s356 : Step := ⟨⟨⟨521,725,159,8367⟩,4320762265600,7734396896⟩,5,by decide,by decide,by decide⟩
private def s357 : Step := ⟨⟨⟨557,776,172,10442⟩,5323788910592,10227269032⟩,7,by decide,by decide,by decide⟩
private def s358 : Step := ⟨⟨⟨676,941,209,11259⟩,9511534592000,22107791483⟩,10,by decide,by decide,by decide⟩
private def s359 : Step := ⟨⟨⟨901,1255,274,14462⟩,22202515456000,68868567988⟩,16,by decide,by decide,by decide⟩
private def s360 : Step := ⟨⟨⟨965,1344,299,16556⟩,27657057075200,91873250596⟩,19,by decide,by decide,by decide⟩
private def s361 : Step := ⟨⟨⟨1446,2015,447,22485⟩,92740129914880,462206300528⟩,32,by decide,by decide,by decide⟩
private def s362 : Step := ⟨⟨⟨1446,2015,439,22222⟩,91478530457600,455762809733⟩,31,by decide,by decide,by decide⟩
private def s363 : Step := ⟨⟨⟨1901,2651,587,28153⟩,210380694487040,1381399446512⟩,44,by decide,by decide,by decide⟩
private def s364 : Step := ⟨⟨⟨2852,3977,882,44263⟩,710645955428352,6998094453157⟩,73,by decide,by decide,by decide⟩
private def s365 : Step := ⟨⟨⟨3000,4184,908,47759⟩,813630922162176,8428416950353⟩,76,by decide,by decide,by decide⟩
private def s366 : Step := ⟨⟨⟨3747,5225,1133,64909⟩,1583649708834816,20477507146738⟩,101,by decide,by decide,by decide⟩
private def s367 : Step := ⟨⟨⟨269,373,83,2889⟩,604708536320,553942033⟩,0,by decide,by decide,by decide⟩
private def s368 : Step := ⟨⟨⟨294,408,91,3175⟩,790165454848,792909453⟩,1,by decide,by decide,by decide⟩
private def s369 : Step := ⟨⟨⟨316,439,97,3585⟩,973976371200,1053621943⟩,2,by decide,by decide,by decide⟩
private def s370 : Step := ⟨⟨⟨334,464,103,4019⟩,1153155727360,1318278333⟩,3,by decide,by decide,by decide⟩
private def s371 : Step := ⟨⟨⟨375,522,116,4038⟩,1633365786624,2109199468⟩,4,by decide,by decide,by decide⟩
private def s372 : Step := ⟨⟨⟨401,557,123,4325⟩,1982954733568,2718384649⟩,5,by decide,by decide,by decide⟩
private def s373 : Step := ⟨⟨⟨469,652,143,4805⟩,3152837345280,5065784484⟩,7,by decide,by decide,by decide⟩
private def s374 : Step := ⟨⟨⟨520,723,159,6034⟩,4302244413440,7666023056⟩,10,by decide,by decide,by decide⟩
private def s375 : Step := ⟨⟨⟨676,941,205,8131⟩,9373527834624,21779095054⟩,16,by decide,by decide,by decide⟩
private def s376 : Step := ⟨⟨⟨751,1045,234,9347⟩,13109297152000,33807579841⟩,20,by decide,by decide,by decide⟩
private def s377 : Step := ⟨⟨⟨1100,1532,334,12763⟩,40316563619840,152572307432⟩,32,by decide,by decide,by decide⟩
private def s378 : Step := ⟨⟨⟨1100,1532,334,12014⟩,40316563619840,152572307432⟩,31,by decide,by decide,by decide⟩
private def s379 : Step := ⟨⟨⟨1351,1882,420,15705⟩,75977603416064,353473369789⟩,43,by decide,by decide,by decide⟩
private def s380 : Step := ⟨⟨⟨2252,3139,697,22764⟩,350236896919552,2720046080940⟩,73,by decide,by decide,by decide⟩
private def s381 : Step := ⟨⟨⟨2252,3139,681,26672⟩,344115077447680,2671329548545⟩,76,by decide,by decide,by decide⟩
private def s382 : Step := ⟨⟨⟨2852,3976,886,33160⟩,713087171952640,7017065369167⟩,102,by decide,by decide,by decide⟩
private def s383 : Step := ⟨⟨⟨226,314,70,2398⟩,360816574464,279745237⟩,0,by decide,by decide,by decide⟩
private def s384 : Step := ⟨⟨⟨239,332,74,2848⟩,426141286400,349077659⟩,1,by decide,by decide,by decide⟩
private def s385 : Step := ⟨⟨⟨269,373,83,2874⟩,604708536320,553942033⟩,2,by decide,by decide,by decide⟩
private def s386 : Step := ⟨⟨⟨281,390,87,3345⟩,690560696320,662678389⟩,3,by decide,by decide,by decide⟩
private def s387 : Step := ⟨⟨⟨316,439,97,3330⟩,973976371200,1053621943⟩,4,by decide,by decide,by decide⟩
private def s388 : Step := ⟨⟨⟨334,464,101,3833⟩,1136265003008,1298495912⟩,5,by decide,by decide,by decide⟩
private def s389 : Step := ⟨⟨⟨376,522,115,4174⟩,1632445661184,2095158739⟩,7,by decide,by decide,by decide⟩
private def s390 : Step := ⟨⟨⟨451,627,138,4741⟩,2812213198848,4346358834⟩,10,by decide,by decide,by decide⟩
private def s391 : Step := ⟨⟨⟨568,791,173,6689⟩,5586192957440,10925512348⟩,16,by decide,by decide,by decide⟩
private def s392 : Step := ⟨⟨⟨675,939,207,7029⟩,9411451944960,21794071506⟩,20,by decide,by decide,by decide⟩
private def s393 : Step := ⟨⟨⟨901,1254,274,11255⟩,22202515456000,68692217088⟩,32,by decide,by decide,by decide⟩
private def s394 : Step := ⟨⟨⟨900,1253,277,9880⟩,22330855915520,69097760578⟩,31,by decide,by decide,by decide⟩
private def s395 : Step := ⟨⟨⟨1178,1641,365,12960⟩,50266885586944,203925968773⟩,44,by decide,by decide,by decide⟩
private def s396 : Step := ⟨⟨⟨1767,2462,548,20920⟩,169543310770176,1032039177005⟩,73,by decide,by decide,by decide⟩
private def s397 : Step := ⟨⟨⟨1801,2510,558,20871⟩,179378212569088,1113775397530⟩,74,by decide,by decide,by decide⟩
private def s398 : Step := ⟨⟨⟨2500,3485,757,28532⟩,471158230876160,4061407017244⟩,103,by decide,by decide,by decide⟩
private def s399 : Step := ⟨⟨⟨183,254,55,2067⟩,188213100544,117869271⟩,0,by decide,by decide,by decide⟩
private def s400 : Step := ⟨⟨⟨200,278,60,2329⟩,244818903040,168238734⟩,1,by decide,by decide,by decide⟩
private def s401 : Step := ⟨⟨⟨211,293,65,2514⟩,292874092544,211692234⟩,2,by decide,by decide,by decide⟩
private def s402 : Step := ⟨⟨⟨226,313,69,2904⟩,356954931200,273860683⟩,3,by decide,by decide,by decide⟩
private def s403 : Step := ⟨⟨⟨249,346,76,2880⟩,476388261888,406778496⟩,4,by decide,by decide,by decide⟩
private def s404 : Step := ⟨⟨⟨268,372,81,3140⟩,588823920640,538985674⟩,5,by decide,by decide,by decide⟩
private def s405 : Step := ⟨⟨⟨295,409,91,3594⟩,796182708224,799166465⟩,7,by decide,by decide,by decide⟩
private def s406 : Step := ⟨⟨⟨351,487,108,4063⟩,1335191666688,1597195933⟩,10,by decide,by decide,by decide⟩
private def s407 : Step := ⟨⟨⟨450,626,139,5436⟩,2813562716160,4348310884⟩,16,by decide,by decide,by decide⟩
private def s408 : Step := ⟨⟨⟨521,724,161,6114⟩,4361720168448,7774976228⟩,20,by decide,by decide,by decide⟩
private def s409 : Step := ⟨⟨⟨750,1044,228,8419⟩,12816073097216,33031832783⟩,32,by decide,by decide,by decide⟩
private def s410 : Step := ⟨⟨⟨714,994,220,8361⟩,11174565642240,27437864297⟩,31,by decide,by decide,by decide⟩
private def s411 : Step := ⟨⟨⟨965,1343,293,10794⟩,27235706208256,90222597195⟩,44,by decide,by decide,by decide⟩
private def s412 : Step := ⟨⟨⟨1446,2014,445,16775⟩,92425607184384,459863749271⟩,73,by decide,by decide,by decide⟩
private def s413 : Step := ⟨⟨⟨1487,2071,459,17575⟩,100733524377600,515343711922⟩,76,by decide,by decide,by decide⟩
private def s414 : Step := ⟨⟨⟨1901,2649,589,23189⟩,210923565875200,1381693281453⟩,101,by decide,by decide,by decide⟩
private def s415 : Step := ⟨⟨⟨350,488,108,8961⟩,1326705278976,1607754763⟩,0,by decide,by decide,by decide⟩
private def s416 : Step := ⟨⟨⟨350,488,108,10361⟩,1326705278976,1607754763⟩,1,by decide,by decide,by decide⟩
private def s417 : Step := ⟨⟨⟨420,586,127,10923⟩,2252760678400,3279920952⟩,2,by decide,by decide,by decide⟩
private def s418 : Step := ⟨⟨⟨420,586,127,12326⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s419 : Step := ⟨⟨⟨520,725,157,12456⟩,4261264752640,7658911630⟩,4,by decide,by decide,by decide⟩
private def s420 : Step := ⟨⟨⟨520,725,154,14521⟩,4199390904320,7545064854⟩,5,by decide,by decide,by decide⟩
private def s421 : Step := ⟨⟨⟨520,725,157,16720⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s422 : Step := ⟨⟨⟨630,879,195,18445⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s423 : Step := ⟨⟨⟨901,1256,279,22511⟩,22508575129600,70021105933⟩,16,by decide,by decide,by decide⟩
private def s424 : Step := ⟨⟨⟨1100,1535,341,25587⟩,40955142733824,156029238110⟩,20,by decide,by decide,by decide⟩
private def s425 : Step := ⟨⟨⟨1350,1883,418,37406⟩,75578221264896,352769102024⟩,32,by decide,by decide,by decide⟩
private def s426 : Step := ⟨⟨⟨1350,1883,408,37306⟩,74202776600576,346190054868⟩,31,by decide,by decide,by decide⟩
private def s427 : Step := ⟨⟨⟨2001,2791,620,45527⟩,245966066417664,1701147081935⟩,44,by decide,by decide,by decide⟩
private def s428 : Step := ⟨⟨⟨2501,3488,775,76803⟩,480070068076544,4147842034257⟩,73,by decide,by decide,by decide⟩
private def s429 : Step := ⟨⟨⟨3001,4186,930,73194⟩,829178280935424,8600191575129⟩,76,by decide,by decide,by decide⟩
private def s430 : Step := ⟨⟨⟨3501,4883,1057,106509⟩,1290381235322880,15600507702257⟩,103,by decide,by decide,by decide⟩
private def s431 : Step := ⟨⟨⟨350,488,106,8891⟩,1308168290304,1584729438⟩,0,by decide,by decide,by decide⟩
private def s432 : Step := ⟨⟨⟨350,488,106,10305⟩,1308168290304,1584729438⟩,1,by decide,by decide,by decide⟩
private def s433 : Step := ⟨⟨⟨350,488,108,11959⟩,1326705278976,1607754763⟩,2,by decide,by decide,by decide⟩
private def s434 : Step := ⟨⟨⟨420,586,124,13140⟩,2212364288000,3219706108⟩,3,by decide,by decide,by decide⟩
private def s435 : Step := ⟨⟨⟨420,586,130,13384⟩,2292767784960,3339653140⟩,4,by decide,by decide,by decide⟩
private def s436 : Step := ⟨⟨⟨420,586,127,16169⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s437 : Step := ⟨⟨⟨520,725,157,16295⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s438 : Step := ⟨⟨⟨630,879,190,18680⟩,7559493713920,16491913877⟩,10,by decide,by decide,by decide⟩
private def s439 : Step := ⟨⟨⟨901,1256,272,22685⟩,22079449333760,68653176066⟩,16,by decide,by decide,by decide⟩
private def s440 : Step := ⟨⟨⟨901,1256,272,28790⟩,22079449333760,68653176066⟩,20,by decide,by decide,by decide⟩
private def s441 : Step := ⟨⟨⟨1350,1883,418,36439⟩,75578221264896,352769102024⟩,32,by decide,by decide,by decide⟩
private def s442 : Step := ⟨⟨⟨1100,1534,341,43635⟩,40955142733824,155702293064⟩,31,by decide,by decide,by decide⟩
private def s443 : Step := ⟨⟨⟨1350,1883,418,66988⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s444 : Step := ⟨⟨⟨2501,3488,775,74817⟩,480070068076544,4147842034257⟩,73,by decide,by decide,by decide⟩
private def s445 : Step := ⟨⟨⟨3001,4186,906,74028⟩,812872257241088,8426888829858⟩,76,by decide,by decide,by decide⟩
private def s446 : Step := ⟨⟨⟨3501,4883,1057,103810⟩,1290381235322880,15600507702257⟩,103,by decide,by decide,by decide⟩
private def s447 : Step := ⟨⟨⟨294,410,91,9498⟩,790165454848,805457011⟩,0,by decide,by decide,by decide⟩
private def s448 : Step := ⟨⟨⟨420,586,130,8862⟩,2292767784960,3339653140⟩,1,by decide,by decide,by decide⟩
private def s449 : Step := ⟨⟨⟨420,586,127,10094⟩,2252760678400,3279920952⟩,2,by decide,by decide,by decide⟩
private def s450 : Step := ⟨⟨⟨420,586,127,11391⟩,2252760678400,3279920952⟩,3,by decide,by decide,by decide⟩
private def s451 : Step := ⟨⟨⟨520,725,161,11190⟩,4343013310464,7809559934⟩,4,by decide,by decide,by decide⟩
private def s452 : Step := ⟨⟨⟨520,725,157,12581⟩,4261264752640,7658911630⟩,5,by decide,by decide,by decide⟩
private def s453 : Step := ⟨⟨⟨520,725,161,14896⟩,4343013310464,7809559934⟩,7,by decide,by decide,by decide⟩
private def s454 : Step := ⟨⟨⟨750,1046,232,15800⟩,12985818152960,33687112323⟩,10,by decide,by decide,by decide⟩
private def s455 : Step := ⟨⟨⟨750,1046,232,23855⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s456 : Step := ⟨⟨⟨901,1256,279,26147⟩,22508575129600,70021105933⟩,20,by decide,by decide,by decide⟩
private def s457 : Step := ⟨⟨⟨1350,1883,408,35835⟩,74202776600576,346190054868⟩,32,by decide,by decide,by decide⟩
private def s458 : Step := ⟨⟨⟨1650,2302,512,31874⟩,138129879859200,788519769358⟩,31,by decide,by decide,by decide⟩
private def s459 : Step := ⟨⟨⟨1650,2302,498,48016⟩,135254251667456,771697512616⟩,44,by decide,by decide,by decide⟩
private def s460 : Step := ⟨⟨⟨3001,4186,930,64638⟩,829178280935424,8600191575129⟩,73,by decide,by decide,by decide⟩
private def s461 : Step := ⟨⟨⟨2501,3488,775,76060⟩,480070068076544,4147842034257⟩,76,by decide,by decide,by decide⟩
private def s462 : Step := ⟨⟨⟨3501,4883,1085,94067⟩,1316270313570304,15921388386716⟩,103,by decide,by decide,by decide⟩
private def s463 : Step := ⟨⟨⟨316,439,97,7499⟩,973976371200,1053621943⟩,0,by decide,by decide,by decide⟩
private def s464 : Step := ⟨⟨⟨379,527,116,7824⟩,1672563130368,2174795908⟩,1,by decide,by decide,by decide⟩
private def s465 : Step := ⟨⟨⟨379,527,116,8956⟩,1672563130368,2174795908⟩,2,by decide,by decide,by decide⟩
private def s466 : Step := ⟨⟨⟨401,557,123,9799⟩,1982954733568,2718384649⟩,3,by decide,by decide,by decide⟩
private def s467 : Step := ⟨⟨⟨421,585,129,10797⟩,2291623526400,3301625792⟩,4,by decide,by decide,by decide⟩
private def s468 : Step := ⟨⟨⟨451,627,138,11569⟩,2812213198848,4346358834⟩,5,by decide,by decide,by decide⟩
private def s469 : Step := ⟨⟨⟨520,723,161,12704⟩,4343013310464,7740496931⟩,7,by decide,by decide,by decide⟩
private def s470 : Step := ⟨⟨⟨600,835,185,15194⟩,6642856099840,13695877387⟩,10,by decide,by decide,by decide⟩
private def s471 : Step := ⟨⟨⟨811,1130,251,18973⟩,16417809235968,45908123333⟩,16,by decide,by decide,by decide⟩
private def s472 : Step := ⟨⟨⟨900,1254,274,23048⟩,22147439001600,68692217088⟩,20,by decide,by decide,by decide⟩
private def s473 : Step := ⟨⟨⟨1178,1641,357,35187⟩,49429552562176,200444998912⟩,32,by decide,by decide,by decide⟩
private def s474 : Step := ⟨⟨⟨1178,1641,365,31984⟩,50266885586944,203925968773⟩,31,by decide,by decide,by decide⟩
private def s475 : Step := ⟨⟨⟨1650,2300,500,40929⟩,135667076300800,771948545360⟩,44,by decide,by decide,by decide⟩
private def s476 : Step := ⟨⟨⟨2702,3767,817,60270⟩,594114231140352,5536684398553⟩,73,by decide,by decide,by decide⟩
private def s477 : Step := ⟨⟨⟨2702,3767,835,61345⟩,604031197642752,5631420081588⟩,76,by decide,by decide,by decide⟩
private def s478 : Step := ⟨⟨⟨3327,4639,1006,88956⟩,1108754070241280,12727443538555⟩,103,by decide,by decide,by decide⟩
private def s479 : Step := ⟨⟨⟨294,408,91,6309⟩,790165454848,792909453⟩,0,by decide,by decide,by decide⟩
private def s480 : Step := ⟨⟨⟨379,527,117,6157⟩,1683404357632,2189247545⟩,1,by decide,by decide,by decide⟩
private def s481 : Step := ⟨⟨⟨379,527,116,7077⟩,1672563130368,2174795908⟩,2,by decide,by decide,by decide⟩
private def s482 : Step := ⟨⟨⟨379,527,116,8246⟩,1672563130368,2174795908⟩,3,by decide,by decide,by decide⟩
private def s483 : Step := ⟨⟨⟨469,652,145,7831⟩,3186037882880,5120467320⟩,4,by decide,by decide,by decide⟩
private def s484 : Step := ⟨⟨⟨469,652,143,8872⟩,3152837345280,5065784484⟩,5,by decide,by decide,by decide⟩
private def s485 : Step := ⟨⟨⟨495,689,153,10580⟩,3743163088896,6373806108⟩,7,by decide,by decide,by decide⟩
private def s486 : Step := ⟨⟨⟨676,941,209,11065⟩,9511534592000,22107791483⟩,10,by decide,by decide,by decide⟩
private def s487 : Step := ⟨⟨⟨750,1044,232,16056⟩,12985818152960,33480320163⟩,16,by decide,by decide,by decide⟩
private def s488 : Step := ⟨⟨⟨857,1193,260,19368⟩,19076725604352,56176845189⟩,20,by decide,by decide,by decide⟩
private def s489 : Step := ⟨⟨⟨1216,1695,369,26643⟩,54416382361600,228244337103⟩,32,by decide,by decide,by decide⟩
private def s490 : Step := ⟨⟨⟨1216,1695,376,24454⟩,55197180100608,231601806743⟩,31,by decide,by decide,by decide⟩
private def s491 : Step := ⟨⟨⟨1569,2187,475,34240⟩,116584333967360,630731810229⟩,44,by decide,by decide,by decide⟩
private def s492 : Step := ⟨⟨⟨2702,3767,835,45967⟩,604031197642752,5631420081588⟩,73,by decide,by decide,by decide⟩
private def s493 : Step := ⟨⟨⟨2377,3314,736,55080⟩,411942278922240,3379289207231⟩,76,by decide,by decide,by decide⟩
private def s494 : Step := ⟨⟨⟨3327,4639,1006,70549⟩,1108754070241280,12727443538555⟩,103,by decide,by decide,by decide⟩
private def s495 : Step := ⟨⟨⟨281,390,87,4397⟩,690560696320,662678389⟩,0,by decide,by decide,by decide⟩
private def s496 : Step := ⟨⟨⟨316,439,97,4728⟩,973976371200,1053621943⟩,1,by decide,by decide,by decide⟩
private def s497 : Step := ⟨⟨⟨316,439,97,5827⟩,973976371200,1053621943⟩,2,by decide,by decide,by decide⟩
private def s498 : Step := ⟨⟨⟨375,522,115,5576⟩,1622760488960,2095158739⟩,3,by decide,by decide,by decide⟩
private def s499 : Step := ⟨⟨⟨375,522,115,6601⟩,1622760488960,2095158739⟩,4,by decide,by decide,by decide⟩
private def s500 : Step := ⟨⟨⟨421,585,129,6530⟩,2291623526400,3301625792⟩,5,by decide,by decide,by decide⟩
private def s501 : Step := ⟨⟨⟨469,652,145,7435⟩,3186037882880,5120467320⟩,7,by decide,by decide,by decide⟩
private def s502 : Step := ⟨⟨⟨558,776,172,8601⟩,5345194541056,10227269032⟩,10,by decide,by decide,by decide⟩
private def s503 : Step := ⟨⟨⟨750,1044,228,11089⟩,12816073097216,33031832783⟩,16,by decide,by decide,by decide⟩
private def s504 : Step := ⟨⟨⟨804,1119,250,13366⟩,16053760163840,44348152608⟩,20,by decide,by decide,by decide⟩
private def s505 : Step := ⟨⟨⟨1178,1641,357,18557⟩,49429552562176,200444998912⟩,32,by decide,by decide,by decide⟩
private def s506 : Step := ⟨⟨⟨1178,1641,365,16814⟩,50266885586944,203925968773⟩,31,by decide,by decide,by decide⟩
private def s507 : Step := ⟨⟨⟨1446,2015,449,23924⟩,93054074880000,463811012032⟩,44,by decide,by decide,by decide⟩
private def s508 : Step := ⟨⟨⟨2141,2985,665,36477⟩,301800972877824,2230300071914⟩,71,by decide,by decide,by decide⟩
private def s509 : Step := ⟨⟨⟨2500,3486,757,36688⟩,471158230876160,4065158762879⟩,76,by decide,by decide,by decide⟩
private def s510 : Step := ⟨⟨⟨3212,4478,971,49427⟩,997581528760320,11050409871062⟩,103,by decide,by decide,by decide⟩
private def s511 : Step := ⟨⟨⟨239,332,74,2815⟩,426141286400,349077659⟩,0,by decide,by decide,by decide⟩
private def s512 : Step := ⟨⟨⟨269,373,83,2982⟩,604708536320,553942033⟩,1,by decide,by decide,by decide⟩
private def s513 : Step := ⟨⟨⟨281,390,87,3431⟩,690560696320,662678389⟩,2,by decide,by decide,by decide⟩
private def s514 : Step := ⟨⟨⟨316,439,97,3557⟩,973976371200,1053621943⟩,3,by decide,by decide,by decide⟩
private def s515 : Step := ⟨⟨⟨334,464,103,3878⟩,1153155727360,1318278333⟩,4,by decide,by decide,by decide⟩
private def s516 : Step := ⟨⟨⟨350,486,108,4272⟩,1326705278976,1586684409⟩,5,by decide,by decide,by decide⟩
private def s517 : Step := ⟨⟨⟨401,557,123,4785⟩,1982954733568,2718384649⟩,7,by decide,by decide,by decide⟩
private def s518 : Step := ⟨⟨⟨469,652,143,5761⟩,3152837345280,5065784484⟩,10,by decide,by decide,by decide⟩
private def s519 : Step := ⟨⟨⟨600,835,185,7450⟩,6642856099840,13695877387⟩,16,by decide,by decide,by decide⟩
private def s520 : Step := ⟨⟨⟨675,939,209,8899⟩,9480073379840,21956989048⟩,20,by decide,by decide,by decide⟩
private def s521 : Step := ⟨⟨⟨964,1343,299,11950⟩,27592923545600,91653421946⟩,32,by decide,by decide,by decide⟩
private def s522 : Step := ⟨⟨⟨964,1343,299,11236⟩,27592923545600,91653421946⟩,31,by decide,by decide,by decide⟩
private def s523 : Step := ⟨⟨⟨1217,1695,378,15749⟩,55521299398656,232557160904⟩,44,by decide,by decide,by decide⟩
private def s524 : Step := ⟨⟨⟨1901,2650,591,23444⟩,211465680191488,1387020449070⟩,73,by decide,by decide,by decide⟩
private def s525 : Step := ⟨⟨⟨2000,2787,606,25432⟩,241468805218304,1663490943357⟩,76,by decide,by decide,by decide⟩
private def s526 : Step := ⟨⟨⟨2502,3487,777,32175⟩,481439418417152,4152321171330⟩,101,by decide,by decide,by decide⟩
private def s527 : Step := ⟨⟨⟨210,291,65,2379⟩,289785774080,207093695⟩,0,by decide,by decide,by decide⟩
private def s528 : Step := ⟨⟨⟨226,314,70,2721⟩,360816574464,279745237⟩,1,by decide,by decide,by decide⟩
private def s529 : Step := ⟨⟨⟨266,369,80,2803⟩,573684056064,520167980⟩,2,by decide,by decide,by decide⟩
private def s530 : Step := ⟨⟨⟨266,369,82,3204⟩,584418590720,530141366⟩,3,by decide,by decide,by decide⟩
private def s531 : Step := ⟨⟨⟨281,390,87,3586⟩,690560696320,662678389⟩,4,by decide,by decide,by decide⟩
private def s532 : Step := ⟨⟨⟨316,439,97,3508⟩,973976371200,1053621943⟩,5,by decide,by decide,by decide⟩
private def s533 : Step := ⟨⟨⟨379,527,115,3825⟩,1661683630080,2160302019⟩,7,by decide,by decide,by decide⟩
private def s534 : Step := ⟨⟨⟨401,557,123,5123⟩,1982954733568,2718384649⟩,10,by decide,by decide,by decide⟩
private def s535 : Step := ⟨⟨⟨568,791,173,5891⟩,5586192957440,10925512348⟩,16,by decide,by decide,by decide⟩
private def s536 : Step := ⟨⟨⟨599,834,185,7602⟩,6618111016960,13643196297⟩,20,by decide,by decide,by decide⟩
private def s537 : Step := ⟨⟨⟨856,1192,260,10606⟩,19026984566784,56025541488⟩,32,by decide,by decide,by decide⟩
private def s538 : Step := ⟨⟨⟨856,1192,260,9858⟩,19026984566784,56025541488⟩,31,by decide,by decide,by decide⟩
private def s539 : Step := ⟨⟨⟨1101,1533,341,12729⟩,41038565081088,155375814677⟩,44,by decide,by decide,by decide⟩
private def s540 : Step := ⟨⟨⟨1651,2300,512,20553⟩,138317479280640,786316039690⟩,73,by decide,by decide,by decide⟩
private def s541 : Step := ⟨⟨⟨1801,2510,546,20668⟩,176443510489088,1095102265817⟩,76,by decide,by decide,by decide⟩
private def s542 : Step := ⟨⟨⟨2252,3138,699,27740⟩,350998036480000,2723312772953⟩,103,by decide,by decide,by decide⟩
private def s543 : Step := ⟨⟨⟨210,293,63,1825⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s544 : Step := ⟨⟨⟨210,293,63,2106⟩,283090354176,206678784⟩,1,by decide,by decide,by decide⟩
private def s545 : Step := ⟨⟨⟨210,293,65,2411⟩,289785774080,211692234⟩,2,by decide,by decide,by decide⟩
private def s546 : Step := ⟨⟨⟨250,348,78,2290⟩,490108092416,422716393⟩,3,by decide,by decide,by decide⟩
private def s547 : Step := ⟨⟨⟨250,348,76,2725⟩,480667500544,414368386⟩,4,by decide,by decide,by decide⟩
private def s548 : Step := ⟨⟨⟨250,348,78,3305⟩,490108092416,422716393⟩,5,by decide,by decide,by decide⟩
private def s549 : Step := ⟨⟨⟨294,410,91,3400⟩,790165454848,805457011⟩,7,by decide,by decide,by decide⟩
private def s550 : Step := ⟨⟨⟨350,488,108,3887⟩,1326705278976,1607754763⟩,10,by decide,by decide,by decide⟩
private def s551 : Step := ⟨⟨⟨520,725,157,4647⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s552 : Step := ⟨⟨⟨630,878,195,5080⟩,7709474160640,16765904450⟩,20,by decide,by decide,by decide⟩
private def s553 : Step := ⟨⟨⟨900,1255,272,7339⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s554 : Step := ⟨⟨⟨751,1046,232,7311⟩,13024603668480,33687112323⟩,31,by decide,by decide,by decide⟩
private def s555 : Step := ⟨⟨⟨1100,1534,341,9143⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s556 : Step := ⟨⟨⟨1650,2301,498,14754⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s557 : Step := ⟨⟨⟨1651,2301,512,14739⟩,138317479280640,787417379725⟩,76,by decide,by decide,by decide⟩
private def s558 : Step := ⟨⟨⟨2000,2788,604,22122⟩,240862397726720,1661128510194⟩,103,by decide,by decide,by decide⟩
private def s559 : Step := ⟨⟨⟨294,410,89,6057⟩,777085255680,791788817⟩,0,by decide,by decide,by decide⟩
private def s560 : Step := ⟨⟨⟨294,410,89,6948⟩,777085255680,791788817⟩,1,by decide,by decide,by decide⟩
private def s561 : Step := ⟨⟨⟨294,410,91,7894⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s562 : Step := ⟨⟨⟨350,488,108,7892⟩,1326705278976,1607754763⟩,3,by decide,by decide,by decide⟩
private def s563 : Step := ⟨⟨⟨350,488,108,8951⟩,1326705278976,1607754763⟩,4,by decide,by decide,by decide⟩
private def s564 : Step := ⟨⟨⟨350,488,108,10336⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s565 : Step := ⟨⟨⟨420,586,127,11321⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s566 : Step := ⟨⟨⟨520,725,157,12694⟩,4261264752640,7658911630⟩,10,by decide,by decide,by decide⟩
private def s567 : Step := ⟨⟨⟨750,1046,226,15636⟩,12730741817344,33009058589⟩,16,by decide,by decide,by decide⟩
private def s568 : Step := ⟨⟨⟨901,1256,279,17033⟩,22508575129600,70021105933⟩,20,by decide,by decide,by decide⟩
private def s569 : Step := ⟨⟨⟨1100,1534,341,24987⟩,40955142733824,155702293064⟩,32,by decide,by decide,by decide⟩
private def s570 : Step := ⟨⟨⟨900,1255,279,29711⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s571 : Step := ⟨⟨⟨1350,1883,408,34728⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s572 : Step := ⟨⟨⟨2001,2790,620,52261⟩,245966066417664,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s573 : Step := ⟨⟨⟨2000,2789,604,59812⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s574 : Step := ⟨⟨⟨3501,4883,1085,63204⟩,1316270313570304,15921388386716⟩,103,by decide,by decide,by decide⟩
private def s575 : Step := ⟨⟨⟨294,410,89,5939⟩,777085255680,791788817⟩,0,by decide,by decide,by decide⟩
private def s576 : Step := ⟨⟨⟨294,410,89,6812⟩,777085255680,791788817⟩,1,by decide,by decide,by decide⟩
private def s577 : Step := ⟨⟨⟨350,488,108,6918⟩,1326705278976,1607754763⟩,2,by decide,by decide,by decide⟩
private def s578 : Step := ⟨⟨⟨350,488,108,7736⟩,1326705278976,1607754763⟩,3,by decide,by decide,by decide⟩
private def s579 : Step := ⟨⟨⟨350,488,106,9042⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s580 : Step := ⟨⟨⟨420,586,130,8706⟩,2292767784960,3339653140⟩,5,by decide,by decide,by decide⟩
private def s581 : Step := ⟨⟨⟨420,586,127,11100⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s582 : Step := ⟨⟨⟨520,725,157,12447⟩,4261264752640,7658911630⟩,10,by decide,by decide,by decide⟩
private def s583 : Step := ⟨⟨⟨750,1046,226,15332⟩,12730741817344,33009058589⟩,16,by decide,by decide,by decide⟩
private def s584 : Step := ⟨⟨⟨901,1256,272,17348⟩,22079449333760,68653176066⟩,20,by decide,by decide,by decide⟩
private def s585 : Step := ⟨⟨⟨1100,1534,332,25696⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s586 : Step := ⟨⟨⟨900,1255,279,29124⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s587 : Step := ⟨⟨⟨1350,1883,418,32476⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s588 : Step := ⟨⟨⟨2001,2790,620,51229⟩,245966066417664,1699185179819⟩,73,by decide,by decide,by decide⟩
private def s589 : Step := ⟨⟨⟨2000,2789,604,58647⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s590 : Step := ⟨⟨⟨3001,4185,930,64711⟩,829178280935424,8593576488693⟩,103,by decide,by decide,by decide⟩
private def s591 : Step := ⟨⟨⟨250,349,76,6275⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s592 : Step := ⟨⟨⟨350,488,108,6008⟩,1326705278976,1607754763⟩,1,by decide,by decide,by decide⟩
private def s593 : Step := ⟨⟨⟨350,488,106,6807⟩,1308168290304,1584729438⟩,2,by decide,by decide,by decide⟩
private def s594 : Step := ⟨⟨⟨350,488,106,7631⟩,1308168290304,1584729438⟩,3,by decide,by decide,by decide⟩
private def s595 : Step := ⟨⟨⟨420,586,130,7654⟩,2292767784960,3339653140⟩,4,by decide,by decide,by decide⟩
private def s596 : Step := ⟨⟨⟨420,586,127,8636⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s597 : Step := ⟨⟨⟨520,725,157,9501⟩,4261264752640,7658911630⟩,7,by decide,by decide,by decide⟩
private def s598 : Step := ⟨⟨⟨630,879,195,10745⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s599 : Step := ⟨⟨⟨631,879,195,15628⟩,7736885510144,16827402390⟩,16,by decide,by decide,by decide⟩
private def s600 : Step := ⟨⟨⟨750,1046,232,17530⟩,12985818152960,33687112323⟩,20,by decide,by decide,by decide⟩
private def s601 : Step := ⟨⟨⟨1100,1534,332,24683⟩,40133103452160,152499774767⟩,32,by decide,by decide,by decide⟩
private def s602 : Step := ⟨⟨⟨1350,1883,418,21732⟩,75578221264896,352769102024⟩,31,by decide,by decide,by decide⟩
private def s603 : Step := ⟨⟨⟨1350,1883,408,32708⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s604 : Step := ⟨⟨⟨2501,3488,775,43899⟩,480070068076544,4147842034257⟩,73,by decide,by decide,by decide⟩
private def s605 : Step := ⟨⟨⟨2000,2789,620,53041⟩,245690786119680,1697224818404⟩,76,by decide,by decide,by decide⟩
private def s606 : Step := ⟨⟨⟨3001,4185,906,65253⟩,812872257241088,8420412037186⟩,103,by decide,by decide,by decide⟩
private def s607 : Step := ⟨⟨⟨250,349,76,5640⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s608 : Step := ⟨⟨⟨350,488,108,5401⟩,1326705278976,1607754763⟩,1,by decide,by decide,by decide⟩
private def s609 : Step := ⟨⟨⟨350,488,106,6123⟩,1308168290304,1584729438⟩,2,by decide,by decide,by decide⟩
private def s610 : Step := ⟨⟨⟨350,488,106,6861⟩,1308168290304,1584729438⟩,3,by decide,by decide,by decide⟩
private def s611 : Step := ⟨⟨⟨350,488,106,7803⟩,1308168290304,1584729438⟩,4,by decide,by decide,by decide⟩
private def s612 : Step := ⟨⟨⟨420,586,127,7769⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s613 : Step := ⟨⟨⟨420,586,127,9584⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s614 : Step := ⟨⟨⟨630,879,195,9662⟩,7709474160640,16827402390⟩,10,by decide,by decide,by decide⟩
private def s615 : Step := ⟨⟨⟨631,879,195,14024⟩,7736885510144,16827402390⟩,16,by decide,by decide,by decide⟩
private def s616 : Step := ⟨⟨⟨750,1046,232,15740⟩,12985818152960,33687112323⟩,20,by decide,by decide,by decide⟩
private def s617 : Step := ⟨⟨⟨900,1255,279,26886⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s618 : Step := ⟨⟨⟨900,1255,272,26721⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s619 : Step := ⟨⟨⟨1350,1883,418,27999⟩,75578221264896,352769102024⟩,44,by decide,by decide,by decide⟩
private def s620 : Step := ⟨⟨⟨2001,2790,604,46814⟩,241131854233600,1664965815864⟩,73,by decide,by decide,by decide⟩
private def s621 : Step := ⟨⟨⟨2000,2789,604,50626⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s622 : Step := ⟨⟨⟨3001,4185,930,55811⟩,829178280935424,8593576488693⟩,103,by decide,by decide,by decide⟩
private def s623 : Step := ⟨⟨⟨294,410,91,4253⟩,790165454848,805457011⟩,0,by decide,by decide,by decide⟩
private def s624 : Step := ⟨⟨⟨294,410,91,4849⟩,790165454848,805457011⟩,1,by decide,by decide,by decide⟩
private def s625 : Step := ⟨⟨⟨294,410,91,5644⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s626 : Step := ⟨⟨⟨350,488,104,6205⟩,1289487646720,1561556019⟩,3,by decide,by decide,by decide⟩
private def s627 : Step := ⟨⟨⟨420,586,127,6054⟩,2252760678400,3279920952⟩,4,by decide,by decide,by decide⟩
private def s628 : Step := ⟨⟨⟨420,586,127,6617⟩,2252760678400,3279920952⟩,5,by decide,by decide,by decide⟩
private def s629 : Step := ⟨⟨⟨420,586,130,7799⟩,2292767784960,3339653140⟩,7,by decide,by decide,by decide⟩
private def s630 : Step := ⟨⟨⟨520,725,161,8728⟩,4343013310464,7809559934⟩,10,by decide,by decide,by decide⟩
private def s631 : Step := ⟨⟨⟨750,1046,232,10781⟩,12985818152960,33687112323⟩,16,by decide,by decide,by decide⟩
private def s632 : Step := ⟨⟨⟨750,1046,226,14133⟩,12730741817344,33009058589⟩,20,by decide,by decide,by decide⟩
private def s633 : Step := ⟨⟨⟨900,1255,272,24337⟩,22024701870080,68477558806⟩,32,by decide,by decide,by decide⟩
private def s634 : Step := ⟨⟨⟨900,1255,279,21180⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s635 : Step := ⟨⟨⟨1350,1883,408,24991⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s636 : Step := ⟨⟨⟨2001,2790,604,39738⟩,241131854233600,1664965815864⟩,73,by decide,by decide,by decide⟩
private def s637 : Step := ⟨⟨⟨2000,2789,620,40290⟩,245690786119680,1697224818404⟩,76,by decide,by decide,by decide⟩
private def s638 : Step := ⟨⟨⟨3001,4185,906,49959⟩,812872257241088,8420412037186⟩,103,by decide,by decide,by decide⟩
private def s639 : Step := ⟨⟨⟨226,314,70,3950⟩,360816574464,279745237⟩,0,by decide,by decide,by decide⟩
private def s640 : Step := ⟨⟨⟨269,373,83,3911⟩,604708536320,553942033⟩,1,by decide,by decide,by decide⟩
private def s641 : Step := ⟨⟨⟨281,390,87,4437⟩,690560696320,662678389⟩,2,by decide,by decide,by decide⟩
private def s642 : Step := ⟨⟨⟨316,439,97,4650⟩,973976371200,1053621943⟩,3,by decide,by decide,by decide⟩
private def s643 : Step := ⟨⟨⟨334,464,103,5053⟩,1153155727360,1318278333⟩,4,by decide,by decide,by decide⟩
private def s644 : Step := ⟨⟨⟨350,486,108,5520⟩,1326705278976,1586684409⟩,5,by decide,by decide,by decide⟩
private def s645 : Step := ⟨⟨⟨401,557,123,6201⟩,1982954733568,2718384649⟩,7,by decide,by decide,by decide⟩
private def s646 : Step := ⟨⟨⟨469,652,145,7237⟩,3186037882880,5120467320⟩,10,by decide,by decide,by decide⟩
private def s647 : Step := ⟨⟨⟨630,877,192,9323⟩,7619678044160,16505144473⟩,16,by decide,by decide,by decide⟩
private def s648 : Step := ⟨⟨⟨675,939,209,11288⟩,9480073379840,21956989048⟩,20,by decide,by decide,by decide⟩
private def s649 : Step := ⟨⟨⟨991,1381,307,14940⟩,29945385451520,102338976877⟩,32,by decide,by decide,by decide⟩
private def s650 : Step := ⟨⟨⟨964,1343,299,14602⟩,27592923545600,91653421946⟩,31,by decide,by decide,by decide⟩
private def s651 : Step := ⟨⟨⟨1178,1641,365,20153⟩,50266885586944,203925968773⟩,43,by decide,by decide,by decide⟩
private def s652 : Step := ⟨⟨⟨1901,2650,591,30145⟩,211465680191488,1387020449070⟩,73,by decide,by decide,by decide⟩
private def s653 : Step := ⟨⟨⟨2000,2787,606,32377⟩,241468805218304,1663490943357⟩,76,by decide,by decide,by decide⟩
private def s654 : Step := ⟨⟨⟨2677,3731,810,41838⟩,578088621309952,5332310404523⟩,103,by decide,by decide,by decide⟩
private def s655 : Step := ⟨⟨⟨210,293,63,3119⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s656 : Step := ⟨⟨⟨251,349,76,2876⟩,484966924288,418199213⟩,1,by decide,by decide,by decide⟩
private def s657 : Step := ⟨⟨⟨251,349,76,3504⟩,484966924288,418199213⟩,2,by decide,by decide,by decide⟩
private def s658 : Step := ⟨⟨⟨294,410,89,3474⟩,777085255680,791788817⟩,3,by decide,by decide,by decide⟩
private def s659 : Step := ⟨⟨⟨294,410,91,3918⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s660 : Step := ⟨⟨⟨350,488,108,3739⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s661 : Step := ⟨⟨⟨350,488,106,5127⟩,1308168290304,1584729438⟩,7,by decide,by decide,by decide⟩
private def s662 : Step := ⟨⟨⟨420,586,130,5504⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s663 : Step := ⟨⟨⟨520,725,157,8344⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s664 : Step := ⟨⟨⟨630,878,190,8679⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s665 : Step := ⟨⟨⟨900,1255,279,10920⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s666 : Step := ⟨⟨⟨900,1255,272,11036⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s667 : Step := ⟨⟨⟨1100,1534,332,16378⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s668 : Step := ⟨⟨⟨1650,2301,498,26477⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s669 : Step := ⟨⟨⟨1651,2301,512,27053⟩,138317479280640,787417379725⟩,76,by decide,by decide,by decide⟩
private def s670 : Step := ⟨⟨⟨2501,3487,775,28056⟩,480070068076544,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s671 : Step := ⟨⟨⟨190,264,59,2505⟩,215642275840,140746391⟩,0,by decide,by decide,by decide⟩
private def s672 : Step := ⟨⟨⟨211,293,65,2683⟩,292874092544,211692234⟩,1,by decide,by decide,by decide⟩
private def s673 : Step := ⟨⟨⟨226,314,70,3018⟩,360816574464,279745237⟩,2,by decide,by decide,by decide⟩
private def s674 : Step := ⟨⟨⟨249,346,76,3212⟩,476388261888,406778496⟩,3,by decide,by decide,by decide⟩
private def s675 : Step := ⟨⟨⟨268,372,83,3343⟩,599698964480,549189173⟩,4,by decide,by decide,by decide⟩
private def s676 : Step := ⟨⟨⟨281,390,87,3741⟩,690560696320,662678389⟩,5,by decide,by decide,by decide⟩
private def s677 : Step := ⟨⟨⟨316,439,97,4368⟩,973976371200,1053621943⟩,7,by decide,by decide,by decide⟩
private def s678 : Step := ⟨⟨⟨376,522,116,4884⟩,1643119116288,2109199468⟩,10,by decide,by decide,by decide⟩
private def s679 : Step := ⟨⟨⟨495,689,151,6372⟩,3706185580544,6309269027⟩,16,by decide,by decide,by decide⟩
private def s680 : Step := ⟨⟨⟨568,790,173,7405⟩,5586192957440,10881173726⟩,20,by decide,by decide,by decide⟩
private def s681 : Step := ⟨⟨⟨804,1119,248,9749⟩,15956629258240,44073024558⟩,32,by decide,by decide,by decide⟩
private def s682 : Step := ⟨⟨⟨812,1130,249,9153⟩,16363847680000,45624253842⟩,31,by decide,by decide,by decide⟩
private def s683 : Step := ⟨⟨⟨1046,1457,317,12964⟩,34623417221120,124655308417⟩,44,by decide,by decide,by decide⟩
private def s684 : Step := ⟨⟨⟨1569,2186,475,20959⟩,116584333967360,629804346601⟩,73,by decide,by decide,by decide⟩
private def s685 : Step := ⟨⟨⟨1569,2186,486,20988⟩,118626912043008,641115905825⟩,75,by decide,by decide,by decide⟩
private def s686 : Step := ⟨⟨⟨2141,2983,661,26475⟩,300424516599808,2215083145663⟩,103,by decide,by decide,by decide⟩
private def s687 : Step := ⟨⟨⟨169,235,51,2084⟩,149005795328,86742047⟩,0,by decide,by decide,by decide⟩
private def s688 : Step := ⟨⟨⟨190,264,57,2220⟩,210162155520,137081511⟩,1,by decide,by decide,by decide⟩
private def s689 : Step := ⟨⟨⟨201,278,62,2398⟩,253699031040,172517110⟩,2,by decide,by decide,by decide⟩
private def s690 : Step := ⟨⟨⟨211,293,65,2791⟩,292874092544,211692234⟩,3,by decide,by decide,by decide⟩
private def s691 : Step := ⟨⟨⟨226,313,70,3025⟩,360816574464,276897427⟩,4,by decide,by decide,by decide⟩
private def s692 : Step := ⟨⟨⟨250,347,76,3060⟩,480667500544,410561506⟩,5,by decide,by decide,by decide⟩
private def s693 : Step := ⟨⟨⟨281,390,87,3375⟩,690560696320,662678389⟩,7,by decide,by decide,by decide⟩
private def s694 : Step := ⟨⟨⟨334,464,103,3882⟩,1153155727360,1318278333⟩,10,by decide,by decide,by decide⟩
private def s695 : Step := ⟨⟨⟨421,585,129,5460⟩,2291623526400,3301625792⟩,16,by decide,by decide,by decide⟩
private def s696 : Step := ⟨⟨⟨496,689,151,6051⟩,3722940776448,6309269027⟩,20,by decide,by decide,by decide⟩
private def s697 : Step := ⟨⟨⟨676,941,209,8707⟩,9511534592000,22107791483⟩,32,by decide,by decide,by decide⟩
private def s698 : Step := ⟨⟨⟨676,941,205,8481⟩,9373527834624,21779095054⟩,31,by decide,by decide,by decide⟩
private def s699 : Step := ⟨⟨⟨901,1254,274,10683⟩,22202515456000,68692217088⟩,44,by decide,by decide,by decide⟩
private def s700 : Step := ⟨⟨⟨1351,1881,410,17538⟩,74602437935104,346324061737⟩,73,by decide,by decide,by decide⟩
private def s701 : Step := ⟨⟨⟨1351,1881,418,18017⟩,75703656644608,351564298530⟩,75,by decide,by decide,by decide⟩
private def s702 : Step := ⟨⟨⟨1801,2509,546,23852⟩,176443510489088,1093698916531⟩,101,by decide,by decide,by decide⟩
private def s703 : Step := ⟨⟨⟨226,314,70,4672⟩,360816574464,279745237⟩,0,by decide,by decide,by decide⟩
private def s704 : Step := ⟨⟨⟨226,314,70,5620⟩,360816574464,279745237⟩,1,by decide,by decide,by decide⟩
private def s705 : Step := ⟨⟨⟨266,369,82,5631⟩,584418590720,530141366⟩,2,by decide,by decide,by decide⟩
private def s706 : Step := ⟨⟨⟨266,369,82,6604⟩,584418590720,530141366⟩,3,by decide,by decide,by decide⟩
private def s707 : Step := ⟨⟨⟨266,369,82,7984⟩,584418590720,530141366⟩,4,by decide,by decide,by decide⟩
private def s708 : Step := ⟨⟨⟨316,439,97,7362⟩,973976371200,1053621943⟩,5,by decide,by decide,by decide⟩
private def s709 : Step := ⟨⟨⟨379,527,117,7861⟩,1683404357632,2189247545⟩,7,by decide,by decide,by decide⟩
private def s710 : Step := ⟨⟨⟨379,527,117,11278⟩,1683404357632,2189247545⟩,10,by decide,by decide,by decide⟩
private def s711 : Step := ⟨⟨⟨568,791,173,12384⟩,5586192957440,10925512348⟩,16,by decide,by decide,by decide⟩
private def s712 : Step := ⟨⟨⟨676,941,205,14025⟩,9373527834624,21779095054⟩,20,by decide,by decide,by decide⟩
private def s713 : Step := ⟨⟨⟨812,1130,251,22270⟩,16463159623680,45908123333⟩,32,by decide,by decide,by decide⟩
private def s714 : Step := ⟨⟨⟨812,1130,247,21665⟩,16264207532032,45339607027⟩,31,by decide,by decide,by decide⟩
private def s715 : Step := ⟨⟨⟨992,1381,301,33054⟩,29567671336960,100782684488⟩,44,by decide,by decide,by decide⟩
private def s716 : Step := ⟨⟨⟨1802,2511,546,39736⟩,176662758031360,1096506839289⟩,73,by decide,by decide,by decide⟩
private def s717 : Step := ⟨⟨⟨1801,2510,546,42587⟩,176443510489088,1095102265817⟩,76,by decide,by decide,by decide⟩
private def s718 : Step := ⟨⟨⟨2702,3766,817,51059⟩,594114231140352,5531955670615⟩,103,by decide,by decide,by decide⟩
private def s719 : Step := ⟨⟨⟨250,349,74,4828⟩,471125196800,409695834⟩,0,by decide,by decide,by decide⟩
private def s720 : Step := ⟨⟨⟨251,349,76,5155⟩,484966924288,418199213⟩,1,by decide,by decide,by decide⟩
private def s721 : Step := ⟨⟨⟨294,410,91,5301⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s722 : Step := ⟨⟨⟨294,410,89,6168⟩,777085255680,791788817⟩,3,by decide,by decide,by decide⟩
private def s723 : Step := ⟨⟨⟨294,410,91,6861⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s724 : Step := ⟨⟨⟨350,488,108,6731⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s725 : Step := ⟨⟨⟨420,586,127,7647⟩,2252760678400,3279920952⟩,7,by decide,by decide,by decide⟩
private def s726 : Step := ⟨⟨⟨520,725,161,8524⟩,4343013310464,7809559934⟩,10,by decide,by decide,by decide⟩
private def s727 : Step := ⟨⟨⟨631,879,190,11745⟩,7586330968064,16491913877⟩,16,by decide,by decide,by decide⟩
private def s728 : Step := ⟨⟨⟨750,1046,226,13400⟩,12730741817344,33009058589⟩,20,by decide,by decide,by decide⟩
private def s729 : Step := ⟨⟨⟨900,1255,279,19408⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s730 : Step := ⟨⟨⟨1100,1534,341,17183⟩,40955142733824,155702293064⟩,31,by decide,by decide,by decide⟩
private def s731 : Step := ⟨⟨⟨1350,1883,408,23810⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s732 : Step := ⟨⟨⟨1650,2301,512,41229⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s733 : Step := ⟨⟨⟨2000,2789,604,39064⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s734 : Step := ⟨⟨⟨2501,3487,775,50316⟩,480070068076544,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s735 : Step := ⟨⟨⟨226,314,70,4456⟩,360816574464,279745237⟩,0,by decide,by decide,by decide⟩
private def s736 : Step := ⟨⟨⟨226,314,70,5360⟩,360816574464,279745237⟩,1,by decide,by decide,by decide⟩
private def s737 : Step := ⟨⟨⟨269,373,83,5319⟩,604708536320,553942033⟩,2,by decide,by decide,by decide⟩
private def s738 : Step := ⟨⟨⟨268,372,83,6223⟩,599698964480,549189173⟩,3,by decide,by decide,by decide⟩
private def s739 : Step := ⟨⟨⟨316,439,97,6181⟩,973976371200,1053621943⟩,4,by decide,by decide,by decide⟩
private def s740 : Step := ⟨⟨⟨316,439,97,7022⟩,973976371200,1053621943⟩,5,by decide,by decide,by decide⟩
private def s741 : Step := ⟨⟨⟨376,522,113,7919⟩,1610984194048,2066952475⟩,7,by decide,by decide,by decide⟩
private def s742 : Step := ⟨⟨⟨451,627,138,8793⟩,2812213198848,4346358834⟩,10,by decide,by decide,by decide⟩
private def s743 : Step := ⟨⟨⟨558,776,174,11605⟩,5391987507200,10319091253⟩,16,by decide,by decide,by decide⟩
private def s744 : Step := ⟨⟨⟨675,939,211,12863⟩,9548426379264,22119378957⟩,20,by decide,by decide,by decide⟩
private def s745 : Step := ⟨⟨⟨964,1343,293,18381⟩,27172624138240,90222597195⟩,32,by decide,by decide,by decide⟩
private def s746 : Step := ⟨⟨⟨804,1119,250,18011⟩,16053760163840,44348152608⟩,29,by decide,by decide,by decide⟩
private def s747 : Step := ⟨⟨⟨1178,1641,367,22111⟩,50475036573696,204792136984⟩,42,by decide,by decide,by decide⟩
private def s748 : Step := ⟨⟨⟨1767,2462,550,35213⟩,170011506245632,1034962418522⟩,71,by decide,by decide,by decide⟩
private def s749 : Step := ⟨⟨⟨1767,2462,535,39639⟩,166482728189952,1012948579305⟩,74,by decide,by decide,by decide⟩
private def s750 : Step := ⟨⟨⟨2677,3731,831,46810⟩,589433174753280,5439590961728⟩,103,by decide,by decide,by decide⟩
private def s751 : Step := ⟨⟨⟨250,349,76,4036⟩,480667500544,418199213⟩,0,by decide,by decide,by decide⟩
private def s752 : Step := ⟨⟨⟨251,349,76,4604⟩,484966924288,418199213⟩,1,by decide,by decide,by decide⟩
private def s753 : Step := ⟨⟨⟨294,410,91,4737⟩,790165454848,805457011⟩,2,by decide,by decide,by decide⟩
private def s754 : Step := ⟨⟨⟨294,410,91,5342⟩,790165454848,805457011⟩,3,by decide,by decide,by decide⟩
private def s755 : Step := ⟨⟨⟨294,410,91,6126⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s756 : Step := ⟨⟨⟨350,488,108,6013⟩,1326705278976,1607754763⟩,5,by decide,by decide,by decide⟩
private def s757 : Step := ⟨⟨⟨420,586,130,6614⟩,2292767784960,3339653140⟩,7,by decide,by decide,by decide⟩
private def s758 : Step := ⟨⟨⟨420,586,130,8619⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s759 : Step := ⟨⟨⟨631,879,190,10503⟩,7586330968064,16491913877⟩,16,by decide,by decide,by decide⟩
private def s760 : Step := ⟨⟨⟨750,1046,226,11990⟩,12730741817344,33009058589⟩,20,by decide,by decide,by decide⟩
private def s761 : Step := ⟨⟨⟨900,1255,279,17333⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s762 : Step := ⟨⟨⟨900,1255,272,17411⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s763 : Step := ⟨⟨⟨1350,1883,408,21305⟩,74202776600576,346190054868⟩,44,by decide,by decide,by decide⟩
private def s764 : Step := ⟨⟨⟨1650,2301,512,36808⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s765 : Step := ⟨⟨⟨2000,2789,604,34941⟩,240862397726720,1663046410409⟩,76,by decide,by decide,by decide⟩
private def s766 : Step := ⟨⟨⟨2501,3487,775,44947⟩,480070068076544,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s767 : Step := ⟨⟨⟨210,293,62,4476⟩,279710269440,204151930⟩,0,by decide,by decide,by decide⟩
private def s768 : Step := ⟨⟨⟨210,293,65,5000⟩,289785774080,211692234⟩,1,by decide,by decide,by decide⟩
private def s769 : Step := ⟨⟨⟨251,349,76,4804⟩,484966924288,418199213⟩,2,by decide,by decide,by decide⟩
private def s770 : Step := ⟨⟨⟨250,348,78,5682⟩,490108092416,422716393⟩,3,by decide,by decide,by decide⟩
private def s771 : Step := ⟨⟨⟨294,410,91,5420⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s772 : Step := ⟨⟨⟨294,410,91,6344⟩,790165454848,805457011⟩,5,by decide,by decide,by decide⟩
private def s773 : Step := ⟨⟨⟨350,488,106,6926⟩,1308168290304,1584729438⟩,7,by decide,by decide,by decide⟩
private def s774 : Step := ⟨⟨⟨420,586,130,7630⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s775 : Step := ⟨⟨⟨520,725,157,10987⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s776 : Step := ⟨⟨⟨630,878,190,11893⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s777 : Step := ⟨⟨⟨900,1255,279,15348⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s778 : Step := ⟨⟨⟨900,1255,272,15437⟩,22024701870080,68477558806⟩,31,by decide,by decide,by decide⟩
private def s779 : Step := ⟨⟨⟨1100,1534,332,22006⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s780 : Step := ⟨⟨⟨1650,2301,512,32552⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s781 : Step := ⟨⟨⟨1651,2301,512,35430⟩,138317479280640,787417379725⟩,76,by decide,by decide,by decide⟩
private def s782 : Step := ⟨⟨⟨2501,3487,775,39827⟩,480070068076544,4144013596741⟩,103,by decide,by decide,by decide⟩
private def s783 : Step := ⟨⟨⟨210,293,63,3473⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s784 : Step := ⟨⟨⟨251,349,78,3284⟩,494498480128,426627288⟩,1,by decide,by decide,by decide⟩
private def s785 : Step := ⟨⟨⟨251,349,74,4405⟩,475332608000,409695834⟩,2,by decide,by decide,by decide⟩
private def s786 : Step := ⟨⟨⟨250,348,76,4816⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s787 : Step := ⟨⟨⟨250,348,78,5899⟩,490108092416,422716393⟩,4,by decide,by decide,by decide⟩
private def s788 : Step := ⟨⟨⟨294,410,89,5459⟩,777085255680,791788817⟩,5,by decide,by decide,by decide⟩
private def s789 : Step := ⟨⟨⟨350,488,108,5524⟩,1326705278976,1607754763⟩,7,by decide,by decide,by decide⟩
private def s790 : Step := ⟨⟨⟨420,586,127,6613⟩,2252760678400,3279920952⟩,10,by decide,by decide,by decide⟩
private def s791 : Step := ⟨⟨⟨520,725,161,8574⟩,4343013310464,7809559934⟩,16,by decide,by decide,by decide⟩
private def s792 : Step := ⟨⟨⟨630,878,190,9859⟩,7559493713920,16431687757⟩,20,by decide,by decide,by decide⟩
private def s793 : Step := ⟨⟨⟨751,1046,232,16707⟩,13024603668480,33687112323⟩,32,by decide,by decide,by decide⟩
private def s794 : Step := ⟨⟨⟨900,1255,279,12222⟩,22452680785920,69841856233⟩,31,by decide,by decide,by decide⟩
private def s795 : Step := ⟨⟨⟨1100,1534,341,17120⟩,40955142733824,155702293064⟩,44,by decide,by decide,by decide⟩
private def s796 : Step := ⟨⟨⟨1650,2301,498,28799⟩,135254251667456,770619519922⟩,73,by decide,by decide,by decide⟩
private def s797 : Step := ⟨⟨⟨1651,2301,512,29189⟩,138317479280640,787417379725⟩,76,by decide,by decide,by decide⟩
private def s798 : Step := ⟨⟨⟨2501,3487,755,35002⟩,470631526170624,4060530796561⟩,103,by decide,by decide,by decide⟩
private def s799 : Step := ⟨⟨⟨210,293,63,2586⟩,283090354176,206678784⟩,0,by decide,by decide,by decide⟩
private def s800 : Step := ⟨⟨⟨210,293,65,2985⟩,289785774080,211692234⟩,1,by decide,by decide,by decide⟩
private def s801 : Step := ⟨⟨⟨251,349,76,2956⟩,484966924288,418199213⟩,2,by decide,by decide,by decide⟩
private def s802 : Step := ⟨⟨⟨250,348,76,3501⟩,480667500544,414368386⟩,3,by decide,by decide,by decide⟩
private def s803 : Step := ⟨⟨⟨294,410,91,3356⟩,790165454848,805457011⟩,4,by decide,by decide,by decide⟩
private def s804 : Step := ⟨⟨⟨294,410,91,3835⟩,790165454848,805457011⟩,5,by decide,by decide,by decide⟩
private def s805 : Step := ⟨⟨⟨350,488,106,4263⟩,1308168290304,1584729438⟩,7,by decide,by decide,by decide⟩
private def s806 : Step := ⟨⟨⟨420,586,130,4742⟩,2292767784960,3339653140⟩,10,by decide,by decide,by decide⟩
private def s807 : Step := ⟨⟨⟨520,725,157,6703⟩,4261264752640,7658911630⟩,16,by decide,by decide,by decide⟩
private def s808 : Step := ⟨⟨⟨520,725,161,9337⟩,4343013310464,7809559934⟩,20,by decide,by decide,by decide⟩
private def s809 : Step := ⟨⟨⟨900,1255,279,9625⟩,22452680785920,69841856233⟩,32,by decide,by decide,by decide⟩
private def s810 : Step := ⟨⟨⟨751,1046,232,11114⟩,13024603668480,33687112323⟩,31,by decide,by decide,by decide⟩
private def s811 : Step := ⟨⟨⟨1100,1534,332,13546⟩,40133103452160,152499774767⟩,44,by decide,by decide,by decide⟩
private def s812 : Step := ⟨⟨⟨1650,2301,512,19948⟩,138129879859200,787417379725⟩,73,by decide,by decide,by decide⟩
private def s813 : Step := ⟨⟨⟨1651,2301,512,21413⟩,138317479280640,787417379725⟩,76,by decide,by decide,by decide⟩
private def s814 : Step := ⟨⟨⟨2000,2788,620,32224⟩,245690786119680,1695265997069⟩,103,by decide,by decide,by decide⟩
private def s815 : Step := ⟨⟨⟨190,264,57,2331⟩,210162155520,137081511⟩,0,by decide,by decide,by decide⟩
private def s816 : Step := ⟨⟨⟨200,278,61,2610⟩,247865278464,170383811⟩,1,by decide,by decide,by decide⟩
private def s817 : Step := ⟨⟨⟨211,293,65,2957⟩,292874092544,211692234⟩,2,by decide,by decide,by decide⟩
private def s818 : Step := ⟨⟨⟨226,313,70,3251⟩,360816574464,276897427⟩,3,by decide,by decide,by decide⟩
private def s819 : Step := ⟨⟨⟨249,346,76,3403⟩,476388261888,406778496⟩,4,by decide,by decide,by decide⟩
private def s820 : Step := ⟨⟨⟨268,372,83,3503⟩,599698964480,549189173⟩,5,by decide,by decide,by decide⟩
private def s821 : Step := ⟨⟨⟨295,409,91,4201⟩,796182708224,799166465⟩,7,by decide,by decide,by decide⟩
private def s822 : Step := ⟨⟨⟨351,487,108,4801⟩,1335191666688,1597195933⟩,10,by decide,by decide,by decide⟩
private def s823 : Step := ⟨⟨⟨469,652,145,5863⟩,3186037882880,5120467320⟩,16,by decide,by decide,by decide⟩
private def s824 : Step := ⟨⟨⟨568,790,173,6523⟩,5586192957440,10881173726⟩,20,by decide,by decide,by decide⟩
private def s825 : Step := ⟨⟨⟨752,1046,232,9513⟩,13063450263552,33687112323⟩,32,by decide,by decide,by decide⟩
private def s826 : Step := ⟨⟨⟨714,994,217,10260⟩,11059077578752,27147283132⟩,31,by decide,by decide,by decide⟩
private def s827 : Step := ⟨⟨⟨965,1343,297,12305⟩,27516996157440,91177576164⟩,44,by decide,by decide,by decide⟩
private def s828 : Step := ⟨⟨⟨1487,2071,459,18701⟩,100733524377600,515343711922⟩,73,by decide,by decide,by decide⟩
private def s829 : Step := ⟨⟨⟨1487,2071,450,21254⟩,99231184453632,507469008976⟩,75,by decide,by decide,by decide⟩
private def s830 : Step := ⟨⟨⟨2000,2786,606,27410⟩,241468805218304,1661570923447⟩,103,by decide,by decide,by decide⟩
private def s831 : Step := ⟨⟨⟨162,225,50,2001⟩,133622136832,74338421⟩,0,by decide,by decide,by decide⟩
private def s832 : Step := ⟨⟨⟨171,237,53,2427⟩,157407510528,91783289⟩,1,by decide,by decide,by decide⟩
private def s833 : Step := ⟨⟨⟨190,264,59,2489⟩,215642275840,140746391⟩,2,by decide,by decide,by decide⟩
private def s834 : Step := ⟨⟨⟨211,293,65,2547⟩,292874092544,211692234⟩,3,by decide,by decide,by decide⟩
private def s835 : Step := ⟨⟨⟨225,313,68,2945⟩,349597597696,270809095⟩,4,by decide,by decide,by decide⟩
private def s836 : Step := ⟨⟨⟨239,331,74,3014⟩,426141286400,345715284⟩,5,by decide,by decide,by decide⟩
private def s837 : Step := ⟨⟨⟨266,369,80,3881⟩,573684056064,520167980⟩,7,by decide,by decide,by decide⟩
private def s838 : Step := ⟨⟨⟨316,439,97,4088⟩,973976371200,1053621943⟩,10,by decide,by decide,by decide⟩
private def s839 : Step := ⟨⟨⟨400,556,123,5652⟩,1971918995456,2702734485⟩,16,by decide,by decide,by decide⟩
private def s840 : Step := ⟨⟨⟨469,652,145,6114⟩,3186037882880,5120467320⟩,20,by decide,by decide,by decide⟩
private def s841 : Step := ⟨⟨⟨676,941,205,8426⟩,9373527834624,21779095054⟩,32,by decide,by decide,by decide⟩
private def s842 : Step := ⟨⟨⟨630,876,195,8662⟩,7709474160640,16643367896⟩,31,by decide,by decide,by decide⟩
private def s843 : Step := ⟨⟨⟨856,1192,260,11124⟩,19026984566784,56025541488⟩,44,by decide,by decide,by decide⟩
private def s844 : Step := ⟨⟨⟨1284,1788,397,17111⟩,64968196882432,286903982624⟩,73,by decide,by decide,by decide⟩
private def s845 : Step := ⟨⟨⟨1351,1881,410,18051⟩,74602437935104,346324061737⟩,76,by decide,by decide,by decide⟩
private def s846 : Step := ⟨⟨⟨1801,2509,556,21794⟩,178890913087488,1109248738030⟩,103,by decide,by decide,by decide⟩
private def r0 : Route := ⟨2,1,![s0,s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16],by decide,rfl,by intro k; fin_cases k <;> decide,![16,14],![147,8125],by intro k; fin_cases k <;> decide,by decide⟩
private def r1 : Route := ⟨2,3,![s17,s18,s19,s20,s21,s22,s23,s24,s25,s26,s27,s28,s29,s30,s31,s32,s33],by decide,rfl,by intro k; fin_cases k <;> decide,![16,13],![140,7498],by intro k; fin_cases k <;> decide,by decide⟩
private def r2 : Route := ⟨2,8,![s34,s35,s36,s37,s38,s39,s40,s41,s42,s43,s44,s45,s46,s47,s48,s49,s50],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![140,7296],by intro k; fin_cases k <;> decide,by decide⟩
private def r3 : Route := ⟨2,15,![s51,s52,s53,s54,s55,s56,s57,s58,s59,s60,s61,s62,s63,s64,s65,s66,s67],by decide,rfl,by intro k; fin_cases k <;> decide,![16,13],![130,5762],by intro k; fin_cases k <;> decide,by decide⟩
private def r4 : Route := ⟨2,25,![s68,s69,s70,s71,s72,s73,s74,s75,s76,s75,s77,s78,s79,s80,s81,s82,s83],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![157,3724],by intro k; fin_cases k <;> decide,by decide⟩
private def r5 : Route := ⟨2,40,![s84,s85,s86,s87,s88,s89,s90,s91,s92,s91,s93,s94,s95,s96,s96,s96,s96],by decide,rfl,by intro k; fin_cases k <;> decide,![13,13],![127,2038],by intro k; fin_cases k <;> decide,by decide⟩
private def r6 : Route := ⟨2,50,![s97,s98,s99,s100,s101,s102,s103,s104,s105,s104,s106,s107,s108,s109,s110,s111,s112],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![57,877],by intro k; fin_cases k <;> decide,by decide⟩
private def r7 : Route := ⟨2,70,![s113,s114,s115,s116,s117,s118,s119,s120,s121,s120,s122,s123,s124,s125,s126,s127,s128],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![44,860],by intro k; fin_cases k <;> decide,by decide⟩
private def r8 : Route := ⟨2,92,![s129,s130,s131,s132,s133,s134,s135,s136,s137,s136,s138,s139,s139,s140,s141,s142,s143],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![33,801],by intro k; fin_cases k <;> decide,by decide⟩
private def r9 : Route := ⟨3,1,![s144,s145,s146,s147,s148,s149,s150,s151,s152,s151,s153,s154,s154,s155,s155,s155,s155],by decide,rfl,by intro k; fin_cases k <;> decide,![13,13],![149,4279],by intro k; fin_cases k <;> decide,by decide⟩
private def r10 : Route := ⟨3,3,![s156,s157,s158,s159,s160,s161,s162,s163,s164,s163,s165,s166,s167,s168,s168,s168,s168],by decide,rfl,by intro k; fin_cases k <;> decide,![13,11],![148,4114],by intro k; fin_cases k <;> decide,by decide⟩
private def r11 : Route := ⟨3,8,![s169,s170,s171,s172,s173,s174,s175,s176,s177,s176,s178,s179,s180,s181,s181,s181,s181],by decide,rfl,by intro k; fin_cases k <;> decide,![13,12],![149,3916],by intro k; fin_cases k <;> decide,by decide⟩
private def r12 : Route := ⟨3,15,![s182,s183,s184,s185,s186,s187,s188,s189,s190,s189,s191,s192,s193,s194,s194,s194,s194],by decide,rfl,by intro k; fin_cases k <;> decide,![12,13],![142,3265],by intro k; fin_cases k <;> decide,by decide⟩
private def r13 : Route := ⟨3,25,![s195,s196,s197,s198,s199,s200,s201,s202,s203,s202,s204,s205,s206,s207,s207,s207,s207],by decide,rfl,by intro k; fin_cases k <;> decide,![13,13],![133,2507],by intro k; fin_cases k <;> decide,by decide⟩
private def r14 : Route := ⟨3,40,![s208,s209,s210,s211,s212,s213,s214,s215,s216,s215,s217,s218,s219,s220,s221,s222,s223],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![95,1456],by intro k; fin_cases k <;> decide,by decide⟩
private def r15 : Route := ⟨3,50,![s224,s225,s226,s227,s228,s229,s230,s231,s232,s231,s233,s234,s235,s236,s237,s238,s239],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![62,815],by intro k; fin_cases k <;> decide,by decide⟩
private def r16 : Route := ⟨3,70,![s240,s241,s242,s243,s244,s245,s246,s247,s248,s247,s249,s250,s251,s252,s253,s254,s255],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![49,819],by intro k; fin_cases k <;> decide,by decide⟩
private def r17 : Route := ⟨3,92,![s256,s257,s258,s259,s260,s261,s262,s263,s264,s263,s265,s266,s267,s268,s269,s270,s271],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![38,774],by intro k; fin_cases k <;> decide,by decide⟩
private def r18 : Route := ⟨4,1,![s272,s273,s274,s275,s276,s277,s278,s279,s280,s279,s281,s282,s282,s283,s284,s285,s286],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![107,1749],by intro k; fin_cases k <;> decide,by decide⟩
private def r19 : Route := ⟨4,3,![s287,s288,s289,s290,s291,s292,s293,s294,s295,s294,s296,s297,s298,s299,s300,s301,s302],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![108,1695],by intro k; fin_cases k <;> decide,by decide⟩
private def r20 : Route := ⟨4,8,![s303,s304,s305,s306,s307,s308,s309,s310,s311,s310,s312,s313,s314,s315,s316,s317,s318],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![107,1687],by intro k; fin_cases k <;> decide,by decide⟩
private def r21 : Route := ⟨4,15,![s319,s320,s321,s322,s323,s324,s325,s326,s327,s326,s328,s329,s330,s331,s332,s333,s334],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![99,1487],by intro k; fin_cases k <;> decide,by decide⟩
private def r22 : Route := ⟨4,25,![s335,s336,s337,s338,s339,s340,s341,s342,s343,s342,s344,s345,s346,s347,s348,s349,s350],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![98,1277],by intro k; fin_cases k <;> decide,by decide⟩
private def r23 : Route := ⟨4,40,![s351,s352,s353,s354,s355,s356,s357,s358,s359,s358,s360,s361,s362,s363,s364,s365,s366],by decide,rfl,by intro k; fin_cases k <;> decide,![16,14],![84,1074],by intro k; fin_cases k <;> decide,by decide⟩
private def r24 : Route := ⟨4,50,![s367,s368,s369,s370,s371,s372,s373,s374,s375,s374,s376,s377,s378,s379,s380,s381,s382],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![64,752],by intro k; fin_cases k <;> decide,by decide⟩
private def r25 : Route := ⟨4,70,![s383,s384,s385,s386,s387,s388,s389,s390,s391,s390,s392,s393,s394,s395,s396,s397,s398],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![55,783],by intro k; fin_cases k <;> decide,by decide⟩
private def r26 : Route := ⟨4,92,![s399,s400,s401,s402,s403,s404,s405,s406,s407,s406,s408,s409,s410,s411,s412,s413,s414],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![43,758],by intro k; fin_cases k <;> decide,by decide⟩
private def r27 : Route := ⟨5,1,![s415,s416,s417,s418,s419,s420,s421,s422,s423,s422,s424,s425,s426,s427,s428,s429,s430],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![87,962],by intro k; fin_cases k <;> decide,by decide⟩
private def r28 : Route := ⟨5,3,![s431,s432,s433,s434,s435,s436,s437,s438,s439,s438,s440,s441,s442,s443,s444,s445,s446],by decide,rfl,by intro k; fin_cases k <;> decide,![13,15],![79,996],by intro k; fin_cases k <;> decide,by decide⟩
private def r29 : Route := ⟨5,8,![s447,s448,s449,s450,s451,s452,s453,s454,s455,s454,s456,s457,s458,s459,s460,s461,s462],by decide,rfl,by intro k; fin_cases k <;> decide,![15,14],![85,974],by intro k; fin_cases k <;> decide,by decide⟩
private def r30 : Route := ⟨5,15,![s463,s464,s465,s466,s467,s468,s469,s470,s471,s470,s472,s473,s474,s475,s476,s477,s478],by decide,rfl,by intro k; fin_cases k <;> decide,![16,15],![83,959],by intro k; fin_cases k <;> decide,by decide⟩
private def r31 : Route := ⟨5,25,![s479,s480,s481,s482,s483,s484,s485,s486,s487,s486,s488,s489,s490,s491,s492,s493,s494],by decide,rfl,by intro k; fin_cases k <;> decide,![15,14],![81,903],by intro k; fin_cases k <;> decide,by decide⟩
private def r32 : Route := ⟨5,40,![s495,s496,s497,s498,s499,s500,s501,s502,s503,s502,s504,s505,s506,s507,s508,s509,s510],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![78,848],by intro k; fin_cases k <;> decide,by decide⟩
private def r33 : Route := ⟨5,50,![s511,s512,s513,s514,s515,s516,s517,s518,s519,s518,s520,s521,s522,s523,s524,s525,s526],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![64,696],by intro k; fin_cases k <;> decide,by decide⟩
private def r34 : Route := ⟨5,70,![s527,s528,s529,s530,s531,s532,s533,s534,s535,s534,s536,s537,s538,s539,s540,s541,s542],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![57,737],by intro k; fin_cases k <;> decide,by decide⟩
private def r35 : Route := ⟨5,92,![s543,s544,s545,s546,s547,s548,s549,s550,s551,s550,s552,s553,s554,s555,s556,s557,s558],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![50,747],by intro k; fin_cases k <;> decide,by decide⟩
private def r36 : Route := ⟨6,1,![s559,s560,s561,s562,s563,s564,s565,s566,s567,s566,s568,s569,s570,s571,s572,s573,s574],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,618],by intro k; fin_cases k <;> decide,by decide⟩
private def r37 : Route := ⟨6,3,![s575,s576,s577,s578,s579,s580,s581,s582,s583,s582,s584,s585,s586,s587,s588,s589,s590],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,649],by intro k; fin_cases k <;> decide,by decide⟩
private def r38 : Route := ⟨6,8,![s591,s592,s593,s594,s595,s596,s597,s598,s599,s598,s600,s601,s602,s603,s604,s605,s606],by decide,rfl,by intro k; fin_cases k <;> decide,![15,14],![76,677],by intro k; fin_cases k <;> decide,by decide⟩
private def r39 : Route := ⟨6,15,![s607,s608,s609,s610,s611,s612,s613,s614,s615,s614,s616,s617,s618,s619,s620,s621,s622],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,670],by intro k; fin_cases k <;> decide,by decide⟩
private def r40 : Route := ⟨6,25,![s623,s624,s625,s626,s627,s628,s629,s630,s631,s630,s632,s633,s634,s635,s636,s637,s638],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![76,698],by intro k; fin_cases k <;> decide,by decide⟩
private def r41 : Route := ⟨6,40,![s639,s640,s641,s642,s643,s644,s645,s646,s647,s646,s648,s649,s650,s651,s652,s653,s654],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![74,713],by intro k; fin_cases k <;> decide,by decide⟩
private def r42 : Route := ⟨6,50,![s655,s656,s657,s658,s659,s660,s661,s662,s663,s662,s664,s665,s666,s667,s668,s669,s670],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![63,642],by intro k; fin_cases k <;> decide,by decide⟩
private def r43 : Route := ⟨6,70,![s671,s672,s673,s674,s675,s676,s677,s678,s679,s678,s680,s681,s682,s683,s684,s685,s686],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![60,699],by intro k; fin_cases k <;> decide,by decide⟩
private def r44 : Route := ⟨6,92,![s687,s688,s689,s690,s691,s692,s693,s694,s695,s694,s696,s697,s698,s699,s700,s701,s702],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![51,726],by intro k; fin_cases k <;> decide,by decide⟩
private def r45 : Route := ⟨7,1,![s703,s704,s705,s706,s707,s708,s709,s710,s711,s710,s712,s713,s714,s715,s716,s717,s718],by decide,rfl,by intro k; fin_cases k <;> decide,![13,16],![70,498],by intro k; fin_cases k <;> decide,by decide⟩
private def r46 : Route := ⟨7,3,![s719,s720,s721,s722,s723,s724,s725,s726,s727,s726,s728,s729,s730,s731,s732,s733,s734],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![72,506],by intro k; fin_cases k <;> decide,by decide⟩
private def r47 : Route := ⟨7,8,![s735,s736,s737,s738,s739,s740,s741,s742,s743,s742,s744,s745,s746,s747,s748,s749,s750],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![75,514],by intro k; fin_cases k <;> decide,by decide⟩
private def r48 : Route := ⟨7,15,![s751,s752,s753,s754,s755,s756,s757,s758,s759,s758,s760,s761,s762,s763,s764,s765,s766],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![72,543],by intro k; fin_cases k <;> decide,by decide⟩
private def r49 : Route := ⟨7,25,![s767,s768,s769,s770,s771,s772,s773,s774,s775,s774,s776,s777,s778,s779,s780,s781,s782],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![69,569],by intro k; fin_cases k <;> decide,by decide⟩
private def r50 : Route := ⟨7,40,![s783,s784,s785,s786,s787,s788,s789,s790,s791,s790,s792,s793,s794,s795,s796,s797,s798],by decide,rfl,by intro k; fin_cases k <;> decide,![15,16],![69,626],by intro k; fin_cases k <;> decide,by decide⟩
private def r51 : Route := ⟨7,50,![s799,s800,s801,s802,s803,s804,s805,s806,s807,s806,s808,s809,s810,s811,s812,s813,s814],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![62,607],by intro k; fin_cases k <;> decide,by decide⟩
private def r52 : Route := ⟨7,70,![s815,s816,s817,s818,s819,s820,s821,s822,s823,s822,s824,s825,s826,s827,s828,s829,s830],by decide,rfl,by intro k; fin_cases k <;> decide,![16,16],![61,671],by intro k; fin_cases k <;> decide,by decide⟩
private def r53 : Route := ⟨7,92,![s831,s832,s833,s834,s835,s836,s837,s838,s839,s838,s840,s841,s842,s843,s844,s845,s846],by decide,rfl,by intro k; fin_cases k <;> decide,![14,16],![56,701],by intro k; fin_cases k <;> decide,by decide⟩

def data : Fin 54 → Route := ![r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53]

def bank (r:Fin 54) (i:Fin 17) := ((data r).stages i).source
def reserve (r:Fin 54) (i:Fin 17) := ((data r).stages i).order
def jetCap (r:Fin 54) := (data r).degree
def seedCap (r:Fin 54) := (data r).upper
def cutoff (h:ℕ) (r:Fin 54) (i:Fin 17) := (bank r i).shape.m*179759-2*h*reserve r i-1
theorem shape_guards (r:Fin 54) (i:Fin 17) : 0<(bank r i).shape.J ∧ (bank r i).shape.J≤(bank r i).shape.B ∧ (bank r i).shape.B<K1.p ∧ (bank r i).shape.U<K1.p ∧ (bank r i).shape.m*179759<K1.p := ((data r).stages i).safe
theorem cutoff_fit {h:ℕ} (hi:h≤2522) (r:Fin 54) (i:Fin 17) :
    cutoff h r i+2*h*reserve r i<(bank r i).shape.m*179759 := by
  have bound : 2*2522*reserve r i<(bank r i).shape.m*179759 := ((data r).stages i).room
  have small := Nat.mul_le_mul_right (reserve r i) (Nat.mul_le_mul_left 2 hi)
  unfold cutoff
  omega
end Lower6960.Rescue6966Source

end Merged6967_High6966RescueData

section Merged6967_Low6966ActiveCyclePrice
set_option Elab.async false






set_option Elab.async false





-- merged module R6960Low6966ActiveCyclePrice
section Merged_R6960Low6966ActiveCyclePrice

set_option autoImplicit false
set_option Elab.async false

namespace Low6966ActiveCycle
noncomputable section

open Low48BentLattice (Cap Chamber Scale latticePoints)
open Low49ActiveLattice (Fits points)
open K1_13 (Shape)
open K1_13_6 (GeoField)
open K1_13_6_2_4_1 (Grade Form unitGrade positiveDiagonal positiveDiagonal_apply
  cube_extract line_coeff squarefree squarefree_apply)
open Low48BentCycle (Family capFamily capSum ambient_cap integral mixedDegree diagonalExponents
  diagonal_nsmul diagonal_add)
open MvPolynomial
open scoped BigOperators Pointwise

open Low48BentCycle (diagonal_unit grade_sum diagonal_sum coeff_congr)
open Low48BentCycle (ambient_list)
open Low49ActiveVolume (fits_scale point_scale point_zero)

private def integr (a : Cap) : ℚ := integral a

private def signed (p : Shape) : ℤ :=
  ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℤ) ^ (5 - J.card) *
    integral (Low48BentLattice.Sum J (caps p))

private theorem base_signed (p : Shape) :
    Low6966Prices.tiltedSurface p Low6966Prices.primaryBox = (signed p).toNat := by
  change Low48Price.ambientMix (slots.map (caps p)) = _
  exact ambient_list (caps p)

private theorem base_normalize (p : Shape) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (capSum (caps p) (positiveDiagonal J))) = (signed p : ℚ) := by
  have H := Low48BentPolarization.remove_baseline (caps p)
  change _ = _ at H
  rw [show (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      integr (capSum (caps p) (positiveDiagonal J))) =
      ∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        integr (Low48BentLattice.Sum J (caps p)) from H]
  unfold signed
  push_cast
  rfl

private theorem ordinary_coeff (a : Cap) (ha : Chamber a) :
    (affineHilbertPolynomial (Ideal.comap
      (monomialMap GeoField (latticePoints a)).toRingHom ⊥)).coeff 5 = integr a / 60 := by
  rw [Low48BentVolume.ambient_coeff a ha]
  unfold integr integral
  rw [Low48BentVolume.cast_price_integral a]

theorem ordinary_budget {p : Shape} (h : ∀ i, Chamber (caps p i)) :
    (60 * 32 : ℚ) * mixedDegree (capFamily (caps p)) ⊥ Finset.univ ≤
      (Low6966Prices.tiltedSurface p Low6966Prices.primaryBox : ℚ) := by
  rw [mul_assoc, ambient_cap (caps p) h (fun a => integr a / 60) ordinary_coeff]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0),
    base_normalize, base_signed]
  exact_mod_cast (show signed p ≤ ((signed p).toNat : ℤ) by omega)

private theorem fits_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s, Fits (a i) (c i)) :
    Fits (Low48BentLattice.Sum s a) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [Fits, Low48BentLattice.Sum]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hs := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hm := Low49ActiveLattice.fits_add (h i (Finset.mem_insert_self _ _)) hs
    simpa only [Low48BentLattice.Sum, Finset.sum_insert hi, Low48BentLattice.Add, Shape.plus] using hm

private theorem points_sum (s : Finset (Fin 5)) (a : Fin 5 → Cap) (c : Fin 5 → ℕ)
    (h : ∀ i ∈ s, Fits (a i) (c i)) :
    (∑ i ∈ s, points (a i) (c i)) = points (Low48BentLattice.Sum s a) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Low48BentLattice.Sum] using point_zero.symm
  | insert i s hi ih =>
    have hs (j : Fin 5) (hj : j ∈ s) := h j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ih hs,
      Low49ActiveLattice.add (h i (Finset.mem_insert_self _ _)) (fits_sum s a c hs)]
    simp only [Low48BentLattice.Sum, Low48BentLattice.Add, Finset.sum_insert hi, Shape.plus]

private def clipSum (p : Shape) (K : ℕ) (t : Grade) : ℕ := ∑ i, t i * clips p K i

private theorem active_diagonal {p : Shape} {K : ℕ} (t : Grade)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    diagonalExponents (activeFamily p K) t = points (capSum (caps p) t) (clipSum p K t) := by
  have h0 := (active_doubled h).double_zero
  calc
    _ = ∑ i : Fin 5, diagonalExponents (activeFamily p K) (t i • unitGrade i) := by
      conv_lhs => rw [← grade_sum t]
      exact diagonal_sum _ _ _
    _ = ∑ i : Fin 5, points (Scale (t i) (caps p i)) (t i * clips p K i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [diagonal_nsmul, diagonal_unit _ h0]
      exact point_scale _ _ (h i) _
    _ = _ := points_sum _ _ _ (fun i _ => fits_scale (h i) _)

private theorem fifth_difference (v : Fin 5 → ℚ) :
    (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
      (∑ i, (positiveDiagonal J i : ℚ) * v i)^5) = 120 * ∏ i, v i := by
  let f : Form := (∑ i : Fin 5, C (v i) * MvPolynomial.X i)^5
  have hlin : (∑ i : Fin 5, (C (v i) * MvPolynomial.X i : Form)).IsHomogeneous 1 := by
    change _ ∈ homogeneousSubmodule (Fin 5) ℚ 1
    apply Submodule.sum_mem
    intro i _
    exact (isHomogeneous_X ℚ i).C_mul _
  have hf : f.IsHomogeneous 5 := by
    simpa only [Nat.mul_one] using hlin.pow 5
  have hsum := cube_extract (Finset.univ : Finset (Fin 5)) f
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  simp_rw [line_coeff, homogeneousComponent_eq_self hf] at hsum
  have he (J : Finset (Fin 5)) :
      eval (fun i => (positiveDiagonal J i : ℚ)) f = (∑ i, (positiveDiagonal J i : ℚ) * v i)^5 := by
    simp [f, mul_comm]
  simp_rw [he] at hsum
  rw [hsum]
  unfold f
  simp only [← smul_eq_C_mul]
  rw [coeff_linearCombination_X_pow_of_fintype]
  have hu (i : Fin 5) : squarefree Finset.univ i = 1 := by simp [squarefree_apply]
  have hd : (squarefree (Finset.univ : Finset (Fin 5))).degree = 5 := by
    simp [K1_13_6_2_4_1.squarefree_degree]
  have hh : (squarefree (Finset.univ : Finset (Fin 5))).support = Finset.univ := by
    ext i
    simp [Finsupp.mem_support_iff, hu]
  have hsum' : (squarefree (Finset.univ : Finset (Fin 5))).sum (fun _ m => m) = 5 := hd
  simp [hsum', Finsupp.multinomial_eq, Finsupp.prod, hh, hu, Nat.multinomial,
    Finset.sum_const, Nat.factorial]

private theorem clips_prod (p : Shape) (K : ℕ) (ht : 3 ≤ p.t)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    (Low6966Prices.activeLoss (Low6966Prices.activeClips p K) : ℚ) =
      480 * ((∏ i, (clips p K i : ℚ)) -
        (∏ i, ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ)))) := by
  rw [← clip_list p K ht]
  unfold Low6966Prices.activeLoss
  have hi (i : Fin 5) : 2 * (caps p i).2 ≤ clips p K i := (h i).2.2.2.2.1
  have hle : (∏ i, (clips p K i - 2 * (caps p i).2)) ≤ ∏ i, clips p K i :=
    Finset.prod_le_prod fun _ _ => Nat.sub_le _ _
  have hp (a : Fin 5 → ℕ) : (slots.map a).prod = ∏ i, a i := by
    rw [← List.prod_toFinset a (show slots.Nodup by decide)]
    rw [show slots.toFinset = Finset.univ by decide]
  simp only [List.map_map, Function.comp_apply, hp]
  rw [Nat.cast_mul, Nat.cast_sub hle]
  push_cast [Nat.cast_sub, hi]
  norm_num

theorem active_budget {p : Shape} {K : ℕ} (ht : 3 ≤ p.t)
    (h : ∀ i, Fits (caps p i) (clips p K i)) :
    (60 * 32 : ℚ) * mixedDegree (activeFamily p K) ⊥ Finset.univ ≤
      (Low6966Prices.tiltedSurfaceActive p Low6966Prices.primaryBox K : ℚ) := by
  classical
  have hcoeff (J : Finset (Fin 5)) :
      (affineHilbertPolynomial (Ideal.comap
        (monomialMap GeoField (diagonalExponents (activeFamily p K) (positiveDiagonal J))) ⊥)).coeff 5 =
      (integr (capSum (caps p) (positiveDiagonal J)) -
        4 * ((clipSum p K (positiveDiagonal J) : ℚ)^5 -
          ((clipSum p K (positiveDiagonal J) : ℚ) -
            2 * ((capSum (caps p) (positiveDiagonal J)).2 : ℚ))^5)) / 60 := by
    rw [coeff_congr _ _ (active_diagonal _ h)]
    have hs := fits_sum Finset.univ (fun i => Scale (positiveDiagonal J i) (caps p i))
      (fun i => positiveDiagonal J i * clips p K i) (fun i _ => fits_scale (h i) _)
    let a := capSum (caps p) (positiveDiagonal J)
    let c := clipSum p K (positiveDiagonal J)
    change (affineHilbertPolynomial ((⊥ : Ideal K1_13_6_2.GeoJets5).comap
      (monomialMap GeoField (points a c)).toRingHom)).coeff 5 = _
    rw [Low49ActiveVolume.ambient_coeff a c hs]
    unfold integr integral
    rw [Low48BentVolume.cast_price_integral a]
  have hc (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) = ∑ i, (positiveDiagonal J i : ℚ) * clips p K i := by
    unfold clipSum
    push_cast
    rfl
  have hcd (J : Finset (Fin 5)) :
      (clipSum p K (positiveDiagonal J) : ℚ) -
          2 * ((capSum (caps p) (positiveDiagonal J)).2 : ℚ) =
        ∑ i, (positiveDiagonal J i : ℚ) * ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ)) := by
    rw [hc]
    simp only [capSum, Low48BentLattice.Sum, Scale, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum,
      Finset.sum_sub_distrib, mul_sub]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold mixedDegree
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show (2 : ℚ)^5 = 32 by norm_num, mul_assoc, ← mul_div_assoc (32 : ℚ),
    mul_div_cancel_left₀ _ (by norm_num : (32 : ℚ) ≠ 0)]
  simp_rw [hcoeff, ← mul_div_assoc]
  rw [← Finset.sum_div, ← mul_div_assoc, mul_div_cancel_left₀ _ (by norm_num : (60 : ℚ) ≠ 0)]
  have hsum_rearr (A C D : Finset (Fin 5) → ℚ) :
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) *
        (A J - 4 * (C J - D J))) =
      (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * A J) -
        4 * ((∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * C J) -
          (∑ J ∈ (Finset.univ : Finset (Fin 5)).powerset, (-1 : ℚ) ^ (5 - J.card) * D J)) := by
    simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro J _
    ring
  rw [hsum_rearr, base_normalize]
  simp_rw [hcd, hc]
  simp_rw [fifth_difference]
  rw [show 4 * (120 * (∏ i, (clips p K i : ℚ)) -
      120 * ∏ i, ((clips p K i : ℚ) - 2 * ((caps p i).2 : ℚ))) =
      (Low6966Prices.activeLoss (Low6966Prices.activeClips p K) : ℚ) by rw [clips_prod p K ht h]; ring]
  unfold Low6966Prices.tiltedSurfaceActive
  rw [base_signed]
  exact_mod_cast (show signed p - (Low6966Prices.activeLoss (Low6966Prices.activeClips p K) : ℤ) ≤
    (((signed p).toNat - Low6966Prices.activeLoss (Low6966Prices.activeClips p K) : ℕ) : ℤ) by omega)

end
end Low6966ActiveCycle

end Merged_R6960Low6966ActiveCyclePrice

end Merged6967_Low6966ActiveCyclePrice
