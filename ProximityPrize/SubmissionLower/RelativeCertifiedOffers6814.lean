import ProximityPrize.SubmissionLower.RelativeCertR9B66T3605To3684Fast
import ProximityPrize.SubmissionLower.RelativeCertR9B65T3656To3720Fast

/-! Checked count offers for every saved complete relative-interpolation record.
Numerical certificates are imported in two bounded parallel build lanes. -/
namespace ProximityPrize.SubmissionLower.RelativeCertifiedOffers6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
open RelativeCertificate6814 MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)

def offer (i : Fin 74) : Band := ![
  ⟨10,56,3902,3917,12314372801839158⟩,
  ⟨10,57,3839,3887,13001470909723472⟩,
  ⟨10,58,3778,3857,13815262346775253⟩,
  ⟨10,59,3720,3826,15142263455696441⟩,
  ⟨10,60,3663,3794,28071367303838939⟩,
  ⟨10,61,3607,3762,25623191491887557⟩,
  ⟨10,62,3553,3729,25429572464128480⟩,
  ⟨10,63,3501,3695,25818239135729719⟩,
  ⟨10,64,3450,3660,30852343176758710⟩,
  ⟨10,65,3365,3382,29942600766848928⟩,
  ⟨10,65,3401,3526,29120250030593851⟩,
  ⟨11,52,3910,3939,15557768288906582⟩,
  ⟨11,53,3843,3910,15920488015804283⟩,
  ⟨11,54,3777,3881,16579153454940115⟩,
  ⟨11,55,3714,3852,17203165831889032⟩,
  ⟨11,56,3653,3822,21365995913629089⟩,
  ⟨11,57,3594,3792,29852491993091276⟩,
  ⟨11,58,3593,3648,31497735569814201⟩,
  ⟨11,58,3649,3760,24048096188955155⟩,
  ⟨11,59,3481,3729,30802988920566145⟩,
  ⟨11,60,3427,3696,33521411871134215⟩,
  ⟨11,61,3342,3663,33078648536786900⟩,
  ⟨11,62,3291,3629,32519066574844031⟩,
  ⟨11,63,3243,3453,33242252433776975⟩,
  ⟨12,49,3885,3924,11380060537880462⟩,
  ⟨12,50,3814,3896,11887928042267056⟩,
  ⟨12,51,3746,3868,12456861955597707⟩,
  ⟨12,52,3680,3840,13454343594378053⟩,
  ⟨12,53,3616,3811,14309438150475707⟩,
  ⟨12,54,3554,3781,45250040799475385⟩,
  ⟨12,55,3569,3622,43635301424197579⟩,
  ⟨12,55,3623,3751,16595982557763940⟩,
  ⟨12,56,3579,3720,45323634816865846⟩,
  ⟨12,57,3562,3604,44327286260835128⟩,
  ⟨12,57,3605,3689,34129398216919554⟩,
  ⟨12,58,3294,3657,37250082627013846⟩,
  ⟨12,59,3242,3624,35744153477019664⟩,
  ⟨12,60,3192,3562,36513206755580898⟩,
  ⟨12,61,3143,3230,36906415880582464⟩,
  ⟨13,46,3891,3902,29834286854120794⟩,
  ⟨13,47,3816,3875,30250102705817801⟩,
  ⟨13,48,3743,3848,30263617675957735⟩,
  ⟨13,49,3673,3820,33595668368951999⟩,
  ⟨13,50,3606,3792,35521311516555975⟩,
  ⟨13,51,3540,3763,35942556125440015⟩,
  ⟨13,52,3477,3734,36220912882672232⟩,
  ⟨13,53,3561,3704,37490083844189941⟩,
  ⟨13,54,3429,3499,43529310385779473⟩,
  ⟨13,54,3500,3673,37547057277830775⟩,
  ⟨13,55,3269,3642,38264302020204984⟩,
  ⟨13,56,3215,3610,38998155752837401⟩,
  ⟨13,57,3162,3521,38189126221457976⟩,
  ⟨13,58,3111,3170,38681762068485816⟩,
  ⟨14,44,3847,3847,31401086485671265⟩,
  ⟨14,45,3769,3820,30916619969042350⟩,
  ⟨14,46,3694,3792,38417668916827212⟩,
  ⟨14,47,3622,3764,38868901089933472⟩,
  ⟨14,48,3552,3736,38930904320711343⟩,
  ⟨14,49,3486,3707,39776287235706232⟩,
  ⟨14,50,3420,3678,40036978180364100⟩,
  ⟨14,51,3326,3648,42696548203814196⟩,
  ⟨14,52,3267,3618,42465170915191208⟩,
  ⟨14,53,3210,3418,41280379768223620⟩,
  ⟨15,43,3743,3756,34235134238621216⟩,
  ⟨15,44,3665,3728,24686100989165518⟩,
  ⟨15,45,3591,3700,24797592955066327⟩,
  ⟨15,46,3519,3672,32050357149758057⟩,
  ⟨15,47,3450,3569,31668756403961290⟩,
  ⟨18,19,3871,3955,1359136408997686⟩,
  ⟨9,62,3819,3822,24778021202031104⟩,
  ⟨9,63,3763,3789,25653739537571487⟩,
  ⟨9,64,3709,3755,24348315935019910⟩,
  ⟨9,65,3656,3720,25575436343300081⟩,
  ⟨9,66,3605,3684,27171955951741397⟩] i

variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance : DecidableEq K := Classical.decEq K

theorem regular_count (i : Fin 74) {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T (offer i).R)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : (offer i).R≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤(offer i).B)
    (hT0 : (offer i).T0≤T) (hT1 : T≤(offer i).T1) (hnu : minimumWeight (offer i)≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun j => (selected gamma).eval (nodes j)=u0 j+gamma*u1 j)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤(offer i).count := by
  fin_cases i
  · exact RelativeCertR10B56T3902To3917Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B57T3839To3887Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B58T3778To3857Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B59T3720To3826Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B60T3663To3794Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B61T3607To3762Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B62T3553To3729Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B63T3501To3695Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B64T3450To3660Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B65T3365To3382Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR10B65T3401To3526Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B52T3910To3939Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B53T3843To3910Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B54T3777To3881Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B55T3714To3852Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B56T3653To3822Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B57T3594To3792Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B58T3593To3648Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B58T3649To3760Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B59T3481To3729Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B60T3427To3696Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B61T3342To3663Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B62T3291To3629Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR11B63T3243To3453Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B49T3885To3924Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B50T3814To3896Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B51T3746To3868Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B52T3680To3840Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B53T3616To3811Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B54T3554To3781Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B55T3569To3622Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B55T3623To3751Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B56T3579To3720Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B57T3562To3604Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B57T3605To3689Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B58T3294To3657Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B59T3242To3624Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B60T3192To3562Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR12B61T3143To3230Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B46T3891To3902Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B47T3816To3875Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B48T3743To3848Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B49T3673To3820Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B50T3606To3792Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B51T3540To3763Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B52T3477To3734Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B53T3561To3704Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B54T3429To3499Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B54T3500To3673Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B55T3269To3642Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B56T3215To3610Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B57T3162To3521Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR13B58T3111To3170Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B44T3847To3847Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B45T3769To3820Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B46T3694To3792Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B47T3622To3764Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B48T3552To3736Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B49T3486To3707Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B50T3420To3678Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B51T3326To3648Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B52T3267To3618Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR14B53T3210To3418Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR15B43T3743To3756Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR15B44T3665To3728Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR15B45T3591To3700Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR15B46T3519To3672Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR15B47T3450To3569Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR18B19T3871To3955Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR9B62T3819To3822Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR9B63T3763To3789Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR9B64T3709To3755Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR9B65T3656To3720Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno
  · exact RelativeCertR9B66T3605To3684Fast.regular_count K I F hbox hcode htotal hslope hB hT0 hT1 hnu
      nodes u0 u1 hcard selected Gamma hdegree hagreement hno

#print axioms regular_count
end
end ProximityPrize.SubmissionLower.RelativeCertifiedOffers6814
