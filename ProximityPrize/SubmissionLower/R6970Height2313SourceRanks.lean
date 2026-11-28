import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.Z6969FastTri
import ProximityPrize.SubmissionLower.Z6969Pack0591
import ProximityPrize.SubmissionLower.Z6969Pack0592
import ProximityPrize.SubmissionLower.Z6969Pack0593
import ProximityPrize.SubmissionLower.Z6969Pack0594
import ProximityPrize.SubmissionLower.Z6969Pack0595
import ProximityPrize.SubmissionLower.Z6969Pack0596
import ProximityPrize.SubmissionLower.Z6969Pack0597
import ProximityPrize.SubmissionLower.Z6969Pack0598
import ProximityPrize.SubmissionLower.Z6969Pack0599
import ProximityPrize.SubmissionLower.Z6969Pack0600
import ProximityPrize.SubmissionLower.Z6969Pack0601
import ProximityPrize.SubmissionLower.Z6969Pack0603
import ProximityPrize.SubmissionLower.Z6969Pack0604
import ProximityPrize.SubmissionLower.Z6969Pack0606
import ProximityPrize.SubmissionLower.Z6969Pack0607
import ProximityPrize.SubmissionLower.Z6969Pack0608
import ProximityPrize.SubmissionLower.Z6969Pack0609
import ProximityPrize.SubmissionLower.Z6969Pack0610
import ProximityPrize.SubmissionLower.Z6969Pack0611
import ProximityPrize.SubmissionLower.Z6969Pack0612
import ProximityPrize.SubmissionLower.Z6969Pack0613
import ProximityPrize.SubmissionLower.Z6969Pack0615
import ProximityPrize.SubmissionLower.Z6969Pack0616
import ProximityPrize.SubmissionLower.Z6969Pack0618
import ProximityPrize.SubmissionLower.Z6969Pack0619
import ProximityPrize.SubmissionLower.Z6969Pack0620
import ProximityPrize.SubmissionLower.Z6969Pack0621
import ProximityPrize.SubmissionLower.Z6969Pack0625
import ProximityPrize.SubmissionLower.Z6969Pack0626
import ProximityPrize.SubmissionLower.Z6969Pack0632
import ProximityPrize.SubmissionLower.Z6969Pack0643
import ProximityPrize.SubmissionLower.Z6969Pack0644
import ProximityPrize.SubmissionLower.Z6969Pack0645
import ProximityPrize.SubmissionLower.Z6969Pack0646
import ProximityPrize.SubmissionLower.Z6969Pack0647
import ProximityPrize.SubmissionLower.Z6969Pack0648
import ProximityPrize.SubmissionLower.Z6969Pack0649
import ProximityPrize.SubmissionLower.Z6969Pack0650
import ProximityPrize.SubmissionLower.Z6969Pack0652
import ProximityPrize.SubmissionLower.Z6969Pack0655
import ProximityPrize.SubmissionLower.Z6969Pack0666

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 0

namespace Research6970.Height2313.Physical

private theorem bank_checked (m b j u N P : ℕ)
    (jm : 2*j≤m) (mb : m+j≤b+1) (small : b<K1.p)
    (rows : 262144*P1_7_1_2.sixPerNode (m-2*j) j = 6*N)
    (pole : P1_7_1.groupedPoleMoment b j≤P) :
    P3_7_1.BankOK ⟨⟨m,b,j,u⟩,N,P⟩ := by
  let shape : K1_14.Shape := ⟨m,b,j,u⟩
  have actual := P1_7_1_2.six_nodeRows shape jm mb
  change 6*P1_7_1.nodeRows shape = 262144*P1_7_1_2.sixPerNode (m-2*j) j at actual
  rw [rows] at actual
  exact ⟨by change P1_7_1.nodeRows shape = N; omega, pole, small⟩

private theorem pole_2930_632 :
    P1_7_1.groupedPoleMoment 2930 632 ≤ 2019119590628 :=
  Research6969.PackedRanks.PackedRanks252To254.moment2930_632

private theorem pole_3201_702 :
    P1_7_1.groupedPoleMoment 3201 702 ≤ 2912992731804 :=
  Research6969.PackedRanks.TerminalRanks20To23.moment3201_702

private theorem pole_3203_724 :
    P1_7_1.groupedPoleMoment 3203 724 ≤ 2989680899568 :=
  Research6969.PackedRanks.TerminalRanks24To27.moment3203_724

private theorem pole_3204_702 :
    P1_7_1.groupedPoleMoment 3204 702 ≤ 2921790084349 :=
  Research6969.PackedRanks.TerminalRanks24To27.moment3204_702

private theorem pole_3204_724 :
    P1_7_1.groupedPoleMoment 3204 724 ≤ 2992689220368 :=
  Research6969.PackedRanks.TerminalRanks24To27.moment3204_724

private theorem pole_3206_702 :
    P1_7_1.groupedPoleMoment 3206 702 ≤ 2927665016684 :=
  Research6969.PackedRanks.TerminalRanks28To31.moment3206_702

private theorem pole_3206_724 :
    P1_7_1.groupedPoleMoment 3206 724 ≤ 2998712046218 :=
  Research6969.PackedRanks.TerminalRanks28To31.moment3206_724

private theorem pole_3207_702 :
    P1_7_1.groupedPoleMoment 3207 702 ≤ 2930605494152 :=
  Research6969.PackedRanks.TerminalRanks28To31.moment3207_702

private theorem pole_3207_724 :
    P1_7_1.groupedPoleMoment 3207 724 ≤ 3001726552718 :=
  Research6969.PackedRanks.TerminalRanks32To35.moment3207_724

private theorem pole_3208_702 :
    P1_7_1.groupedPoleMoment 3208 702 ≤ 2933547980091 :=
  Research6969.PackedRanks.TerminalRanks32To35.moment3208_702

private theorem pole_3208_724 :
    P1_7_1.groupedPoleMoment 3208 724 ≤ 3004743122568 :=
  Research6969.PackedRanks.TerminalRanks32To35.moment3208_724

private theorem pole_3209_702 :
    P1_7_1.groupedPoleMoment 3209 702 ≤ 2936492475204 :=
  Research6969.PackedRanks.TerminalRanks36To39.moment3209_702

private theorem pole_3209_724 :
    P1_7_1.groupedPoleMoment 3209 724 ≤ 3007761756493 :=
  Research6969.PackedRanks.TerminalRanks36To39.moment3209_724

private theorem pole_3322_747 :
    P1_7_1.groupedPoleMoment 3322 747 ≤ 3445098204118 :=
  Research6969.PackedRanks.PackedRanks255To257.moment3322_747

private theorem pole_3620_775 :
    P1_7_1.groupedPoleMoment 3620 775 ≤ 4674619806217 :=
  Research6969.PackedRanks.TerminalRanks36To39.moment3620_775

private theorem pole_3623_793 :
    P1_7_1.groupedPoleMoment 3623 793 ≤ 4771760428124 :=
  Research6969.PackedRanks.TerminalRanks40To43.moment3623_793

private theorem pole_3623_819 :
    P1_7_1.groupedPoleMoment 3623 819 ≤ 4892906717079 :=
  Research6969.PackedRanks.PackedRanks258To260.moment3623_819

private theorem pole_3624_819 :
    P1_7_1.groupedPoleMoment 3624 819 ≤ 4897259437389 :=
  Research6969.PackedRanks.TerminalRanks44To47.moment3624_819

private theorem pole_3625_793 :
    P1_7_1.groupedPoleMoment 3625 793 ≤ 4780245027563 :=
  Research6969.PackedRanks.TerminalRanks44To47.moment3625_793

private theorem pole_3625_819 :
    P1_7_1.groupedPoleMoment 3625 819 ≤ 4901614794409 :=
  Research6969.PackedRanks.PackedRanks261To263.moment3625_819

private theorem pole_3626_793 :
    P1_7_1.groupedPoleMoment 3626 793 ≤ 4784491173220 :=
  Research6969.PackedRanks.TerminalRanks48To51.moment3626_793

private theorem pole_3626_819 :
    P1_7_1.groupedPoleMoment 3626 819 ≤ 4905972788959 :=
  Research6969.PackedRanks.PackedRanks264To266.moment3626_819

private theorem pole_3627_793 :
    P1_7_1.groupedPoleMoment 3627 793 ≤ 4788739883894 :=
  Research6969.PackedRanks.TerminalRanks48To51.moment3627_793

private theorem pole_3627_819 :
    P1_7_1.groupedPoleMoment 3627 819 ≤ 4910333421859 :=
  Research6969.PackedRanks.PackedRanks267To269.moment3627_819

private theorem pole_3628_781 :
    P1_7_1.groupedPoleMoment 3628 781 ≤ 4736360367482 :=
  _root_.PoleAffine6970.certified 3628 781 4736360367482 (by decide) (by decide +kernel)

private theorem pole_3628_782 :
    P1_7_1.groupedPoleMoment 3628 782 ≤ 4741090958317 :=
  _root_.PoleAffine6970.certified 3628 782 4741090958317 (by decide) (by decide +kernel)

private theorem pole_3628_783 :
    P1_7_1.groupedPoleMoment 3628 783 ≤ 4745819470168 :=
  Research6969.PackedRanks.PackedRanks270To272.moment3628_783

private theorem pole_3628_793 :
    P1_7_1.groupedPoleMoment 3628 793 ≤ 4792991160379 :=
  Research6969.PackedRanks.TerminalRanks52To55.moment3628_793

private theorem pole_3691_830 :
    P1_7_1.groupedPoleMoment 3691 830 ≤ 5249056297887 :=
  Research6969.PackedRanks.PackedRanks270To272.moment3691_830

private theorem pole_3767_814 :
    P1_7_1.groupedPoleMoment 3767 814 ≤ 5520825894692 :=
  Research6969.PackedRanks.PackedRanks273To275.moment3767_814

private theorem pole_3782_845 :
    P1_7_1.groupedPoleMoment 3782 845 ≤ 5756976302970 :=
  Research6969.PackedRanks.PackedRanks273To275.moment3782_845

private theorem pole_3798_830 :
    P1_7_1.groupedPoleMoment 3798 830 ≤ 5755034811151 :=
  Research6969.PackedRanks.TerminalRanks52To55.moment3798_830

private theorem pole_3852_861 :
    P1_7_1.groupedPoleMoment 3852 861 ≤ 6196939591060 :=
  Research6969.PackedRanks.PackedRanks273To275.moment3852_861

private theorem pole_3852_866 :
    P1_7_1.groupedPoleMoment 3852 866 ≤ 6224865038545 :=
  Research6969.PackedRanks.PackedRanks276To278.moment3852_866

private theorem pole_3896_854 :
    P1_7_1.groupedPoleMoment 3896 854 ≤ 6387110095257 :=
  Research6969.PackedRanks.TerminalRanks56To59.moment3896_854

private theorem pole_3901_854 :
    P1_7_1.groupedPoleMoment 3901 854 ≤ 6413535689982 :=
  Research6969.PackedRanks.TerminalRanks56To59.moment3901_854

private theorem pole_3901_882 :
    P1_7_1.groupedPoleMoment 3901 882 ≤ 6576375970149 :=
  Research6969.PackedRanks.TerminalRanks60To63.moment3901_882

private theorem pole_3902_854 :
    P1_7_1.groupedPoleMoment 3902 854 ≤ 6418829718882 :=
  Research6969.PackedRanks.TerminalRanks60To63.moment3902_854

private theorem pole_3902_882 :
    P1_7_1.groupedPoleMoment 3902 882 ≤ 6581809445307 :=
  Research6969.PackedRanks.TerminalRanks60To63.moment3902_882

private theorem pole_3903_854 :
    P1_7_1.groupedPoleMoment 3903 854 ≤ 6424126719762 :=
  Research6969.PackedRanks.TerminalRanks64To67.moment3903_854

private theorem pole_3903_882 :
    P1_7_1.groupedPoleMoment 3903 882 ≤ 6587245977411 :=
  Research6969.PackedRanks.TerminalRanks64To67.moment3903_882

private theorem pole_3905_854 :
    P1_7_1.groupedPoleMoment 3905 854 ≤ 6434729640882 :=
  Research6969.PackedRanks.TerminalRanks64To67.moment3905_854

private theorem pole_3905_882 :
    P1_7_1.groupedPoleMoment 3905 882 ≤ 6598128215989 :=
  Research6969.PackedRanks.TerminalRanks64To67.moment3905_882

private theorem pole_3906_854 :
    P1_7_1.groupedPoleMoment 3906 854 ≤ 6440035562832 :=
  Research6969.PackedRanks.TerminalRanks68To71.moment3906_854

private theorem pole_3906_882 :
    P1_7_1.groupedPoleMoment 3906 882 ≤ 6603573924229 :=
  Research6969.PackedRanks.TerminalRanks68To71.moment3906_882

private theorem pole_3907_834 :
    P1_7_1.groupedPoleMoment 3907 834 ≤ 6327305614587 :=
  Research6969.PackedRanks.TerminalRanks68To71.moment3907_834

private theorem pole_3907_854 :
    P1_7_1.groupedPoleMoment 3907 854 ≤ 6445344460182 :=
  Research6969.PackedRanks.TerminalRanks72To75.moment3907_854

private theorem pole_3913_874 :
    P1_7_1.groupedPoleMoment 3913 874 ≤ 6594957993633 :=
  Research6969.PackedRanks.PackedRanks276To278.moment3913_874

private theorem pole_3923_851 :
    P1_7_1.groupedPoleMoment 3923 851 ≤ 6512804695549 :=
  Research6969.PackedRanks.PackedRanks279To281.moment3923_851

private theorem pole_3989_885 :
    P1_7_1.groupedPoleMoment 3989 885 ≤ 7085003902524 :=
  Research6969.PackedRanks.PackedRanks279To281.moment3989_885

private theorem pole_4037_875 :
    P1_7_1.groupedPoleMoment 4037 875 ≤ 7298293490304 :=
  Research6969.PackedRanks.PackedRanks282To284.moment4037_875

private theorem pole_4038_864 :
    P1_7_1.groupedPoleMoment 4038 864 ≤ 7232363502162 :=
  Research6969.PackedRanks.PackedRanks282To284.moment4038_864

private theorem pole_4063_892 :
    P1_7_1.groupedPoleMoment 4063 892 ≤ 7563211302447 :=
  Research6969.PackedRanks.PackedRanks285To287.moment4063_892

private theorem pole_4063_893 :
    P1_7_1.groupedPoleMoment 4063 893 ≤ 7569810562400 :=
  Research6969.PackedRanks.PackedRanks288To290.moment4063_893

private theorem pole_4064_890 :
    P1_7_1.groupedPoleMoment 4064 890 ≤ 7555988947369 :=
  Research6969.PackedRanks.PackedRanks288To290.moment4064_890

private theorem pole_4117_893 :
    P1_7_1.groupedPoleMoment 4117 893 ≤ 7898464820375 :=
  Research6969.PackedRanks.PackedRanks288To290.moment4117_893

private theorem pole_4137_897 :
    P1_7_1.groupedPoleMoment 4137 897 ≤ 8050621479572 :=
  Research6969.PackedRanks.PackedRanks291To293.moment4137_897

private theorem pole_4175_894 :
    P1_7_1.groupedPoleMoment 4175 894 ≤ 8269353083383 :=
  Research6969.PackedRanks.TerminalRanks72To75.moment4175_894

private theorem pole_4178_894 :
    P1_7_1.groupedPoleMoment 4178 894 ≤ 8288484232853 :=
  Research6969.PackedRanks.TerminalRanks72To75.moment4178_894

private theorem pole_4180_894 :
    P1_7_1.groupedPoleMoment 4180 894 ≤ 8301255031708 :=
  Research6969.PackedRanks.TerminalRanks76To78.moment4180_894

private theorem pole_4182_898 :
    P1_7_1.groupedPoleMoment 4182 898 ≤ 8343071159337 :=
  Research6969.PackedRanks.PackedRanks291To293.moment4182_898

private theorem pole_4184_894 :
    P1_7_1.groupedPoleMoment 4184 894 ≤ 8326836739738 :=
  Research6969.PackedRanks.TerminalRanks76To78.moment4184_894

private theorem pole_4463_982 :
    P1_7_1.groupedPoleMoment 4463 982 ≤ 11028049925768 :=
  Research6969.PackedRanks.PackedRanks297To299.moment4463_982

private theorem pole_4464_947 :
    P1_7_1.groupedPoleMoment 4464 947 ≤ 10727945722509 :=
  _root_.PoleAffine6970.certified 4464 947 10727945722509 (by decide) (by decide +kernel)

private theorem pole_4465_963 :
    P1_7_1.groupedPoleMoment 4465 963 ≤ 10877088344236 :=
  Research6969.PackedRanks.PackedRanks303To305.moment4465_963

private theorem pole_5507_1244 :
    P1_7_1.groupedPoleMoment 5507 1244 ≤ 26084011577468 :=
  Research6969.PackedRanks.PackedRanks306To308.moment5507_1244

private theorem pole_5509_1213 :
    P1_7_1.groupedPoleMoment 5509 1213 ≤ 25607310424524 :=
  Research6969.PackedRanks.PackedRanks306To308.moment5509_1213

private theorem pole_5510_1189 :
    P1_7_1.groupedPoleMoment 5510 1189 ≤ 25226292539926 :=
  Research6969.PackedRanks.PackedRanks309To311.moment5510_1189

private theorem pole_5511_1169 :
    P1_7_1.groupedPoleMoment 5511 1169 ≤ 24908733781624 :=
  _root_.PoleAffine6970.certified 5511 1169 24908733781624 (by decide) (by decide +kernel)

private theorem pole_5512_1189 :
    P1_7_1.groupedPoleMoment 5512 1189 ≤ 25255771038451 :=
  Research6969.PackedRanks.PackedRanks315To317.moment5512_1189

private theorem pole_5512_1213 :
    P1_7_1.groupedPoleMoment 5512 1213 ≤ 25652240151764 :=
  Research6969.PackedRanks.PackedRanks315To317.moment5512_1213

private theorem pole_6690_1474 :
    P1_7_1.groupedPoleMoment 6690 1474 ≤ 55703383755931 :=
  Research6969.PackedRanks.PackedRanks315To317.moment6690_1474

private theorem pole_6690_1512 :
    P1_7_1.groupedPoleMoment 6690 1512 ≤ 56816483122989 :=
  Research6969.PackedRanks.PackedRanks318To320.moment6690_1512

private theorem pole_6696_1474 :
    P1_7_1.groupedPoleMoment 6696 1474 ≤ 55864419956306 :=
  Research6969.PackedRanks.PackedRanks324To326.moment6696_1474

private theorem pole_6696_1512 :
    P1_7_1.groupedPoleMoment 6696 1512 ≤ 56980856955989 :=
  Research6969.PackedRanks.PackedRanks327To329.moment6696_1512

private theorem pole_6697_1474 :
    P1_7_1.groupedPoleMoment 6697 1474 ≤ 55891290082931 :=
  Research6969.PackedRanks.PackedRanks327To329.moment6697_1474

private theorem pole_6698_1445 :
    P1_7_1.groupedPoleMoment 6698 1445 ≤ 55058665830093 :=
  Research6969.PackedRanks.PackedRanks330To332.moment6698_1445

private theorem pole_7835_1720 :
    P1_7_1.groupedPoleMoment 7835 1720 ≤ 104477286568219 :=
  Research6969.PackedRanks.PackedRanks333To335.moment7835_1720

private theorem pole_7948_1750 :
    P1_7_1.groupedPoleMoment 7948 1750 ≤ 110890906752819 :=
  Research6969.PackedRanks.PackedRanks336To338.moment7948_1750

private theorem pole_7950_1750 :
    P1_7_1.groupedPoleMoment 7950 1750 ≤ 110980791054694 :=
  Research6969.PackedRanks.PackedRanks336To338.moment7950_1750

private theorem pole_7950_1796 :
    P1_7_1.groupedPoleMoment 7950 1796 ≤ 113242283843565 :=
  Research6969.PackedRanks.PackedRanks339To341.moment7950_1796

private theorem pole_7952_1716 :
    P1_7_1.groupedPoleMoment 7952 1716 ≤ 109384694947514 :=
  Research6969.PackedRanks.PackedRanks342To344.moment7952_1716

private theorem pole_7953_1750 :
    P1_7_1.groupedPoleMoment 7953 1750 ≤ 111115710437454 :=
  Research6969.PackedRanks.PackedRanks345To347.moment7953_1750

private theorem pole_7954_1716 :
    P1_7_1.groupedPoleMoment 7954 1716 ≤ 109473260530676 :=
  Research6969.PackedRanks.PackedRanks345To347.moment7954_1716

private theorem pole_9623_2174 :
    P1_7_1.groupedPoleMoment 9623 2174 ≤ 243058712908678 :=
  Research6969.PackedRanks.PackedRanks351To353.moment9623_2174

private theorem pole_9626_2077 :
    P1_7_1.groupedPoleMoment 9626 2077 ≤ 234809190715807 :=
  Research6969.PackedRanks.PackedRanks354To356.moment9626_2077

private theorem pole_9628_2077 :
    P1_7_1.groupedPoleMoment 9628 2077 ≤ 234966243278304 :=
  Research6969.PackedRanks.PackedRanks357To359.moment9628_2077

private theorem pole_9628_2118 :
    P1_7_1.groupedPoleMoment 9628 2118 ≤ 238575106344005 :=
  Research6969.PackedRanks.PackedRanks360To362.moment9628_2118

private theorem pole_11569_2498 :
    P1_7_1.groupedPoleMoment 11569 2498 ≤ 490105817011183 :=
  _root_.PoleAffine6970.certified 11569 2498 490105817011183 (by decide) (by decide +kernel)

private theorem pole_11575_2548 :
    P1_7_1.groupedPoleMoment 11575 2548 ≤ 498569901356632 :=
  Research6969.PackedRanks.PackedRanks360To362.moment11575_2548

private theorem pole_11575_2615 :
    P1_7_1.groupedPoleMoment 11575 2615 ≤ 508734991702659 :=
  Research6969.PackedRanks.PackedRanks363To365.moment11575_2615

private theorem pole_11579_2498 :
    P1_7_1.groupedPoleMoment 11579 2498 ≤ 491470625461013 :=
  Research6969.PackedRanks.PackedRanks366To368.moment11579_2498

private theorem pole_11579_2548 :
    P1_7_1.groupedPoleMoment 11579 2548 ≤ 499124969898998 :=
  Research6969.PackedRanks.PackedRanks366To368.moment11579_2548

private theorem pole_11580_2548 :
    P1_7_1.groupedPoleMoment 11580 2548 ≤ 499263802703202 :=
  Research6969.PackedRanks.PackedRanks369To371.moment11580_2548

private theorem pole_11581_2498 :
    P1_7_1.groupedPoleMoment 11581 2498 ≤ 491743896877039 :=
  Research6969.PackedRanks.PackedRanks369To371.moment11581_2498

private theorem pole_13950_3150 :
    P1_7_1.groupedPoleMoment 13950 3150 ≤ 1072717072025530 :=
  Research6969.PackedRanks.PackedRanks378To380.moment13950_3150

private theorem pole_13952_3070 :
    P1_7_1.groupedPoleMoment 13952 3070 ≤ 1051954539834997 :=
  Research6969.PackedRanks.PackedRanks378To380.moment13952_3070

private theorem pole_13953_3010 :
    P1_7_1.groupedPoleMoment 13953 3010 ≤ 1036125345444439 :=
  Research6969.PackedRanks.PackedRanks381To383.moment13953_3010

theorem bank_2801_3907_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3907,854,u⟩,665994008985600,6445344460182⟩ :=
  bank_checked 2801 3907 854 u 665994008985600 6445344460182
    (by decide) (by decide) (by decide) (by decide) pole_3907_854

theorem bank_2601_3628_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3628,793,u⟩,533334139076608,4792991160379⟩ :=
  bank_checked 2601 3628 793 u 533334139076608 4792991160379
    (by decide) (by decide) (by decide) (by decide) pole_3628_793

theorem bank_2801_3902_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3902,882,u⟩,682478913454080,6581809445307⟩ :=
  bank_checked 2801 3902 882 u 682478913454080 6581809445307
    (by decide) (by decide) (by decide) (by decide) pole_3902_882

theorem bank_2801_3906_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3906,854,u⟩,665994008985600,6440035562832⟩ :=
  bank_checked 2801 3906 854 u 665994008985600 6440035562832
    (by decide) (by decide) (by decide) (by decide) pole_3906_854

theorem bank_4801_6696_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4801,6696,1512,u⟩,3434740917207040,56980856955989⟩ :=
  bank_checked 4801 6696 1512 u 3434740917207040 56980856955989
    (by decide) (by decide) (by decide) (by decide) pole_6696_1512

theorem bank_2801_3905_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3905,882,u⟩,682478913454080,6598128215989⟩ :=
  bank_checked 2801 3905 882 u 682478913454080 6598128215989
    (by decide) (by decide) (by decide) (by decide) pole_3905_882

theorem bank_2801_3906_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3906,882,u⟩,682478913454080,6603573924229⟩ :=
  bank_checked 2801 3906 882 u 682478913454080 6603573924229
    (by decide) (by decide) (by decide) (by decide) pole_3906_882

theorem bank_2601_3627_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3627,793,u⟩,533334139076608,4788739883894⟩ :=
  bank_checked 2601 3627 793 u 533334139076608 4788739883894
    (by decide) (by decide) (by decide) (by decide) pole_3627_793

theorem bank_2301_3208_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3208,724,u⟩,378271924224000,3004743122568⟩ :=
  bank_checked 2301 3208 724 u 378271924224000 3004743122568
    (by decide) (by decide) (by decide) (by decide) pole_3208_724

theorem bank_2601_3625_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3625,793,u⟩,533334139076608,4780245027563⟩ :=
  bank_checked 2601 3625 793 u 533334139076608 4780245027563
    (by decide) (by decide) (by decide) (by decide) pole_3625_793

theorem bank_2301_3207_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3207,724,u⟩,378271924224000,3001726552718⟩ :=
  bank_checked 2301 3207 724 u 378271924224000 3001726552718
    (by decide) (by decide) (by decide) (by decide) pole_3207_724

theorem bank_2801_3905_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3905,854,u⟩,665994008985600,6434729640882⟩ :=
  bank_checked 2801 3905 854 u 665994008985600 6434729640882
    (by decide) (by decide) (by decide) (by decide) pole_3905_854

theorem bank_5701_7950_1796 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5701,7950,1796,u⟩,5751590126092288,113242283843565⟩ :=
  bank_checked 5701 7950 1796 u 5751590126092288 113242283843565
    (by decide) (by decide) (by decide) (by decide) pole_7950_1796

theorem bank_2301_3204_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3204,724,u⟩,378271924224000,2992689220368⟩ :=
  bank_checked 2301 3204 724 u 378271924224000 2992689220368
    (by decide) (by decide) (by decide) (by decide) pole_3204_724

theorem bank_2601_3625_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3625,819,u⟩,546534142771200,4901614794409⟩ :=
  bank_checked 2601 3625 819 u 546534142771200 4901614794409
    (by decide) (by decide) (by decide) (by decide) pole_3625_819

theorem bank_6901_9623_2174 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6901,9623,2174,u⟩,10200078057472000,243058712908678⟩ :=
  bank_checked 6901 9623 2174 u 10200078057472000 243058712908678
    (by decide) (by decide) (by decide) (by decide) pole_9623_2174

theorem bank_2601_3626_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3626,819,u⟩,546534142771200,4905972788959⟩ :=
  bank_checked 2601 3626 819 u 546534142771200 4905972788959
    (by decide) (by decide) (by decide) (by decide) pole_3626_819

theorem bank_2301_3207_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3207,702,u⟩,369529993297920,2930605494152⟩ :=
  bank_checked 2301 3207 702 u 369529993297920 2930605494152
    (by decide) (by decide) (by decide) (by decide) pole_3207_702

theorem bank_2802_3903_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2802,3903,854,u⟩,666526325145600,6424126719762⟩ :=
  bank_checked 2802 3903 854 u 666526325145600 6424126719762
    (by decide) (by decide) (by decide) (by decide) pole_3903_854

theorem bank_2601_3623_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3623,819,u⟩,546534142771200,4892906717079⟩ :=
  bank_checked 2601 3623 819 u 546534142771200 4892906717079
    (by decide) (by decide) (by decide) (by decide) pole_3623_819

theorem bank_2301_3204_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3204,702,u⟩,369529993297920,2921790084349⟩ :=
  bank_checked 2301 3204 702 u 369529993297920 2921790084349
    (by decide) (by decide) (by decide) (by decide) pole_3204_702

theorem bank_3001_4178_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3001,4178,894,u⟩,804652430131200,8288484232853⟩ :=
  bank_checked 3001 4178 894 u 804652430131200 8288484232853
    (by decide) (by decide) (by decide) (by decide) pole_4178_894

theorem bank_2601_3620_775 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3620,775,u⟩,524090966278144,4674619806217⟩ :=
  bank_checked 2601 3620 775 u 524090966278144 4674619806217
    (by decide) (by decide) (by decide) (by decide) pole_3620_775

theorem bank_3001_4175_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3001,4175,894,u⟩,804652430131200,8269353083383⟩ :=
  bank_checked 3001 4175 894 u 804652430131200 8269353083383
    (by decide) (by decide) (by decide) (by decide) pole_4175_894

theorem bank_2801_3896_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3896,854,u⟩,665994008985600,6387110095257⟩ :=
  bank_checked 2801 3896 854 u 665994008985600 6387110095257
    (by decide) (by decide) (by decide) (by decide) pole_3896_854

theorem bank_2802_3906_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2802,3906,854,u⟩,666526325145600,6440035562832⟩ :=
  bank_checked 2802 3906 854 u 666526325145600 6440035562832
    (by decide) (by decide) (by decide) (by decide) pole_3906_854

theorem bank_2301_3209_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3209,702,u⟩,369529993297920,2936492475204⟩ :=
  bank_checked 2301 3209 702 u 369529993297920 2936492475204
    (by decide) (by decide) (by decide) (by decide) pole_3209_702

theorem bank_4802_6697_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4802,6697,1474,u⟩,3370690805760000,55891290082931⟩ :=
  bank_checked 4802 6697 1474 u 3370690805760000 55891290082931
    (by decide) (by decide) (by decide) (by decide) pole_6697_1474

theorem bank_2602_3627_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3627,793,u⟩,533793196998656,4788739883894⟩ :=
  bank_checked 2602 3627 793 u 533793196998656 4788739883894
    (by decide) (by decide) (by decide) (by decide) pole_3627_793

theorem bank_8308_11575_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8308,11575,2548,u⟩,17437292043960320,498569901356632⟩ :=
  bank_checked 8308 11575 2548 u 17437292043960320 498569901356632
    (by decide) (by decide) (by decide) (by decide) pole_11575_2548

theorem bank_2805_3906_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2805,3906,854,u⟩,668124618424320,6440035562832⟩ :=
  bank_checked 2805 3906 854 u 668124618424320 6440035562832
    (by decide) (by decide) (by decide) (by decide) pole_3906_854

theorem bank_2601_3627_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3627,819,u⟩,546534142771200,4910333421859⟩ :=
  bank_checked 2601 3627 819 u 546534142771200 4910333421859
    (by decide) (by decide) (by decide) (by decide) pole_3627_819

theorem bank_3952_5509_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3952,5509,1213,u⟩,1879191526834176,25607310424524⟩ :=
  bank_checked 3952 5509 1213 u 1879191526834176 25607310424524
    (by decide) (by decide) (by decide) (by decide) pole_5509_1213

theorem bank_8304_11575_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8304,11575,2548,u⟩,17418495435735040,498569901356632⟩ :=
  bank_checked 8304 11575 2548 u 17418495435735040 498569901356632
    (by decide) (by decide) (by decide) (by decide) pole_11575_2548

theorem bank_2301_3203_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3203,724,u⟩,378271924224000,2989680899568⟩ :=
  bank_checked 2301 3203 724 u 378271924224000 2989680899568
    (by decide) (by decide) (by decide) (by decide) pole_3203_724

theorem bank_8302_11575_2615 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8302,11575,2615,u⟩,17755053843546112,508734991702659⟩ :=
  bank_checked 8302 11575 2615 u 17755053843546112 508734991702659
    (by decide) (by decide) (by decide) (by decide) pole_11575_2615

theorem bank_2601_3624_819 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3624,819,u⟩,546534142771200,4897259437389⟩ :=
  bank_checked 2601 3624 819 u 546534142771200 4897259437389
    (by decide) (by decide) (by decide) (by decide) pole_3624_819

theorem bank_2601_3623_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3623,793,u⟩,533334139076608,4771760428124⟩ :=
  bank_checked 2601 3623 793 u 533334139076608 4771760428124
    (by decide) (by decide) (by decide) (by decide) pole_3623_793

theorem bank_3001_4180_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3001,4180,894,u⟩,804652430131200,8301255031708⟩ :=
  bank_checked 3001 4180 894 u 804652430131200 8301255031708
    (by decide) (by decide) (by decide) (by decide) pole_4180_894

theorem bank_2301_3208_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3208,702,u⟩,369529993297920,2933547980091⟩ :=
  bank_checked 2301 3208 702 u 369529993297920 2933547980091
    (by decide) (by decide) (by decide) (by decide) pole_3208_702

theorem bank_2802_3905_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2802,3905,854,u⟩,666526325145600,6434729640882⟩ :=
  bank_checked 2802 3905 854 u 666526325145600 6434729640882
    (by decide) (by decide) (by decide) (by decide) pole_3905_854

theorem bank_3952_5510_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3952,5510,1189,u⟩,1850839393894400,25226292539926⟩ :=
  bank_checked 3952 5510 1189 u 1850839393894400 25226292539926
    (by decide) (by decide) (by decide) (by decide) pole_5510_1189

theorem bank_2602_3626_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2602,3626,793,u⟩,533793196998656,4784491173220⟩ :=
  bank_checked 2602 3626 793 u 533793196998656 4784491173220
    (by decide) (by decide) (by decide) (by decide) pole_3626_793

theorem bank_2601_3626_793 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3626,793,u⟩,533334139076608,4784491173220⟩ :=
  bank_checked 2601 3626 793 u 533334139076608 4784491173220
    (by decide) (by decide) (by decide) (by decide) pole_3626_793

theorem bank_3952_5507_1244 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3952,5507,1244,u⟩,1915473271193600,26084011577468⟩ :=
  bank_checked 3952 5507 1244 u 1915473271193600 26084011577468
    (by decide) (by decide) (by decide) (by decide) pole_5507_1244

theorem bank_5702_7948_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5702,7948,1750,u⟩,5641801597714432,110890906752819⟩ :=
  bank_checked 5702 7948 1750 u 5641801597714432 110890906752819
    (by decide) (by decide) (by decide) (by decide) pole_7948_1750

theorem bank_5625_7835_1720 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5625,7835,1720,u⟩,5401185994670080,104477286568219⟩ :=
  bank_checked 5625 7835 1720 u 5401185994670080 104477286568219
    (by decide) (by decide) (by decide) (by decide) pole_7835_1720

theorem bank_2801_3901_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3901,882,u⟩,682478913454080,6576375970149⟩ :=
  bank_checked 2801 3901 882 u 682478913454080 6576375970149
    (by decide) (by decide) (by decide) (by decide) pole_3901_882

theorem bank_5701_7950_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5701,7950,1750,u⟩,5639585936441344,110980791054694⟩ :=
  bank_checked 5701 7950 1750 u 5639585936441344 110980791054694
    (by decide) (by decide) (by decide) (by decide) pole_7950_1750

theorem bank_3201_4463_982 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3201,4463,982,u⟩,998465823047680,11028049925768⟩ :=
  bank_checked 3201 4463 982 u 998465823047680 11028049925768
    (by decide) (by decide) (by decide) (by decide) pole_4463_982

theorem bank_4805_6690_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4805,6690,1474,u⟩,3375408473702400,55703383755931⟩ :=
  bank_checked 4805 6690 1474 u 3375408473702400 55703383755931
    (by decide) (by decide) (by decide) (by decide) pole_6690_1474

theorem bank_2302_3206_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2302,3206,702,u⟩,369889537687552,2927665016684⟩ :=
  bank_checked 2302 3206 702 u 369889537687552 2927665016684
    (by decide) (by decide) (by decide) (by decide) pole_3206_702

theorem bank_2801_3903_882 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3903,882,u⟩,682478913454080,6587245977411⟩ :=
  bank_checked 2801 3903 882 u 682478913454080 6587245977411
    (by decide) (by decide) (by decide) (by decide) pole_3903_882

theorem bank_4801_6690_1512 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4801,6690,1512,u⟩,3434740917207040,56816483122989⟩ :=
  bank_checked 4801 6690 1512 u 3434740917207040 56816483122989
    (by decide) (by decide) (by decide) (by decide) pole_6690_1512

theorem bank_2801_3903_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3903,854,u⟩,665994008985600,6424126719762⟩ :=
  bank_checked 2801 3903 854 u 665994008985600 6424126719762
    (by decide) (by decide) (by decide) (by decide) pole_3903_854

theorem bank_2301_3206_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3206,724,u⟩,378271924224000,2998712046218⟩ :=
  bank_checked 2301 3206 724 u 378271924224000 2998712046218
    (by decide) (by decide) (by decide) (by decide) pole_3206_724

theorem bank_2801_3901_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3901,854,u⟩,665994008985600,6413535689982⟩ :=
  bank_checked 2801 3901 854 u 665994008985600 6413535689982
    (by decide) (by decide) (by decide) (by decide) pole_3901_854

theorem bank_2301_3201_702 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3201,702,u⟩,369529993297920,2912992731804⟩ :=
  bank_checked 2301 3201 702 u 369529993297920 2912992731804
    (by decide) (by decide) (by decide) (by decide) pole_3201_702

theorem bank_2388_3322_747 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2388,3322,747,u⟩,420928100499456,3445098204118⟩ :=
  bank_checked 2388 3322 747 u 420928100499456 3445098204118
    (by decide) (by decide) (by decide) (by decide) pole_3322_747

theorem bank_2768_3852_861 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2768,3852,861,u⟩,652578441134080,6196939591060⟩ :=
  bank_checked 2768 3852 861 u 652578441134080 6196939591060
    (by decide) (by decide) (by decide) (by decide) pole_3852_861

theorem bank_5701_7948_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5701,7948,1750,u⟩,5639585936441344,110890906752819⟩ :=
  bank_checked 5701 7948 1750 u 5639585936441344 110890906752819
    (by decide) (by decide) (by decide) (by decide) pole_7948_1750

theorem bank_2718_3782_845 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2718,3782,845,u⟩,617621286027264,5756976302970⟩ :=
  bank_checked 2718 3782 845 u 617621286027264 5756976302970
    (by decide) (by decide) (by decide) (by decide) pole_3782_845

theorem bank_2812_3913_874 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2812,3913,874,u⟩,683771002880000,6594957993633⟩ :=
  bank_checked 2812 3913 874 u 683771002880000 6594957993633
    (by decide) (by decide) (by decide) (by decide) pole_3913_874

theorem bank_2731_3798_830 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2731,3798,830,u⟩,615828072955904,5755034811151⟩ :=
  bank_checked 2731 3798 830 u 615828072955904 5755034811151
    (by decide) (by decide) (by decide) (by decide) pole_3798_830

theorem bank_2301_3209_724 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2301,3209,724,u⟩,378271924224000,3007761756493⟩ :=
  bank_checked 2301 3209 724 u 378271924224000 3007761756493
    (by decide) (by decide) (by decide) (by decide) pole_3209_724

theorem bank_10001_13950_3150 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10001,13950,3150,u⟩,31034610050924544,1072717072025530⟩ :=
  bank_checked 10001 13950 3150 u 31034610050924544 1072717072025530
    (by decide) (by decide) (by decide) (by decide) pole_13950_3150

theorem bank_2896_4038_864 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2896,4038,864,u⟩,723972888985600,7232363502162⟩ :=
  bank_checked 2896 4038 864 u 723972888985600 7232363502162
    (by decide) (by decide) (by decide) (by decide) pole_4038_864

theorem bank_2918_4064_890 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2918,4064,890,u⟩,753145732399104,7555988947369⟩ :=
  bank_checked 2918 4064 890 u 753145732399104 7555988947369
    (by decide) (by decide) (by decide) (by decide) pole_4064_890

theorem bank_3002_4184_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3002,4184,894,u⟩,805251881369600,8326836739738⟩ :=
  bank_checked 3002 4184 894 u 805251881369600 8326836739738
    (by decide) (by decide) (by decide) (by decide) pole_4184_894

theorem bank_10004_13952_3070 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10004,13952,3070,u⟩,30455640113807360,1051954539834997⟩ :=
  bank_checked 10004 13952 3070 u 30455640113807360 1051954539834997
    (by decide) (by decide) (by decide) (by decide) pole_13952_3070

theorem bank_2997_4182_898 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2997,4182,898,u⟩,804993131872256,8343071159337⟩ :=
  bank_checked 2997 4182 898 u 804993131872256 8343071159337
    (by decide) (by decide) (by decide) (by decide) pole_4182_898

theorem bank_8304_11580_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8304,11580,2548,u⟩,17418495435735040,499263802703202⟩ :=
  bank_checked 8304 11580 2548 u 17418495435735040 499263802703202
    (by decide) (by decide) (by decide) (by decide) pole_11580_2548

theorem bank_8298_11569_2498 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8298,11569,2498,u⟩,17130000980377600,490105817011183⟩ :=
  bank_checked 8298 11569 2498 u 17130000980377600 490105817011183
    (by decide) (by decide) (by decide) (by decide) pole_11569_2498

theorem bank_8300_11581_2498 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8300,11581,2498,u⟩,17139238515245056,491743896877039⟩ :=
  bank_checked 8300 11581 2498 u 17139238515245056 491743896877039
    (by decide) (by decide) (by decide) (by decide) pole_11581_2498

theorem bank_2917_4063_892 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2917,4063,892,u⟩,753852707766272,7563211302447⟩ :=
  bank_checked 2917 4063 892 u 753852707766272 7563211302447
    (by decide) (by decide) (by decide) (by decide) pole_4063_892

theorem bank_2952_4117_893 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2952,4117,893,u⟩,774906445561856,7898464820375⟩ :=
  bank_checked 2952 4117 893 u 774906445561856 7898464820375
    (by decide) (by decide) (by decide) (by decide) pole_4117_893

theorem bank_6900_9628_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6900,9628,2077,u⟩,9849424459857920,234966243278304⟩ :=
  bank_checked 6900 9628 2077 u 9849424459857920 234966243278304
    (by decide) (by decide) (by decide) (by decide) pole_9628_2077

theorem bank_3949_5511_1169 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3949,5511,1169,u⟩,1823933886627840,24908733781624⟩ :=
  bank_checked 3949 5511 1169 u 1823933886627840 24908733781624
    (by decide) (by decide) (by decide) (by decide) pole_5511_1169

theorem bank_2653_3691_830 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2653,3691,830,u⟩,577129590554624,5249056297887⟩ :=
  bank_checked 2653 3691 830 u 577129590554624 5249056297887
    (by decide) (by decide) (by decide) (by decide) pole_3691_830

theorem bank_4800_6698_1445 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4800,6698,1445,u⟩,3317023033262080,55058665830093⟩ :=
  bank_checked 4800 6698 1445 u 3317023033262080 55058665830093
    (by decide) (by decide) (by decide) (by decide) pole_6698_1445

theorem bank_2768_3852_866 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2768,3852,866,u⟩,655445302968320,6224865038545⟩ :=
  bank_checked 2768 3852 866 u 655445302968320 6224865038545
    (by decide) (by decide) (by decide) (by decide) pole_3852_866

theorem bank_2101_2930_632 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2101,2930,632,u⟩,278356530298880,2019119590628⟩ :=
  bank_checked 2101 2930 632 u 278356530298880 2019119590628
    (by decide) (by decide) (by decide) (by decide) pole_2930_632

theorem bank_2600_3628_783 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2600,3628,783,u⟩,527755772952576,4745819470168⟩ :=
  bank_checked 2600 3628 783 u 527755772952576 4745819470168
    (by decide) (by decide) (by decide) (by decide) pole_3628_783

theorem bank_3199_4464_947 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3199,4464,947,u⟩,969886596595712,10727945722509⟩ :=
  bank_checked 3199 4464 947 u 969886596595712 10727945722509
    (by decide) (by decide) (by decide) (by decide) pole_4464_947

theorem bank_3200_4465_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3200,4465,963,u⟩,983050615259136,10877088344236⟩ :=
  bank_checked 3200 4465 963 u 983050615259136 10877088344236
    (by decide) (by decide) (by decide) (by decide) pole_4465_963

theorem bank_3950_5512_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3950,5512,1189,u⟩,1848744952463360,25255771038451⟩ :=
  bank_checked 3950 5512 1189 u 1848744952463360 25255771038451
    (by decide) (by decide) (by decide) (by decide) pole_5512_1189

theorem bank_5700_7954_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5700,7954,1716,u⟩,5553838907981824,109473260530676⟩ :=
  bank_checked 5700 7954 1716 u 5553838907981824 109473260530676
    (by decide) (by decide) (by decide) (by decide) pole_7954_1716

theorem bank_2601_3628_782 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3628,782,u⟩,527695962439680,4741090958317⟩ :=
  bank_checked 2601 3628 782 u 527695962439680 4741090958317
    (by decide) (by decide) (by decide) (by decide) pole_3628_782

theorem bank_2601_3628_781 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2601,3628,781,u⟩,527181781925888,4736360367482⟩ :=
  bank_checked 2601 3628 781 u 527181781925888 4736360367482
    (by decide) (by decide) (by decide) (by decide) pole_3628_781

theorem bank_2800_3907_834 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2800,3907,834,u⟩,653560508579840,6327305614587⟩ :=
  bank_checked 2800 3907 834 u 653560508579840 6327305614587
    (by decide) (by decide) (by decide) (by decide) pole_3907_834

theorem bank_3951_5512_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3951,5512,1189,u⟩,1849792017203200,25255771038451⟩ :=
  bank_checked 3951 5512 1189 u 1849792017203200 25255771038451
    (by decide) (by decide) (by decide) (by decide) pole_5512_1189

theorem bank_5703_7954_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5703,7954,1716,u⟩,5560379779317760,109473260530676⟩ :=
  bank_checked 5703 7954 1716 u 5560379779317760 109473260530676
    (by decide) (by decide) (by decide) (by decide) pole_7954_1716

theorem bank_3201_4465_963 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3201,4465,963,u⟩,983737851445248,10877088344236⟩ :=
  bank_checked 3201 4465 963 u 983737851445248 10877088344236
    (by decide) (by decide) (by decide) (by decide) pole_4465_963

theorem bank_3952_5512_1189 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3952,5512,1189,u⟩,1850839393894400,25255771038451⟩ :=
  bank_checked 3952 5512 1189 u 1850839393894400 25255771038451
    (by decide) (by decide) (by decide) (by decide) pole_5512_1189

theorem bank_5708_7952_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5708,7952,1716,u⟩,5571290233569280,109384694947514⟩ :=
  bank_checked 5708 7952 1716 u 5571290233569280 109384694947514
    (by decide) (by decide) (by decide) (by decide) pole_7952_1716

theorem bank_3951_5512_1213 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨3951,5512,1213,u⟩,1878126845493248,25652240151764⟩ :=
  bank_checked 3951 5512 1213 u 1878126845493248 25652240151764
    (by decide) (by decide) (by decide) (by decide) pole_5512_1213

theorem bank_2973_4137_897 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2973,4137,897,u⟩,789976206278656,8050621479572⟩ :=
  bank_checked 2973 4137 897 u 789976206278656 8050621479572
    (by decide) (by decide) (by decide) (by decide) pole_4137_897

theorem bank_2816_3923_851 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2816,3923,851,u⟩,672199863697408,6512804695549⟩ :=
  bank_checked 2816 3923 851 u 672199863697408 6512804695549
    (by decide) (by decide) (by decide) (by decide) pole_3923_851

theorem bank_5705_7952_1716 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5705,7952,1716,u⟩,5564742610714624,109384694947514⟩ :=
  bank_checked 5705 7952 1716 u 5564742610714624 109384694947514
    (by decide) (by decide) (by decide) (by decide) pole_7952_1716

theorem bank_6906_9626_2077 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6906,9626,2077,u⟩,9868593692672000,234809190715807⟩ :=
  bank_checked 6906 9626 2077 u 9868593692672000 234809190715807
    (by decide) (by decide) (by decide) (by decide) pole_9626_2077

theorem bank_4803_6697_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4803,6697,1474,u⟩,3372262975078400,55891290082931⟩ :=
  bank_checked 4803 6697 1474 u 3372262975078400 55891290082931
    (by decide) (by decide) (by decide) (by decide) pole_6697_1474

theorem bank_6901_9628_2118 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨6901,9628,2118,u⟩,10000281241387008,238575106344005⟩ :=
  bank_checked 6901 9628 2118 u 10000281241387008 238575106344005
    (by decide) (by decide) (by decide) (by decide) pole_9628_2118

theorem bank_5701_7953_1750 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨5701,7953,1750,u⟩,5639585936441344,111115710437454⟩ :=
  bank_checked 5701 7953 1750 u 5639585936441344 111115710437454
    (by decide) (by decide) (by decide) (by decide) pole_7953_1750

theorem bank_8299_11579_2498 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8299,11579,2498,u⟩,17134619420262400,491470625461013⟩ :=
  bank_checked 8299 11579 2498 u 17134619420262400 491470625461013
    (by decide) (by decide) (by decide) (by decide) pole_11579_2498

theorem bank_10004_13953_3010 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨10004,13953,3010,u⟩,30001510422937600,1036125345444439⟩ :=
  bank_checked 10004 13953 3010 u 30001510422937600 1036125345444439
    (by decide) (by decide) (by decide) (by decide) pole_13953_3010

theorem bank_2801_3902_854 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2801,3902,854,u⟩,665994008985600,6418829718882⟩ :=
  bank_checked 2801 3902 854 u 665994008985600 6418829718882
    (by decide) (by decide) (by decide) (by decide) pole_3902_854

theorem bank_2918_4063_893 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2918,4063,893,u⟩,755073772421120,7569810562400⟩ :=
  bank_checked 2918 4063 893 u 755073772421120 7569810562400
    (by decide) (by decide) (by decide) (by decide) pole_4063_893

theorem bank_2703_3767_814 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2703,3767,814,u⟩,592943209512960,5520825894692⟩ :=
  bank_checked 2703 3767 814 u 592943209512960 5520825894692
    (by decide) (by decide) (by decide) (by decide) pole_3767_814

theorem bank_4801_6697_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4801,6697,1474,u⟩,3369119023104000,55891290082931⟩ :=
  bank_checked 4801 6697 1474 u 3369119023104000 55891290082931
    (by decide) (by decide) (by decide) (by decide) pole_6697_1474

theorem bank_2865_3989_885 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2865,3989,885,u⟩,719773612113920,7085003902524⟩ :=
  bank_checked 2865 3989 885 u 719773612113920 7085003902524
    (by decide) (by decide) (by decide) (by decide) pole_3989_885

theorem bank_2898_4037_875 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2898,4037,875,u⟩,732116294303744,7298293490304⟩ :=
  bank_checked 2898 4037 875 u 732116294303744 7298293490304
    (by decide) (by decide) (by decide) (by decide) pole_4037_875

theorem bank_2999_4184_894 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨2999,4184,894,u⟩,803454231511040,8326836739738⟩ :=
  bank_checked 2999 4184 894 u 803454231511040 8326836739738
    (by decide) (by decide) (by decide) (by decide) pole_4184_894

theorem bank_8304_11579_2548 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨8304,11579,2548,u⟩,17418495435735040,499124969898998⟩ :=
  bank_checked 8304 11579 2548 u 17418495435735040 499124969898998
    (by decide) (by decide) (by decide) (by decide) pole_11579_2548

theorem bank_4801_6696_1474 (u : ℕ) :
    P3_7_1.BankOK ⟨⟨4801,6696,1474,u⟩,3369119023104000,55864419956306⟩ :=
  bank_checked 4801 6696 1474 u 3369119023104000 55864419956306
    (by decide) (by decide) (by decide) (by decide) pole_6696_1474

end Research6970.Height2313.Physical
