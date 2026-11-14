import ProximityPrize.SubmissionLower.RecoveryCore06
set_option autoImplicit false
set_option linter.all false
set_option Elab.async true
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source0:Parameters:=⟨48,1122,20,9,65,1,2⟩
theorem shape0:Shape source0:=by constructor<;>decide+kernel
theorem middle0 (h:ℕ) (hh:h≤9):65≤(source0.cutoff h+20-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source0,Parameters.cutoff,
          AQ.reserve]
theorem CPO:
    AM.AW source0.cutoff 131071 1122 20 9 65=27717348495507:=by
  decide+kernel
theorem rank0:AR.rankBound 48 1122 20 9 65=105705598:=by decide+kernel
theorem dimension0:Dimension source0 7260213395:=by
  exact AZ source0 7260213395 27717348495507 105705598
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle0 CPO rank0 (by decide)
def source1:Parameters:=⟨50,1038,20,9,68,1,2⟩
theorem shape1:Shape source1:=by constructor<;>decide+kernel
theorem middle1 (h:ℕ) (hh:h≤9):68≤(source1.cutoff h+20-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source1,Parameters.cutoff,
          AQ.reserve]
theorem COM:
    AM.AW source1.cutoff 131071 1038 20 9 68=28114742457739:=by
  decide+kernel
theorem rank1:AR.rankBound 50 1038 20 9 68=107197185:=by decide+kernel
theorem dimension1:Dimension source1 13643593099:=by
  exact AZ source1 13643593099 28114742457739 107197185
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle1 COM rank1 (by decide)
def source2:Parameters:=⟨52,949,22,10,71,1,2⟩
theorem shape2:Shape source2:=by constructor<;>decide+kernel
theorem middle2 (h:ℕ) (hh:h≤10):71≤(source2.cutoff h+22-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source2,Parameters.cutoff,
          AQ.reserve]
theorem CNU:
    AM.AW source2.cutoff 131071 949 22 10 71=32361544350750:=by
  decide+kernel
theorem rank2:AR.rankBound 52 949 22 10 71=123296314:=by decide+kernel
theorem dimension2:Dimension source2 40155413534:=by
  exact AZ source2 40155413534 32361544350750 123296314
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle2 CNU rank2 (by decide)
def source3:Parameters:=⟨56,800,25,12,77,1,2⟩
theorem shape3:Shape source3:=by constructor<;>decide+kernel
theorem middle3 (h:ℕ) (hh:h≤12):77≤(source3.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source3,Parameters.cutoff,
          AQ.reserve]
theorem CNC:
    AM.AW source3.cutoff 131071 800 25 12 77=39098119905013:=by
  decide+kernel
theorem rank3:AR.rankBound 56 800 25 12 77=148924194:=by decide+kernel
theorem dimension3:Dimension source3 58535993077:=by
  exact AZ source3 58535993077 39098119905013 148924194
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle3 CNC rank3 (by decide)
end EZ
end MergedPart0
section MergedPart1
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source4:Parameters:=⟨56,1000,25,12,77,1,2⟩
theorem shape4:Shape source4:=by constructor<;>decide+kernel
theorem middle4 (h:ℕ) (hh:h≤12):77≤(source4.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source4,Parameters.cutoff,
          AQ.reserve]
theorem COY:
    AM.AW source4.cutoff 131071 1000 25 12 77=49281075667213:=by
  decide+kernel
theorem rank4:AR.rankBound 56 1000 25 12 77=187451594:=by decide+kernel
theorem dimension4:Dimension source4 141765009677:=by
  exact AZ source4 141765009677 49281075667213 187451594
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle4 COY rank4 (by decide)
def source5:Parameters:=⟨56,1200,25,12,77,1,2⟩
theorem shape5:Shape source5:=by constructor<;>decide+kernel
theorem middle5 (h:ℕ) (hh:h≤12):77≤(source5.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source5,Parameters.cutoff,
          AQ.reserve]
theorem CPF:
    AM.AW source5.cutoff 131071 1200 25 12 77=59464031429413:=by
  decide+kernel
theorem rank5:AR.rankBound 56 1200 25 12 77=225978994:=by decide+kernel
theorem dimension5:Dimension source5 224994026277:=by
  exact AZ source5 224994026277 59464031429413 225978994
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle5 CPF rank5 (by decide)
def source6:Parameters:=⟨56,1400,25,12,77,1,2⟩
theorem shape6:Shape source6:=by constructor<;>decide+kernel
theorem middle6 (h:ℕ) (hh:h≤12):77≤(source6.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source6,Parameters.cutoff,
          AQ.reserve]
theorem CMZ:
    AM.AW source6.cutoff 131071 1400 25 12 77=69646987191613:=by
  decide+kernel
theorem rank6:AR.rankBound 56 1400 25 12 77=264506394:=by decide+kernel
theorem dimension6:Dimension source6 308223042877:=by
  exact AZ source6 308223042877 69646987191613 264506394
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle6 CMZ rank6 (by decide)
def source7:Parameters:=⟨58,628,25,11,79,1,2⟩
theorem shape7:Shape source7:=by constructor<;>decide+kernel
theorem middle7 (h:ℕ) (hh:h≤11):79≤(source7.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source7,Parameters.cutoff,
          AQ.reserve]
theorem CMX:
    AM.AW source7.cutoff 131071 628 25 11 79=32544010944169:=by
  decide+kernel
theorem rank7:AR.rankBound 58 628 25 11 79=124143749:=by decide+kernel
theorem dimension7:Dimension source7 472006313:=by
  exact AZ source7 472006313 32544010944169 124143749
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle7 CMX rank7 (by decide)
end EZ
end MergedPart1
section MergedPart2
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source8:Parameters:=⟨58,800,25,11,79,1,2⟩
theorem shape8:Shape source8:=by constructor<;>decide+kernel
theorem middle8 (h:ℕ) (hh:h≤11):79≤(source8.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source8,Parameters.cutoff,
          AQ.reserve]
theorem COE:
    AM.AW source8.cutoff 131071 800 25 11 79=41952125769889:=by
  decide+kernel
theorem rank8:AR.rankBound 58 800 25 11 79=159703717:=by decide+kernel
theorem dimension8:Dimension source8 86754580641:=by
  exact AZ source8 86754580641 41952125769889 159703717
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle8 COE rank8 (by decide)
def source9:Parameters:=⟨58,1000,25,11,79,1,2⟩
theorem shape9:Shape source9:=by constructor<;>decide+kernel
theorem middle9 (h:ℕ) (hh:h≤11):79≤(source9.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source9,Parameters.cutoff,
          AQ.reserve]
theorem COS:
    AM.AW source9.cutoff 131071 1000 25 11 79=52891794171889:=by
  decide+kernel
theorem rank9:AR.rankBound 58 1000 25 11 79=201052517:=by decide+kernel
theorem dimension9:Dimension source9 187083155441:=by
  exact AZ source9 187083155441 52891794171889 201052517
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle9 COS rank9 (by decide)
def source10:Parameters:=⟨58,1200,25,11,79,1,2⟩
theorem shape10:Shape source10:=by constructor<;>decide+kernel
theorem middle10 (h:ℕ) (hh:h≤11):79≤(source10.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source10,Parameters.cutoff,
          AQ.reserve]
theorem BVI:
    AM.AW source10.cutoff 131071 1200 25 11 79=63831462573889:=by
  decide+kernel
theorem rank10:AR.rankBound 58 1200 25 11 79=242401317:=by decide+kernel
theorem dimension10:Dimension source10 287411730241:=by
  exact AZ source10 287411730241 63831462573889 242401317
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle10 BVI rank10 (by decide)
def source11:Parameters:=⟨60,1000,25,12,82,1,2⟩
theorem shape11:Shape source11:=by constructor<;>decide+kernel
theorem middle11 (h:ℕ) (hh:h≤12):82≤(source11.cutoff h+25-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source11,Parameters.cutoff,
          AQ.reserve]
theorem BTL:
    AM.AW source11.cutoff 131071 1000 25 12 82=57836745872828:=by
  decide+kernel
theorem rank11:AR.rankBound 60 1000 25 12 82=219762148:=by decide+kernel
theorem dimension11:Dimension source11 227417347516:=by
  exact AZ source11 227417347516 57836745872828 219762148
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle11 BTL rank11 (by decide)
end EZ
end MergedPart2
section MergedPart3
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source12:Parameters:=⟨60,598,26,12,82,1,2⟩
theorem shape12:Shape source12:=by constructor<;>decide+kernel
theorem middle12 (h:ℕ) (hh:h≤12):82≤(source12.cutoff h+26-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source12,Parameters.cutoff,
          AQ.reserve]
theorem BSP:
    AM.AW source12.cutoff 131071 598 26 12 82=35671052990370:=by
  decide+kernel
theorem rank12:AR.rankBound 60 598 26 12 82=136072501:=by decide+kernel
theorem dimension12:Dimension source12 463288226:=by
  exact AZ source12 463288226 35671052990370 136072501
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle12 BSP rank12 (by decide)
def source13:Parameters:=⟨62,579,27,12,85,1,2⟩
theorem shape13:Shape source13:=by constructor<;>decide+kernel
theorem middle13 (h:ℕ) (hh:h≤12):85≤(source13.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source13,Parameters.cutoff,
          AQ.reserve]
theorem BYL:
    AM.AW source13.cutoff 131071 579 27 12 85=39093859867050:=by
  decide+kernel
theorem rank13:AR.rankBound 62 579 27 12 85=149129869:=by decide+kernel
theorem dimension13:Dimension source13 359487914:=by
  exact AZ source13 359487914 39093859867050 149129869
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle13 BYL rank13 (by decide)
def source14:Parameters:=⟨64,2220,26,11,87,2,3⟩
theorem shape14:Shape source14:=by constructor<;>decide+kernel
theorem middle14 (h:ℕ) (hh:h≤11):87≤(source14.cutoff h+26-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source14,Parameters.cutoff,
          AQ.reserve]
theorem BUT:
    AM.AW source14.cutoff 131071 2220 26 11 87=157081074719147:=by
  decide+kernel
theorem rank14:AR.rankBound 64 2220 26 11 87=598723817:=by decide+kernel
theorem dimension14:Dimension source14 129218435499:=by
  exact AZ source14 129218435499 157081074719147 598723817
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle14 BUT rank14 (by decide)
def source15:Parameters:=⟨64,2167,26,12,87,2,3⟩
theorem shape15:Shape source15:=by constructor<;>decide+kernel
theorem middle15 (h:ℕ) (hh:h≤12):87≤(source15.cutoff h+26-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source15,Parameters.cutoff,
          AQ.reserve]
theorem BZD:
    AM.AW source15.cutoff 131071 2167 26 12 87=155639786392334:=by
  decide+kernel
theorem rank15:AR.rankBound 64 2167 26 12 87=593244562:=by decide+kernel
theorem dimension15:Dimension source15 124283931406:=by
  exact AZ source15 124283931406 155639786392334 593244562
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle15 BZD rank15 (by decide)
end EZ
end MergedPart3
section MergedPart4
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source16:Parameters:=⟨66,2096,26,11,90,2,3⟩
theorem shape16:Shape source16:=by constructor<;>decide+kernel
theorem middle16 (h:ℕ) (hh:h≤11):90≤(source16.cutoff h+26-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source16,Parameters.cutoff,
          AQ.reserve]
theorem DKR:
    AM.AW source16.cutoff 131071 2096 26 11 90=159098450813179:=by
  decide+kernel
theorem rank16:AR.rankBound 66 2096 26 11 90=606301662:=by decide+kernel
theorem dimension16:Dimension source16 160107929851:=by
  exact AZ source16 160107929851 159098450813179 606301662
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle16 DKR rank16 (by decide)
def source17:Parameters:=⟨66,2052,26,12,90,2,3⟩
theorem shape17:Shape source17:=by constructor<;>decide+kernel
theorem middle17 (h:ℕ) (hh:h≤12):90≤(source17.cutoff h+26-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source17,Parameters.cutoff,
          AQ.reserve]
theorem DIR:
    AM.AW source17.cutoff 131071 2052 26 12 90=158108187856944:=by
  decide+kernel
theorem rank17:AR.rankBound 66 2052 26 12 90=602544606:=by decide+kernel
theorem dimension17:Dimension source17 154734661680:=by
  exact AZ source17 154734661680 158108187856944 602544606
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle17 DIR rank17 (by decide)
def source18:Parameters:=⟨66,1587,28,12,90,2,3⟩
theorem shape18:Shape source18:=by constructor<;>decide+kernel
theorem middle18 (h:ℕ) (hh:h≤12):90≤(source18.cutoff h+28-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source18,Parameters.cutoff,
          AQ.reserve]
theorem DIW:
    AM.AW source18.cutoff 131071 1587 28 12 90=134395175628245:=by
  decide+kernel
theorem rank18:AR.rankBound 66 1587 28 12 90=512363070:=by decide+kernel
theorem dimension18:Dimension source18 82271006165:=by
  exact AZ source18 82271006165 134395175628245 512363070
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle18 DIW rank18 (by decide)
def source19:Parameters:=⟨66,1376,28,14,90,2,3⟩
theorem shape19:Shape source19:=by constructor<;>decide+kernel
theorem middle19 (h:ℕ) (hh:h≤14):90≤(source19.cutoff h+28-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source19,Parameters.cutoff,
          AQ.reserve]
theorem DJR:
    AM.AW source19.cutoff 131071 1376 28 14 90=118172654079165:=by
  decide+kernel
theorem rank19:AR.rankBound 66 1376 28 14 90=450792645:=by decide+kernel
theorem dimension19:Dimension source19 66948285:=by
  exact AZ source19 66948285 118172654079165 450792645
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle19 DJR rank19 (by decide)
end EZ
end MergedPart4
section MergedPart5
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source20:Parameters:=⟨68,1373,27,13,93,2,3⟩
theorem shape20:Shape source20:=by constructor<;>decide+kernel
theorem middle20 (h:ℕ) (hh:h≤13):93≤(source20.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source20,Parameters.cutoff,
          AQ.reserve]
theorem DLE:
    AM.AW source20.cutoff 131071 1373 27 13 93=119413695941595:=by
  decide+kernel
theorem rank20:AR.rankBound 68 1373 27 13 93=455525715:=by decide+kernel
theorem dimension20:Dimension source20 362908635:=by
  exact AZ source20 362908635 119413695941595 455525715
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle20 DLE rank20 (by decide)
def source21:Parameters:=⟨68,1400,27,13,93,2,3⟩
theorem shape21:Shape source21:=by constructor<;>decide+kernel
theorem middle21 (h:ℕ) (hh:h≤13):93≤(source21.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source21,Parameters.cutoff,
          AQ.reserve]
theorem ETF:
    AM.AW source21.cutoff 131071 1400 27 13 93=121829218030512:=by
  decide+kernel
theorem rank21:AR.rankBound 68 1400 27 13 93=464694078:=by decide+kernel
theorem dimension21:Dimension source21 12453647280:=by
  exact AZ source21 12453647280 121829218030512 464694078
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle21 ETF rank21 (by decide)
def source22:Parameters:=⟨68,1500,27,13,93,2,3⟩
theorem shape22:Shape source22:=by constructor<;>decide+kernel
theorem middle22 (h:ℕ) (hh:h≤13):93≤(source22.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source22,Parameters.cutoff,
          AQ.reserve]
theorem GRS:
    AM.AW source22.cutoff 131071 1500 27 13 93=130775596137612:=by
  decide+kernel
theorem rank22:AR.rankBound 68 1500 27 13 93=498650978:=by decide+kernel
theorem dimension22:Dimension source22 57234160780:=by
  exact AZ source22 57234160780 130775596137612 498650978
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle22 GRS rank22 (by decide)
def source23:Parameters:=⟨68,1600,27,13,93,2,3⟩
theorem shape23:Shape source23:=by constructor<;>decide+kernel
theorem middle23 (h:ℕ) (hh:h≤13):93≤(source23.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source23,Parameters.cutoff,
          AQ.reserve]
theorem GMJ:
    AM.AW source23.cutoff 131071 1600 27 13 93=139721974244712:=by
  decide+kernel
theorem rank23:AR.rankBound 68 1600 27 13 93=532607878:=by decide+kernel
theorem dimension23:Dimension source23 102014674280:=by
  exact AZ source23 102014674280 139721974244712 532607878
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle23 GMJ rank23 (by decide)
end EZ
end MergedPart5
section MergedPart6
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source24:Parameters:=⟨68,1640,27,13,93,2,3⟩
theorem shape24:Shape source24:=by constructor<;>decide+kernel
theorem middle24 (h:ℕ) (hh:h≤13):93≤(source24.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source24,Parameters.cutoff,
          AQ.reserve]
theorem GNS:
    AM.AW source24.cutoff 131071 1640 27 13 93=143300525487552:=by
  decide+kernel
theorem rank24:AR.rankBound 68 1640 27 13 93=546190638:=by decide+kernel
theorem dimension24:Dimension source24 119926879680:=by
  exact AZ source24 119926879680 143300525487552 546190638
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle24 GNS rank24 (by decide)
def source25:Parameters:=⟨68,1680,27,13,93,2,3⟩
theorem shape25:Shape source25:=by constructor<;>decide+kernel
theorem middle25 (h:ℕ) (hh:h≤13):93≤(source25.cutoff h+27-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source25,Parameters.cutoff,
          AQ.reserve]
theorem GLG:
    AM.AW source25.cutoff 131071 1680 27 13 93=146879076730392:=by
  decide+kernel
theorem rank25:AR.rankBound 68 1680 27 13 93=559773398:=by decide+kernel
theorem dimension25:Dimension source25 137839085080:=by
  exact AZ source25 137839085080 146879076730392 559773398
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle25 GLG rank25 (by decide)
def source26:Parameters:=⟨68,1683,28,12,93,2,3⟩
theorem shape26:Shape source26:=by constructor<;>decide+kernel
theorem middle26 (h:ℕ) (hh:h≤12):93≤(source26.cutoff h+28-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source26,Parameters.cutoff,
          AQ.reserve]
theorem GMH:
    AM.AW source26.cutoff 131071 1683 28 12 93=152984695765589:=by
  decide+kernel
theorem rank26:AR.rankBound 68 1683 28 12 93=582826619:=by decide+kernel
theorem dimension26:Dimension source26 200194554453:=by
  exact AZ source26 200194554453 152984695765589 582826619
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle26 GMH rank26 (by decide)
def source27:Parameters:=⟨76,982,31,14,104,2,3⟩
theorem shape27:Shape source27:=by constructor<;>decide+kernel
theorem middle27 (h:ℕ) (hh:h≤14):104≤(source27.cutoff h+31-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source27,Parameters.cutoff,
          AQ.reserve]
theorem GKW:
    AM.AW source27.cutoff 131071 982 31 14 104=133694881346345:=by
  decide+kernel
theorem rank27:AR.rankBound 76 982 31 14 104=510001814:=by decide+kernel
theorem dimension27:Dimension source27 965817129:=by
  exact AZ source27 965817129 133694881346345 510001814
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle27 GKW rank27 (by decide)
end EZ
end MergedPart6
section MergedPart7
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source28:Parameters:=⟨76,940,32,15,104,2,3⟩
theorem shape28:Shape source28:=by constructor<;>decide+kernel
theorem middle28 (h:ℕ) (hh:h≤15):104≤(source28.cutoff h+32-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source28,Parameters.cutoff,
          AQ.reserve]
theorem GMO:
    AM.AW source28.cutoff 131071 940 32 15 104=134705376909802:=by
  decide+kernel
theorem rank28:AR.rankBound 76 940 32 15 104=513857981:=by decide+kernel
theorem dimension28:Dimension source28 590338538:=by
  exact AZ source28 590338538 134705376909802 513857981
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle28 GMO rank28 (by decide)
def source29:Parameters:=⟨76,917,34,15,104,2,3⟩
theorem shape29:Shape source29:=by constructor<;>decide+kernel
theorem middle29 (h:ℕ) (hh:h≤15):104≤(source29.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source29,Parameters.cutoff,
          AQ.reserve]
theorem GJA:
    AM.AW source29.cutoff 131071 917 34 15 104=142598071339232:=by
  decide+kernel
theorem rank29:AR.rankBound 76 917 34 15 104=543963929:=by decide+kernel
theorem dimension29:Dimension source29 1191135456:=by
  exact AZ source29 1191135456 142598071339232 543963929
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle29 GJA rank29 (by decide)
def source30:Parameters:=⟨76,913,34,16,104,2,3⟩
theorem shape30:Shape source30:=by constructor<;>decide+kernel
theorem middle30 (h:ℕ) (hh:h≤16):104≤(source30.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source30,Parameters.cutoff,
          AQ.reserve]
theorem GSU:
    AM.AW source30.cutoff 131071 913 34 16 104=143261369068301:=by
  decide+kernel
theorem rank30:AR.rankBound 76 913 34 16 104=546498068:=by decide+kernel
theorem dimension30:Dimension source30 179530509:=by
  exact AZ source30 179530509 143261369068301 546498068
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle30 GSU rank30 (by decide)
def source31:Parameters:=⟨78,883,34,15,107,2,3⟩
theorem shape31:Shape source31:=by constructor<;>decide+kernel
theorem middle31 (h:ℕ) (hh:h≤15):107≤(source31.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source31,Parameters.cutoff,
          AQ.reserve]
theorem GRF:
    AM.AW source31.cutoff 131071 883 34 15 107=145571774513948:=by
  decide+kernel
theorem rank31:AR.rankBound 78 883 34 15 107=555311479:=by decide+kernel
theorem dimension31:Dimension source31 202162972:=by
  exact AZ source31 202162972 145571774513948 555311479
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle31 GRF rank31 (by decide)
end EZ
end MergedPart7
section MergedPart8
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source32:Parameters:=⟨78,881,34,16,107,2,3⟩
theorem shape32:Shape source32:=by constructor<;>decide+kernel
theorem middle32 (h:ℕ) (hh:h≤16):107≤(source32.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source32,Parameters.cutoff,
          AQ.reserve]
theorem GPY:
    AM.AW source32.cutoff 131071 881 34 16 107=146572116790381:=by
  decide+kernel
theorem rank32:AR.rankBound 78 881 34 16 107=559123621:=by decide+kernel
theorem dimension32:Dimension source32 1214286957:=by
  exact AZ source32 1214286957 146572116790381 559123621
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle32 GPY rank32 (by decide)
def source33:Parameters:=⟨80,869,34,15,109,2,3⟩
theorem shape33:Shape source33:=by constructor<;>decide+kernel
theorem middle33 (h:ℕ) (hh:h≤15):109≤(source33.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source33,Parameters.cutoff,
          AQ.reserve]
theorem GLS:
    AM.AW source33.cutoff 131071 869 34 15 109=151765953371070:=by
  decide+kernel
theorem rank33:AR.rankBound 80 869 34 15 109=578936775:=by decide+kernel
theorem dimension33:Dimension source33 1151425470:=by
  exact AZ source33 1151425470 151765953371070 578936775
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle33 GLS rank33 (by decide)
def source34:Parameters:=⟨80,2375,34,15,109,3,4⟩
theorem shape34:Shape source34:=by constructor<;>decide+kernel
theorem middle34 (h:ℕ) (hh:h≤15):109≤(source34.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source34,Parameters.cutoff,
          AQ.reserve]
theorem GJH:
    AM.AW source34.cutoff 131071 2375 34 15 109=427057385929506:=by
  decide+kernel
theorem rank34:AR.rankBound 80 2375 34 15 109=1628406429:=by decide+kernel
theorem dimension34:Dimension source34 180411005730:=by
  exact AZ source34 180411005730 427057385929506 1628406429
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle34 GJH rank34 (by decide)
def source35:Parameters:=⟨80,867,34,16,109,2,3⟩
theorem shape35:Shape source35:=by constructor<;>decide+kernel
theorem middle35 (h:ℕ) (hh:h≤16):109≤(source35.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source35,Parameters.cutoff,
          AQ.reserve]
theorem GNH:
    AM.AW source35.cutoff 131071 867 34 16 109=152802915039751:=by
  decide+kernel
theorem rank35:AR.rankBound 80 867 34 16 109=582890484:=by decide+kernel
theorem dimension35:Dimension source35 1672002055:=by
  exact AZ source35 1672002055 152802915039751 582890484
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle35 GNH rank35 (by decide)
end EZ
end MergedPart8
section MergedPart9
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source36:Parameters:=⟨82,2232,34,15,112,3,4⟩
theorem shape36:Shape source36:=by constructor<;>decide+kernel
theorem middle36 (h:ℕ) (hh:h≤15):112≤(source36.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source36,Parameters.cutoff,
          AQ.reserve]
theorem GQV:
    AM.AW source36.cutoff 131071 2232 34 15 112=424644082194670:=by
  decide+kernel
theorem rank36:AR.rankBound 82 2232 34 15 112=1618876085:=by decide+kernel
theorem dimension36:Dimension source36 265429768430:=by
  exact AZ source36 265429768430 424644082194670 1618876085
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle36 GQV rank36 (by decide)
def source37:Parameters:=⟨82,825,36,16,112,2,3⟩
theorem shape37:Shape source37:=by constructor<;>decide+kernel
theorem middle37 (h:ℕ) (hh:h≤16):112≤(source37.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source37,Parameters.cutoff,
          AQ.reserve]
theorem GKL:
    AM.AW source37.cutoff 131071 825 36 16 112=166105894539459:=by
  decide+kernel
theorem rank37:AR.rankBound 82 825 36 16 112=633636570:=by decide+kernel
theorem dimension37:Dimension source37 1869533379:=by
  exact AZ source37 1869533379 166105894539459 633636570
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle37 GKL rank37 (by decide)
def source38:Parameters:=⟨82,2103,36,16,112,3,4⟩
theorem shape38:Shape source38:=by constructor<;>decide+kernel
theorem middle38 (h:ℕ) (hh:h≤16):112≤(source38.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source38,Parameters.cutoff,
          AQ.reserve]
theorem GKN:
    AM.AW source38.cutoff 131071 2103 36 16 112=436655641292013:=by
  decide+kernel
theorem rank38:AR.rankBound 82 2103 36 16 112=1664811318:=by decide+kernel
theorem dimension38:Dimension source38 235343146221:=by
  exact AZ source38 235343146221 436655641292013 1664811318
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle38 GKN rank38 (by decide)
def source39:Parameters:=⟨84,2213,34,15,115,3,4⟩
theorem shape39:Shape source39:=by constructor<;>decide+kernel
theorem middle39 (h:ℕ) (hh:h≤15):115≤(source39.cutoff h+34-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source39,Parameters.cutoff,
          AQ.reserve]
theorem GMP:
    AM.AW source39.cutoff 131071 2213 34 15 115=445218340154382:=by
  decide+kernel
theorem rank39:AR.rankBound 84 2213 34 15 115=1696905609:=by decide+kernel
theorem dimension39:Dimension source39 384716188686:=by
  exact AZ source39 384716188686 445218340154382 1696905609
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle39 GMP rank39 (by decide)
end EZ
end MergedPart9
section MergedPart10
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source40:Parameters:=⟨84,1664,36,16,115,3,4⟩
theorem shape40:Shape source40:=by constructor<;>decide+kernel
theorem middle40 (h:ℕ) (hh:h≤16):115≤(source40.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source40,Parameters.cutoff,
          AQ.reserve]
theorem GLH:
    AM.AW source40.cutoff 131071 1664 36 16 115=363347219182981:=by
  decide+kernel
theorem rank40:AR.rankBound 84 1664 36 16 115=1386056672:=by decide+kernel
theorem dimension40:Dimension source40 778958213:=by
  exact AZ source40 778958213 363347219182981 1386056672
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle40 GLH rank40 (by decide)
def source41:Parameters:=⟨84,1902,36,16,115,3,4⟩
theorem shape41:Shape source41:=by constructor<;>decide+kernel
theorem middle41 (h:ℕ) (hh:h≤16):115≤(source41.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source41,Parameters.cutoff,
          AQ.reserve]
theorem GNB:
    AM.AW source41.cutoff 131071 1902 36 16 115=416868415574273:=by
  decide+kernel
theorem rank41:AR.rankBound 84 1902 36 16 115=1589225610:=by decide+kernel
theorem dimension41:Dimension source41 262457266433:=by
  exact AZ source41 262457266433 416868415574273 1589225610
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle41 GNB rank41 (by decide)
def source42:Parameters:=⟨84,2138,36,16,115,3,4⟩
theorem shape42:Shape source42:=by constructor<;>decide+kernel
theorem middle42 (h:ℕ) (hh:h≤16):115≤(source42.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source42,Parameters.cutoff,
          AQ.reserve]
theorem GOC:
    AM.AW source42.cutoff 131071 2138 36 16 115=469939854012697:=by
  decide+kernel
theorem rank42:AR.rankBound 84 2138 36 16 115=1790687246:=by decide+kernel
theorem dimension42:Dimension source42 521936597273:=by
  exact AZ source42 521936597273 469939854012697 1790687246
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle42 GOC rank42 (by decide)
def source43:Parameters:=⟨84,2131,36,17,115,3,4⟩
theorem shape43:Shape source43:=by constructor<;>decide+kernel
theorem middle43 (h:ℕ) (hh:h≤17):115≤(source43.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source43,Parameters.cutoff,
          AQ.reserve]
theorem GOK:
    AM.AW source43.cutoff 131071 2131 36 17 115=472257195087276:=by
  decide+kernel
theorem rank43:AR.rankBound 84 2131 36 17 115=1799540541:=by decide+kernel
theorem dimension43:Dimension source43 518439507372:=by
  exact AZ source43 518439507372 472257195087276 1799540541
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle43 GOK rank43 (by decide)
end EZ
end MergedPart10
section MergedPart11
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source44:Parameters:=⟨84,2259,36,17,115,3,4⟩
theorem shape44:Shape source44:=by constructor<;>decide+kernel
theorem middle44 (h:ℕ) (hh:h≤17):115≤(source44.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source44,Parameters.cutoff,
          AQ.reserve]
theorem GRB:
    AM.AW source44.cutoff 131071 2259 36 17 115=501280949560236:=by
  decide+kernel
theorem rank44:AR.rankBound 84 2259 36 17 115=1909716285:=by decide+kernel
theorem dimension44:Dimension source44 660283745196:=by
  exact AZ source44 660283745196 501280949560236 1909716285
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle44 GRB rank44 (by decide)
def source45:Parameters:=⟨85,799,37,17,116,2,3⟩
theorem shape45:Shape source45:=by constructor<;>decide+kernel
theorem middle45 (h:ℕ) (hh:h≤17):116≤(source45.cutoff h+37-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source45,Parameters.cutoff,
          AQ.reserve]
theorem GOG:
    AM.AW source45.cutoff 131071 799 37 17 116=182805643525992:=by
  decide+kernel
theorem rank45:AR.rankBound 85 799 37 17 116=697340658:=by decide+kernel
theorem dimension45:Dimension source45 1974075240:=by
  exact AZ source45 1974075240 182805643525992 697340658
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle45 GOG rank45 (by decide)
def source46:Parameters:=⟨86,2117,36,16,117,3,4⟩
theorem shape46:Shape source46:=by constructor<;>decide+kernel
theorem middle46 (h:ℕ) (hh:h≤16):117≤(source46.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source46,Parameters.cutoff,
          AQ.reserve]
theorem GQQ:
    AM.AW source46.cutoff 131071 2117 36 16 117=491517334713762:=by
  decide+kernel
theorem rank46:AR.rankBound 86 2117 36 16 117=1872282170:=by decide+kernel
theorem dimension46:Dimension source46 709797541282:=by
  exact AZ source46 709797541282 491517334713762 1872282170
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle46 GQQ rank46 (by decide)
def source47:Parameters:=⟨86,2108,36,17,117,3,4⟩
theorem shape47:Shape source47:=by constructor<;>decide+kernel
theorem middle47 (h:ℕ) (hh:h≤17):117≤(source47.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source47,Parameters.cutoff,
          AQ.reserve]
theorem GRC:
    AM.AW source47.cutoff 131071 2108 36 17 117=493446182526171:=by
  decide+kernel
theorem rank47:AR.rankBound 86 2108 36 17 117=1879663641:=by decide+kernel
theorem dimension47:Dimension source47 703637019867:=by
  exact AZ source47 703637019867 493446182526171 1879663641
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle47 GRC rank47 (by decide)
end EZ
end MergedPart11
section MergedPart12
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source48:Parameters:=⟨86,1968,38,17,117,3,4⟩
theorem shape48:Shape source48:=by constructor<;>decide+kernel
theorem middle48 (h:ℕ) (hh:h≤17):117≤(source48.cutoff h+38-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source48,Parameters.cutoff,
          AQ.reserve]
theorem GLI:
    AM.AW source48.cutoff 131071 1968 38 17 117=496035317046120:=by
  decide+kernel
theorem rank48:AR.rankBound 86 1968 38 17 117=1889829174:=by decide+kernel
theorem dimension48:Dimension source48 627938057064:=by
  exact AZ source48 627938057064 496035317046120 1889829174
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle48 GLI rank48 (by decide)
def source49:Parameters:=⟨87,783,38,17,119,2,3⟩
theorem shape49:Shape source49:=by constructor<;>decide+kernel
theorem middle49 (h:ℕ) (hh:h≤17):119≤(source49.cutoff h+38-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source49,Parameters.cutoff,
          AQ.reserve]
theorem GLO:
    AM.AW source49.cutoff 131071 783 38 17 119=195789073722486:=by
  decide+kernel
theorem rank49:AR.rankBound 87 783 38 17 119=746872443:=by decide+kernel
theorem dimension49:Dimension source49 944024694:=by
  exact AZ source49 944024694 195789073722486 746872443
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle49 GLO rank49 (by decide)
def source50:Parameters:=⟨87,1460,38,17,119,3,4⟩
theorem shape50:Shape source50:=by constructor<;>decide+kernel
theorem middle50 (h:ℕ) (hh:h≤17):119≤(source50.cutoff h+38-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source50,Parameters.cutoff,
          AQ.reserve]
theorem GSV:
    AM.AW source50.cutoff 131071 1460 38 17 119=374692558954578:=by
  decide+kernel
theorem rank50:AR.rankBound 87 1460 38 17 119=1429335156:=by decide+kernel
theorem dimension50:Dimension source50 923820114:=by
  exact AZ source50 923820114 374692558954578 1429335156
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle50 GSV rank50 (by decide)
def source51:Parameters:=⟨88,1895,36,17,120,3,4⟩
theorem shape51:Shape source51:=by constructor<;>decide+kernel
theorem middle51 (h:ℕ) (hh:h≤17):120≤(source51.cutoff h+36-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source51,Parameters.cutoff,
          AQ.reserve]
theorem GLB:
    AM.AW source51.cutoff 131071 1895 36 17 120=466701469574106:=by
  decide+kernel
theorem rank51:AR.rankBound 88 1895 36 17 120=1778166957:=by decide+kernel
theorem dimension51:Dimension source51 565670798298:=by
  exact AZ source51 565670798298 466701469574106 1778166957
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle51 GLB rank51 (by decide)
end EZ
end MergedPart12
section MergedPart13
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source52:Parameters:=⟨90,1330,39,18,123,3,4⟩
theorem shape52:Shape source52:=by constructor<;>decide+kernel
theorem middle52 (h:ℕ) (hh:h≤18):123≤(source52.cutoff h+39-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source52,Parameters.cutoff,
          AQ.reserve]
theorem GPE:
    AM.AW source52.cutoff 131071 1330 39 18 123=384855991026523:=by
  decide+kernel
theorem rank52:AR.rankBound 90 1330 39 18 123=1468106200:=by decide+kernel
theorem dimension52:Dimension source52 759333723:=by
  exact AZ source52 759333723 384855991026523 1468106200
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle52 GPE rank52 (by decide)
def source53:Parameters:=⟨92,1638,38,17,126,3,4⟩
theorem shape53:Shape source53:=by constructor<;>decide+kernel
theorem middle53 (h:ℕ) (hh:h≤17):126≤(source53.cutoff h+38-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source53,Parameters.cutoff,
          AQ.reserve]
theorem GLW:
    AM.AW source53.cutoff 131071 1638 38 17 126=480725054973051:=by
  decide+kernel
theorem rank53:AR.rankBound 92 1638 38 17 126=1831370378:=by decide+kernel
theorem dimension53:Dimension source53 642298602619:=by
  exact AZ source53 642298602619 480725054973051 1831370378
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle53 GLW rank53 (by decide)
def source54:Parameters:=⟨92,746,42,19,126,2,3⟩
theorem shape54:Shape source54:=by constructor<;>decide+kernel
theorem middle54 (h:ℕ) (hh:h≤19):126≤(source54.cutoff h+42-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source54,Parameters.cutoff,
          AQ.reserve]
theorem GKJ:
    AM.AW source54.cutoff 131071 746 42 19 126=246628385418597:=by
  decide+kernel
theorem rank54:AR.rankBound 92 746 42 19 126=940801461:=by decide+kernel
theorem dimension54:Dimension source54 2927226213:=by
  exact AZ source54 2927226213 246628385418597 940801461
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle54 GKJ rank54 (by decide)
def source55:Parameters:=⟨94,1209,41,19,128,3,4⟩
theorem shape55:Shape source55:=by constructor<;>decide+kernel
theorem middle55 (h:ℕ) (hh:h≤19):128≤(source55.cutoff h+41-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source55,Parameters.cutoff,
          AQ.reserve]
theorem GOB:
    AM.AW source55.cutoff 131071 1209 41 19 128=416454642035929:=by
  decide+kernel
theorem rank55:AR.rankBound 94 1209 41 19 128=1588643629:=by decide+kernel
theorem dimension55:Dimension source55 1246555353:=by
  exact AZ source55 1246555353 416454642035929 1588643629
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle55 GOB rank55 (by decide)
end EZ
end MergedPart13
section MergedPart14
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source56:Parameters:=⟨98,1123,43,20,134,3,4⟩
theorem shape56:Shape source56:=by constructor<;>decide+kernel
theorem middle56 (h:ℕ) (hh:h≤20):134≤(source56.cutoff h+43-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source56,Parameters.cutoff,
          AQ.reserve]
theorem GNC:
    AM.AW source56.cutoff 131071 1123 43 20 134=457044715719196:=by
  decide+kernel
theorem rank56:AR.rankBound 98 1123 43 20 134=1743478281:=by decide+kernel
theorem dimension56:Dimension source56 2345224732:=by
  exact AZ source56 2345224732 457044715719196 1743478281
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle56 GNC rank56 (by decide)
def source57:Parameters:=⟨100,2306,42,19,136,4,5⟩
theorem shape57:Shape source57:=by constructor<;>decide+kernel
theorem middle57 (h:ℕ) (hh:h≤19):136≤(source57.cutoff h+42-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source57,Parameters.cutoff,
          AQ.reserve]
theorem GSW:
    AM.AW source57.cutoff 131071 2306 42 19 136=966858756020051:=by
  decide+kernel
theorem rank57:AR.rankBound 100 2306 42 19 136=3687036866:=by decide+kernel
theorem dimension57:Dimension source57 324163819347:=by
  exact AZ source57 324163819347 966858756020051 3687036866
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle57 GSW rank57 (by decide)
def source58:Parameters:=⟨102,1064,45,21,139,3,4⟩
theorem shape58:Shape source58:=by constructor<;>decide+kernel
theorem middle58 (h:ℕ) (hh:h≤21):139≤(source58.cutoff h+45-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source58,Parameters.cutoff,
          AQ.reserve]
theorem GKK:
    AM.AW source58.cutoff 131071 1064 45 21 139=508212786890492:=by
  decide+kernel
theorem rank58:AR.rankBound 102 1064 45 21 139=1938665963:=by decide+kernel
theorem dimension58:Dimension source58 3136685820:=by
  exact AZ source58 3136685820 508212786890492 1938665963
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle58 GKK rank58 (by decide)
def source59:Parameters:=⟨108,1014,47,21,148,3,4⟩
theorem shape59:Shape source59:=by constructor<;>decide+kernel
theorem middle59 (h:ℕ) (hh:h≤21):148≤(source59.cutoff h+47-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source59,Parameters.cutoff,
          AQ.reserve]
theorem GKI:
    AM.AW source59.cutoff 131071 1014 47 21 148=585751086172302:=by
  decide+kernel
theorem rank59:AR.rankBound 108 1014 47 21 148=2234451580:=by decide+kernel
theorem dimension59:Dimension source59 3011184782:=by
  exact AZ source59 3011184782 585751086172302 2234451580
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle59 GKI rank59 (by decide)
end EZ
end MergedPart14
section MergedPart15
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source60:Parameters:=⟨112,3686,45,20,152,5,6⟩
theorem shape60:Shape source60:=by constructor<;>decide+kernel
theorem middle60 (h:ℕ) (hh:h≤20):152≤(source60.cutoff h+45-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source60,Parameters.cutoff,
          AQ.reserve]
theorem GPC:
    AM.AW source60.cutoff 131071 3686 45 20 152=2250003094304000:=by
  decide+kernel
theorem rank60:AR.rankBound 112 3686 45 20 152=8581076106:=by decide+kernel
theorem dimension60:Dimension source60 525479572736:=by
  exact AZ source60 525479572736 2250003094304000 8581076106
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle60 GPC rank60 (by decide)
def source61:Parameters:=⟨113,3378,46,21,153,5,6⟩
theorem shape61:Shape source61:=by constructor<;>decide+kernel
theorem middle61 (h:ℕ) (hh:h≤21):153≤(source61.cutoff h+46-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source61,Parameters.cutoff,
          AQ.reserve]
theorem GJN:
    AM.AW source61.cutoff 131071 3378 46 21 153=2185124418683662:=by
  decide+kernel
theorem rank61:AR.rankBound 113 3378 46 21 153=8333726260:=by decide+kernel
theorem dimension61:Dimension source61 488081982222:=by
  exact AZ source61 488081982222 2185124418683662 8333726260
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle61 GJN rank61 (by decide)
def source62:Parameters:=⟨114,3146,47,21,154,5,6⟩
theorem shape62:Shape source62:=by constructor<;>decide+kernel
theorem middle62 (h:ℕ) (hh:h≤21):154≤(source62.cutoff h+47-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source62,Parameters.cutoff,
          AQ.reserve]
theorem GRW:
    AM.AW source62.cutoff 131071 3146 47 21 154=2138048866468915:=by
  decide+kernel
theorem rank62:AR.rankBound 114 3146 47 21 154=8154240246:=by decide+kernel
theorem dimension62:Dimension source62 463711421491:=by
  exact AZ source62 463711421491 2138048866468915 8154240246
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle62 GRW rank62 (by decide)
def source63:Parameters:=⟨120,1405,54,25,164,4,5⟩
theorem shape63:Shape source63:=by constructor<;>decide+kernel
theorem middle63 (h:ℕ) (hh:h≤25):164≤(source63.cutoff h+54-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source63,Parameters.cutoff,
          AQ.reserve]
theorem GLA:
    AM.AW source63.cutoff 131071 1405 54 25 164=1311207354956943:=by
  decide+kernel
theorem rank63:AR.rankBound 120 1405 54 25 164=4999133419:=by decide+kernel
theorem dimension63:Dimension source63 714523966607:=by
  exact AZ source63 714523966607 1311207354956943 4999133419
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle63 GLA rank63 (by decide)
end EZ
end MergedPart15
section MergedPart16
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source64:Parameters:=⟨128,3734,53,24,174,6,7⟩
theorem shape64:Shape source64:=by constructor<;>decide+kernel
theorem middle64 (h:ℕ) (hh:h≤24):174≤(source64.cutoff h+53-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source64,Parameters.cutoff,
          AQ.reserve]
theorem GQC:
    AM.AW source64.cutoff 131071 3734 53 24 174=4029639517955012:=by
  decide+kernel
theorem rank64:AR.rankBound 128 3734 53 24 174=15369613990:=by decide+kernel
theorem dimension64:Dimension source64 587428160452:=by
  exact AZ source64 587428160452 4029639517955012 15369613990
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle64 GQC rank64 (by decide)
def source65:Parameters:=⟨129,3680,53,25,175,6,7⟩
theorem shape65:Shape source65:=by constructor<;>decide+kernel
theorem middle65 (h:ℕ) (hh:h≤25):175≤(source65.cutoff h+53-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source65,Parameters.cutoff,
          AQ.reserve]
theorem GKG:
    AM.AW source65.cutoff 131071 3680 53 25 175=4064321179557964:=by
  decide+kernel
theorem rank65:AR.rankBound 129 3680 53 25 175=15501968380:=by decide+kernel
theorem dimension65:Dimension source65 573180551244:=by
  exact AZ source65 573180551244 4064321179557964 15501968380
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle65 GKG rank65 (by decide)
def source66:Parameters:=⟨130,3618,53,24,176,6,7⟩
theorem shape66:Shape source66:=by constructor<;>decide+kernel
theorem middle66 (h:ℕ) (hh:h≤24):176≤(source66.cutoff h+53-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source66,Parameters.cutoff,
          AQ.reserve]
theorem GRH:
    AM.AW source66.cutoff 131071 3618 53 24 176=4045700360688751:=by
  decide+kernel
theorem rank66:AR.rankBound 130 3618 53 24 176=15430961278:=by decide+kernel
theorem dimension66:Dimension source66 566447428719:=by
  exact AZ source66 566447428719 4045700360688751 15430961278
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle66 GRH rank66 (by decide)
def source67:Parameters:=⟨130,3543,53,24,177,6,7⟩
theorem shape67:Shape source67:=by constructor<;>decide+kernel
theorem middle67 (h:ℕ) (hh:h≤24):177≤(source67.cutoff h+53-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source67,Parameters.cutoff,
          AQ.reserve]
theorem GPR:
    AM.AW source67.cutoff 131071 3543 53 24 177=3960401139331784:=by
  decide+kernel
theorem rank67:AR.rankBound 130 3543 53 24 177=15105604012:=by decide+kernel
theorem dimension67:Dimension source67 557681210056:=by
  exact AZ source67 557681210056 3960401139331784 15105604012
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle67 GPR rank67 (by decide)
end EZ
end MergedPart16
section MergedPart17
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source68:Parameters:=⟨140,1238,58,27,192,4,5⟩
theorem shape68:Shape source68:=by constructor<;>decide+kernel
theorem middle68 (h:ℕ) (hh:h≤27):192≤(source68.cutoff h+58-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source68,Parameters.cutoff,
          AQ.reserve]
theorem GMG:
    AM.AW source68.cutoff 131071 1238 58 27 192=1833111051290417:=by
  decide+kernel
theorem rank68:AR.rankBound 140 1238 58 27 192=6992695342:=by decide+kernel
theorem dimension68:Dimension source68 17923557169:=by
  exact AZ source68 17923557169 1833111051290417 6992695342
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle68 GMG rank68 (by decide)
def source69:Parameters:=⟨140,1238,58,27,192,4,5⟩
theorem shape69:Shape source69:=by constructor<;>decide+kernel
theorem middle69 (h:ℕ) (hh:h≤27):192≤(source69.cutoff h+58-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source69,Parameters.cutoff,
          AQ.reserve]
theorem GMV:
    AM.AW source69.cutoff 131071 1238 58 27 192=1833111051290417:=by
  decide+kernel
theorem rank69:AR.rankBound 140 1238 58 27 192=6992695342:=by decide+kernel
theorem dimension69:Dimension source69 17923557169:=by
  exact AZ source69 17923557169 1833111051290417 6992695342
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle69 GMV rank69 (by decide)
def source70:Parameters:=⟨140,1190,60,28,192,4,5⟩
theorem shape70:Shape source70:=by constructor<;>decide+kernel
theorem middle70 (h:ℕ) (hh:h≤28):192≤(source70.cutoff h+60-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source70,Parameters.cutoff,
          AQ.reserve]
theorem GOR:
    AM.AW source70.cutoff 131071 1190 60 28 192=1853549991733680:=by
  decide+kernel
theorem rank70:AR.rankBound 140 1190 60 28 192=7070673495:=by decide+kernel
theorem dimension70:Dimension source70 15359060400:=by
  exact AZ source70 15359060400 1853549991733680 7070673495
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle70 GOR rank70 (by decide)
def source71:Parameters:=⟨140,1190,60,28,192,4,5⟩
theorem shape71:Shape source71:=by constructor<;>decide+kernel
theorem middle71 (h:ℕ) (hh:h≤28):192≤(source71.cutoff h+60-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source71,Parameters.cutoff,
          AQ.reserve]
theorem GJQ:
    AM.AW source71.cutoff 131071 1190 60 28 192=1853549991733680:=by
  decide+kernel
theorem rank71:AR.rankBound 140 1190 60 28 192=7070673495:=by decide+kernel
theorem dimension71:Dimension source71 15359060400:=by
  exact AZ source71 15359060400 1853549991733680 7070673495
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle71 GJQ rank71 (by decide)
end EZ
end MergedPart17
section MergedPart18
namespace EZ
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def source72:Parameters:=⟨140,1190,60,28,192,4,5⟩
theorem shape72:Shape source72:=by constructor<;>decide+kernel
theorem middle72 (h:ℕ) (hh:h≤28):192≤(source72.cutoff h+60-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source72,Parameters.cutoff,
          AQ.reserve]
theorem GKZ:
    AM.AW source72.cutoff 131071 1190 60 28 192=1853549991733680:=by
  decide+kernel
theorem rank72:AR.rankBound 140 1190 60 28 192=7070673495:=by decide+kernel
theorem dimension72:Dimension source72 15359060400:=by
  exact AZ source72 15359060400 1853549991733680 7070673495
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle72 GKZ rank72 (by decide)
def source73:Parameters:=⟨140,1161,62,29,192,4,5⟩
theorem shape73:Shape source73:=by constructor<;>decide+kernel
theorem middle73 (h:ℕ) (hh:h≤29):192≤(source73.cutoff h+62-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source73,Parameters.cutoff,
          AQ.reserve]
theorem GPA:
    AM.AW source73.cutoff 131071 1161 62 29 192=1900054032997360:=by
  decide+kernel
theorem rank73:AR.rankBound 140 1161 62 29 192=7248071031:=by decide+kernel
theorem dimension73:Dimension source73 15700646896:=by
  exact AZ source73 15700646896 1900054032997360 7248071031
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle73 GPA rank73 (by decide)
def source74:Parameters:=⟨160,1128,70,33,219,4,5⟩
theorem shape74:Shape source74:=by constructor<;>decide+kernel
theorem middle74 (h:ℕ) (hh:h≤33):219≤(source74.cutoff h+70-1)/131071:=by
  interval_cases h<;>
    first
      | decide
      | norm_num [source74,Parameters.cutoff,
          AQ.reserve]
theorem GQS:
    AM.AW source74.cutoff 131071 1128 70 33 219=3029363482064731:=by
  decide+kernel
theorem rank74:AR.rankBound 160 1128 70 33 219=11555967880:=by decide+kernel
theorem dimension74:Dimension source74 35838130011:=by
  exact AZ source74 35838130011 3029363482064731 11555967880
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle74 GQS rank74 (by decide)
end EZ
end MergedPart18

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BED
open FF
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000

def e0:Parameters:=⟨66,1584,26,12,90,2,3⟩
theorem shape_e0:Shape e0:=by constructor<;>decide+kernel
theorem middle_e0 (h:ℕ) (hh:h≤12):90≤(e0.cutoff h+26-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e0,Parameters.cutoff,AQ.reserve]
theorem GFY:AM.AW e0.cutoff 131071 1584 26 12 90=121386345430584:=by decide+kernel
theorem rank_e0:AR.rankBound 66 1584 26 12 90=463051122:=by decide+kernel
theorem dimension_e0:Dimension e0 272105016:=by
  exact AZ e0 272105016 121386345430584 463051122
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e0 GFY rank_e0 (by decide)

def e1:Parameters:=⟨48,1105,20,9,65,1,2⟩
theorem shape_e1:Shape e1:=by constructor<;>decide+kernel
theorem middle_e1 (h:ℕ) (hh:h≤9):65≤(e1.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e1,Parameters.cutoff,AQ.reserve]
theorem GIU:AM.AW e1.cutoff 131071 1105 20 9 65=27287081368745:=by decide+kernel
theorem rank_e1:AR.rankBound 48 1105 20 9 65=104071541:=by decide+kernel
theorem dimension_e1:Dimension e1 5351324841:=by
  exact AZ e1 5351324841 27287081368745 104071541
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e1 GIU rank_e1 (by decide)

def e2:Parameters:=⟨48,1101,20,9,65,1,2⟩
theorem shape_e2:Shape e2:=by constructor<;>decide+kernel
theorem middle_e2 (h:ℕ) (hh:h≤9):65≤(e2.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e2,Parameters.cutoff,AQ.reserve]
theorem GIO:AM.AW e2.cutoff 131071 1101 20 9 65=27185842044801:=by decide+kernel
theorem rank_e2:AR.rankBound 48 1101 20 9 65=103687057:=by decide+kernel
theorem dimension_e2:Dimension e2 4902174593:=by
  exact AZ e2 4902174593 27185842044801 103687057
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e2 GIO rank_e2 (by decide)

def e3:Parameters:=⟨52,1051,22,10,71,1,2⟩
theorem shape_e3:Shape e3:=by constructor<;>decide+kernel
theorem middle_e3 (h:ℕ) (hh:h≤10):71≤(e3.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e3,Parameters.cutoff,AQ.reserve]
theorem GFX:AM.AW e3.cutoff 131071 1051 22 10 71=35950788776328:=by decide+kernel
theorem rank_e3:AR.rankBound 52 1051 22 10 71=136897912:=by decide+kernel
theorem dimension_e3:Dimension e3 63822533000:=by
  exact AZ e3 63822533000 35950788776328 136897912
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e3 GFX rank_e3 (by decide)

def e4:Parameters:=⟨68,1538,27,13,93,2,3⟩
theorem shape_e4:Shape e4:=by constructor<;>decide+kernel
theorem middle_e4 (h:ℕ) (hh:h≤13):93≤(e4.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e4,Parameters.cutoff,AQ.reserve]
theorem GFV:AM.AW e4.cutoff 131071 1538 27 13 93=134175219818310:=by decide+kernel
theorem rank_e4:AR.rankBound 68 1538 27 13 93=511554600:=by decide+kernel
theorem dimension_e4:Dimension e4 74250755910:=by
  exact AZ e4 74250755910 134175219818310 511554600
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e4 GFV rank_e4 (by decide)

def e5:Parameters:=⟨52,982,22,10,71,1,2⟩
theorem shape_e5:Shape e5:=by constructor<;>decide+kernel
theorem middle_e5 (h:ℕ) (hh:h≤10):71≤(e5.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e5,Parameters.cutoff,AQ.reserve]
theorem GID:AM.AW e5.cutoff 131071 982 22 10 71=33522770488437:=by decide+kernel
theorem rank_e5:AR.rankBound 52 982 22 10 71=127696831:=by decide+kernel
theorem dimension_e5:Dimension e5 47812422773:=by
  exact AZ e5 47812422773 33522770488437 127696831
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e5 GID rank_e5 (by decide)

def e6:Parameters:=⟨68,1505,27,13,93,2,3⟩
theorem shape_e6:Shape e6:=by constructor<;>decide+kernel
theorem middle_e6 (h:ℕ) (hh:h≤13):93≤(e6.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e6,Parameters.cutoff,AQ.reserve]
theorem GGL:AM.AW e6.cutoff 131071 1505 27 13 93=131222915042967:=by decide+kernel
theorem rank_e6:AR.rankBound 68 1505 27 13 93=500348823:=by decide+kernel
theorem dimension_e6:Dimension e6 59473186455:=by
  exact AZ e6 59473186455 131222915042967 500348823
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e6 GGL rank_e6 (by decide)

def e7:Parameters:=⟨50,946,20,9,68,1,2⟩
theorem shape_e7:Shape e7:=by constructor<;>decide+kernel
theorem middle_e7 (h:ℕ) (hh:h≤9):68≤(e7.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e7,Parameters.cutoff,AQ.reserve]
theorem GHT:AM.AW e7.cutoff 131071 946 20 9 68=25554241487151:=by decide+kernel
theorem rank_e7:AR.rankBound 50 946 20 9 68=97481617:=by decide+kernel
theorem dimension_e7:Dimension e7 20480303:=by
  exact AZ e7 20480303 25554241487151 97481617
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e7 GHT rank_e7 (by decide)

def e8:Parameters:=⟨87,1808,38,17,119,3,4⟩
theorem shape_e8:Shape e8:=by constructor<;>decide+kernel
theorem middle_e8 (h:ℕ) (hh:h≤17):119≤(e8.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e8,Parameters.cutoff,AQ.reserve]
theorem GFU:AM.AW e8.cutoff 131071 1808 38 17 119=467185671295026:=by decide+kernel
theorem rank_e8:AR.rankBound 87 1808 38 17 119=1780143168:=by decide+kernel
theorem dimension_e8:Dimension e8 531820662834:=by
  exact AZ e8 531820662834 467185671295026 1780143168
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e8 GFU rank_e8 (by decide)

def e9:Parameters:=⟨100,2472,42,19,136,4,5⟩
theorem shape_e9:Shape e9:=by constructor<;>decide+kernel
theorem middle_e9 (h:ℕ) (hh:h≤19):136≤(e9.cutoff h+42-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e9,Parameters.cutoff,AQ.reserve]
theorem GGG:AM.AW e9.cutoff 131071 2472 42 19 136=1038236856820691:=by decide+kernel
theorem rank_e9:AR.rankBound 100 2472 42 19 136=3958078512:=by decide+kernel
theorem dimension_e9:Dimension e9 650323370963:=by
  exact AZ e9 650323370963 1038236856820691 3958078512
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e9 GGG rank_e9 (by decide)

def e10:Parameters:=⟨88,1902,36,17,120,3,4⟩
theorem shape_e10:Shape e10:=by constructor<;>decide+kernel
theorem middle_e10 (h:ℕ) (hh:h≤17):120≤(e10.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e10,Parameters.cutoff,AQ.reserve]
theorem GAO:AM.AW e10.cutoff 131071 1902 36 17 120=468472294102971:=by decide+kernel
theorem rank_e10:AR.rankBound 88 1902 36 17 120=1784882750:=by decide+kernel
theorem GXY:Dimension e10 575990486971:=by
  exact AZ e10 575990486971 468472294102971 1784882750
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e10 GAO rank_e10 (by decide)

def e11:Parameters:=⟨82,2530,34,15,112,3,4⟩
theorem shape_e11:Shape e11:=by constructor<;>decide+kernel
theorem middle_e11 (h:ℕ) (hh:h≤15):112≤(e11.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e11,Parameters.cutoff,AQ.reserve]
theorem GFF:AM.AW e11.cutoff 131071 2530 34 15 112=482552044664846:=by decide+kernel
theorem rank_e11:AR.rankBound 82 2530 34 15 112=1838844785:=by decide+kernel
theorem GYD:Dimension e11 509917345806:=by
  exact AZ e11 509917345806 482552044664846 1838844785
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e11 GFF rank_e11 (by decide)

def e12:Parameters:=⟨88,1885,36,17,120,3,4⟩
theorem shape_e12:Shape e12:=by constructor<;>decide+kernel
theorem middle_e12 (h:ℕ) (hh:h≤17):120≤(e12.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e12,Parameters.cutoff,AQ.reserve]
theorem GBI:AM.AW e12.cutoff 131071 1885 36 17 120=464171720247156:=by decide+kernel
theorem rank_e12:AR.rankBound 88 1885 36 17 120=1768572967:=by decide+kernel
theorem GTZ:Dimension e12 550928385908:=by
  exact AZ e12 550928385908 464171720247156 1768572967
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e12 GBI rank_e12 (by decide)

def e13:Parameters:=⟨87,1784,38,17,119,3,4⟩
theorem shape_e13:Shape e13:=by constructor<;>decide+kernel
theorem middle_e13 (h:ℕ) (hh:h≤17):119≤(e13.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e13,Parameters.cutoff,AQ.reserve]
theorem GDP:AM.AW e13.cutoff 131071 1784 38 17 119=460806835961202:=by decide+kernel
theorem rank_e13:AR.rankBound 87 1784 38 17 119=1755949512:=by decide+kernel
theorem GYA:Dimension e13 495207087474:=by
  exact AZ e13 495207087474 460806835961202 1755949512
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e13 GDP rank_e13 (by decide)

def e14:Parameters:=⟨66,1599,26,11,90,2,3⟩
theorem shape_e14:Shape e14:=by constructor<;>decide+kernel
theorem middle_e14 (h:ℕ) (hh:h≤11):90≤(e14.cutoff h+26-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e14,Parameters.cutoff,AQ.reserve]
theorem FZX:AM.AW e14.cutoff 131071 1599 26 11 90=120695579231139:=by decide+kernel
theorem rank_e14:AR.rankBound 66 1599 26 11 90=460416755:=by decide+kernel
theorem GVC:Dimension e14 89408419:=by
  exact AZ e14 89408419 120695579231139 460416755
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e14 FZX rank_e14 (by decide)

def e15:Parameters:=⟨82,2510,34,15,112,3,4⟩
theorem shape_e15:Shape e15:=by constructor<;>decide+kernel
theorem middle_e15 (h:ℕ) (hh:h≤15):112≤(e15.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e15,Parameters.cutoff,AQ.reserve]
theorem GCP:AM.AW e15.cutoff 131071 2510 34 15 112=478665604230606:=by decide+kernel
theorem rank_e15:AR.rankBound 82 2510 34 15 112=1824081785:=by decide+kernel
theorem GTN:Dimension e15 493508783566:=by
  exact AZ e15 493508783566 478665604230606 1824081785
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e15 GCP rank_e15 (by decide)

def e16:Parameters:=⟨88,1870,36,17,120,3,4⟩
theorem shape_e16:Shape e16:=by constructor<;>decide+kernel
theorem middle_e16 (h:ℕ) (hh:h≤17):120≤(e16.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e16,Parameters.cutoff,AQ.reserve]
theorem FZW:AM.AW e16.cutoff 131071 1870 36 17 120=460377096256731:=by decide+kernel
theorem rank_e16:AR.rankBound 88 1870 36 17 120=1754181982:=by decide+kernel
theorem GXN:Dimension e16 528814767323:=by
  exact AZ e16 528814767323 460377096256731 1754181982
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e16 FZW rank_e16 (by decide)

def e17:Parameters:=⟨82,2489,34,15,112,3,4⟩
theorem shape_e17:Shape e17:=by constructor<;>decide+kernel
theorem middle_e17 (h:ℕ) (hh:h≤15):112≤(e17.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e17,Parameters.cutoff,AQ.reserve]
theorem GCT:AM.AW e17.cutoff 131071 2489 34 15 112=474584841774654:=by decide+kernel
theorem rank_e17:AR.rankBound 82 2489 34 15 112=1808580635:=by decide+kernel
theorem GVQ:Dimension e17 476279793214:=by
  exact AZ e17 476279793214 474584841774654 1808580635
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e17 GCT rank_e17 (by decide)

def e18:Parameters:=⟨88,1853,36,17,120,3,4⟩
theorem shape_e18:Shape e18:=by constructor<;>decide+kernel
theorem middle_e18 (h:ℕ) (hh:h≤17):120≤(e18.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e18,Parameters.cutoff,AQ.reserve]
theorem FYY:AM.AW e18.cutoff 131071 1853 36 17 120=456076522400916:=by decide+kernel
theorem rank_e18:AR.rankBound 88 1853 36 17 120=1737872199:=by decide+kernel
theorem GUJ:Dimension e18 503752666260:=by
  exact AZ e18 503752666260 456076522400916 1737872199
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e18 FYY rank_e18 (by decide)

def e19:Parameters:=⟨87,1756,38,17,119,3,4⟩
theorem shape_e19:Shape e19:=by constructor<;>decide+kernel
theorem middle_e19 (h:ℕ) (hh:h≤17):119≤(e19.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e19,Parameters.cutoff,AQ.reserve]
theorem GCX:AM.AW e19.cutoff 131071 1756 38 17 119=453364861405074:=by decide+kernel
theorem rank_e19:AR.rankBound 87 1756 38 17 119=1727723580:=by decide+kernel
theorem GXW:Dimension e19 452491249554:=by
  exact AZ e19 452491249554 453364861405074 1727723580
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e19 GCX rank_e19 (by decide)

def e20:Parameters:=⟨82,2468,34,15,112,3,4⟩
theorem shape_e20:Shape e20:=by constructor<;>decide+kernel
theorem middle_e20 (h:ℕ) (hh:h≤15):112≤(e20.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e20,Parameters.cutoff,AQ.reserve]
theorem GBN:AM.AW e20.cutoff 131071 2468 34 15 112=470504079318702:=by decide+kernel
theorem rank_e20:AR.rankBound 82 2468 34 15 112=1793079485:=by decide+kernel
theorem GTC:Dimension e20 459050802862:=by
  exact AZ e20 459050802862 470504079318702 1793079485
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e20 GBN rank_e20 (by decide)

def e21:Parameters:=⟨88,1836,36,17,120,3,4⟩
theorem shape_e21:Shape e21:=by constructor<;>decide+kernel
theorem middle_e21 (h:ℕ) (hh:h≤17):120≤(e21.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e21,Parameters.cutoff,AQ.reserve]
theorem GCQ:AM.AW e21.cutoff 131071 1836 36 17 120=451775948545101:=by decide+kernel
theorem rank_e21:AR.rankBound 88 1836 36 17 120=1721562416:=by decide+kernel
theorem GYF:Dimension e21 478690565197:=by
  exact AZ e21 478690565197 451775948545101 1721562416
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e21 GCQ rank_e21 (by decide)

def e22:Parameters:=⟨82,2447,34,15,112,3,4⟩
theorem shape_e22:Shape e22:=by constructor<;>decide+kernel
theorem middle_e22 (h:ℕ) (hh:h≤15):112≤(e22.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e22,Parameters.cutoff,AQ.reserve]
theorem FYW:AM.AW e22.cutoff 131071 2447 34 15 112=466423316862750:=by decide+kernel
theorem rank_e22:AR.rankBound 82 2447 34 15 112=1777578335:=by decide+kernel
theorem GXQ:Dimension e22 441821812510:=by
  exact AZ e22 441821812510 466423316862750 1777578335
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e22 FYW rank_e22 (by decide)

def e23:Parameters:=⟨88,1820,36,17,120,3,4⟩
theorem shape_e23:Shape e23:=by constructor<;>decide+kernel
theorem middle_e23 (h:ℕ) (hh:h≤17):120≤(e23.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e23,Parameters.cutoff,AQ.reserve]
theorem GBF:AM.AW e23.cutoff 131071 1820 36 17 120=447728349621981:=by decide+kernel
theorem rank_e23:AR.rankBound 88 1820 36 17 120=1706212032:=by decide+kernel
theorem GUW:Dimension e23 455102705373:=by
  exact AZ e23 455102705373 447728349621981 1706212032
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e23 GBF rank_e23 (by decide)

def e24:Parameters:=⟨87,1728,38,17,119,3,4⟩
theorem shape_e24:Shape e24:=by constructor<;>decide+kernel
theorem middle_e24 (h:ℕ) (hh:h≤17):119≤(e24.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e24,Parameters.cutoff,AQ.reserve]
theorem GCK:AM.AW e24.cutoff 131071 1728 38 17 119=445922886848946:=by decide+kernel
theorem rank_e24:AR.rankBound 87 1728 38 17 119=1699497648:=by decide+kernel
theorem GUH:Dimension e24 409775411634:=by
  exact AZ e24 409775411634 445922886848946 1699497648
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e24 GCK rank_e24 (by decide)

def e25:Parameters:=⟨68,1566,27,13,93,2,3⟩
theorem shape_e25:Shape e25:=by constructor<;>decide+kernel
theorem middle_e25 (h:ℕ) (hh:h≤13):93≤(e25.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e25,Parameters.cutoff,AQ.reserve]
theorem GDC:AM.AW e25.cutoff 131071 1566 27 13 93=136680205688298:=by decide+kernel
theorem rank_e25:AR.rankBound 68 1566 27 13 93=521062532:=by decide+kernel
theorem GWB:Dimension e25 86789299690:=by
  exact AZ e25 86789299690 136680205688298 521062532
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e25 GDC rank_e25 (by decide)

def e26:Parameters:=⟨52,909,22,10,71,1,2⟩
theorem shape_e26:Shape e26:=by constructor<;>decide+kernel
theorem middle_e26 (h:ℕ) (hh:h≤10):71≤(e26.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e26,Parameters.cutoff,AQ.reserve]
theorem FZJ:AM.AW e26.cutoff 131071 909 22 10 71=30953997517190:=by decide+kernel
theorem rank_e26:AR.rankBound 52 909 22 10 71=117962354:=by decide+kernel
theorem GWZ:Dimension e26 30874190214:=by
  exact AZ e26 30874190214 30953997517190 117962354
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e26 FZJ rank_e26 (by decide)

def e27:Parameters:=⟨82,2427,34,15,112,3,4⟩
theorem shape_e27:Shape e27:=by constructor<;>decide+kernel
theorem middle_e27 (h:ℕ) (hh:h≤15):112≤(e27.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e27,Parameters.cutoff,AQ.reserve]
theorem GEL:AM.AW e27.cutoff 131071 2427 34 15 112=462536876428510:=by decide+kernel
theorem rank_e27:AR.rankBound 82 2427 34 15 112=1762815335:=by decide+kernel
theorem GTT:Dimension e27 425413250270:=by
  exact AZ e27 425413250270 462536876428510 1762815335
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e27 GEL rank_e27 (by decide)

def e28:Parameters:=⟨88,1804,36,17,120,3,4⟩
theorem shape_e28:Shape e28:=by constructor<;>decide+kernel
theorem middle_e28 (h:ℕ) (hh:h≤17):120≤(e28.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e28,Parameters.cutoff,AQ.reserve]
theorem FZO:AM.AW e28.cutoff 131071 1804 36 17 120=443680750698861:=by decide+kernel
theorem rank_e28:AR.rankBound 88 1804 36 17 120=1690861648:=by decide+kernel
theorem GUM:Dimension e28 431514845549:=by
  exact AZ e28 431514845549 443680750698861 1690861648
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e28 FZO rank_e28 (by decide)

def e29:Parameters:=⟨84,2358,36,17,115,3,4⟩
theorem shape_e29:Shape e29:=by constructor<;>decide+kernel
theorem middle_e29 (h:ℕ) (hh:h≤17):115≤(e29.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e29,Parameters.cutoff,AQ.reserve]
theorem GAY:AM.AW e29.cutoff 131071 2358 36 17 115=523729009660416:=by decide+kernel
theorem rank_e29:AR.rankBound 84 2358 36 17 115=1994930337:=by decide+kernel
theorem GWS:Dimension e29 769991397888:=by
  exact AZ e29 769991397888 523729009660416 1994930337
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e29 GAY rank_e29 (by decide)

def e30:Parameters:=⟨68,1949,27,13,93,2,3⟩
theorem shape_e30:Shape e30:=by constructor<;>decide+kernel
theorem middle_e30 (h:ℕ) (hh:h≤13):93≤(e30.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e30,Parameters.cutoff,AQ.reserve]
theorem GCH:AM.AW e30.cutoff 131071 1949 27 13 93=170944833838491:=by decide+kernel
theorem rank_e30:AR.rankBound 68 1949 27 13 93=651117459:=by decide+kernel
theorem GTX:Dimension e30 258298666395:=by
  exact AZ e30 258298666395 170944833838491 651117459
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e30 GCH rank_e30 (by decide)

def e31:Parameters:=⟨66,1844,28,14,90,2,3⟩
theorem shape_e31:Shape e31:=by constructor<;>decide+kernel
theorem middle_e31 (h:ℕ) (hh:h≤14):90≤(e31.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e31,Parameters.cutoff,AQ.reserve]
theorem FZK:AM.AW e31.cutoff 131071 1844 28 14 90=159493399900065:=by decide+kernel
theorem rank_e31:AR.rankBound 66 1844 28 14 90=607684965:=by decide+kernel
theorem GUV:Dimension e31 192432435105:=by
  exact AZ e31 192432435105 159493399900065 607684965
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e31 FZK rank_e31 (by decide)

def e32:Parameters:=⟨84,2316,36,17,115,3,4⟩
theorem shape_e32:Shape e32:=by constructor<;>decide+kernel
theorem middle_e32 (h:ℕ) (hh:h≤17):115≤(e32.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e32,Parameters.cutoff,AQ.reserve]
theorem GDU:AM.AW e32.cutoff 131071 2316 36 17 115=514205590223976:=by decide+kernel
theorem rank_e32:AR.rankBound 84 2316 36 17 115=1958778921:=by decide+kernel
theorem GYE:Dimension e32 723448757352:=by
  exact AZ e32 723448757352 514205590223976 1958778921
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e32 GDU rank_e32 (by decide)

def e33:Parameters:=⟨68,1919,27,13,93,2,3⟩
theorem shape_e33:Shape e33:=by constructor<;>decide+kernel
theorem middle_e33 (h:ℕ) (hh:h≤13):93≤(e33.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e33,Parameters.cutoff,AQ.reserve]
theorem GCB:AM.AW e33.cutoff 131071 1919 27 13 93=168260920406361:=by decide+kernel
theorem rank_e33:AR.rankBound 68 1919 27 13 93=640930389:=by decide+kernel
theorem GXR:Dimension e33 244864512345:=by
  exact AZ e33 244864512345 168260920406361 640930389
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e33 GCB rank_e33 (by decide)

def e34:Parameters:=⟨84,2218,34,15,115,3,4⟩
theorem shape_e34:Shape e34:=by constructor<;>decide+kernel
theorem middle_e34 (h:ℕ) (hh:h≤15):115≤(e34.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e34,Parameters.cutoff,AQ.reserve]
theorem GFG:AM.AW e34.cutoff 131071 2218 34 15 115=446246407275722:=by decide+kernel
theorem rank_e34:AR.rankBound 84 2218 34 15 115=1700809189:=by decide+kernel
theorem GXP:Dimension e34 389483234506:=by
  exact AZ e34 389483234506 446246407275722 1700809189
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e34 GFG rank_e34 (by decide)

def e35:Parameters:=⟨84,2275,36,17,115,3,4⟩
theorem shape_e35:Shape e35:=by constructor<;>decide+kernel
theorem middle_e35 (h:ℕ) (hh:h≤17):115≤(e35.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e35,Parameters.cutoff,AQ.reserve]
theorem GCS:AM.AW e35.cutoff 131071 2275 36 17 115=504908918869356:=by decide+kernel
theorem rank_e35:AR.rankBound 84 2275 36 17 115=1923488253:=by decide+kernel
theorem GUY:Dimension e35 678014274924:=by
  exact AZ e35 678014274924 504908918869356 1923488253
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e35 GCS rank_e35 (by decide)

def e36:Parameters:=⟨66,1798,28,14,90,2,3⟩
theorem shape_e36:Shape e36:=by constructor<;>decide+kernel
theorem middle_e36 (h:ℕ) (hh:h≤14):90≤(e36.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e36,Parameters.cutoff,AQ.reserve]
theorem GAL:AM.AW e36.cutoff 131071 1798 28 14 90=155431959071515:=by decide+kernel
theorem rank_e36:AR.rankBound 66 1798 28 14 90=592263925:=by decide+kernel
theorem GTR:Dimension e36 173524716315:=by
  exact AZ e36 173524716315 155431959071515 592263925
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e36 GAL rank_e36 (by decide)

def e37:Parameters:=⟨68,1521,27,13,93,2,3⟩
theorem shape_e37:Shape e37:=by constructor<;>decide+kernel
theorem middle_e37 (h:ℕ) (hh:h≤13):93≤(e37.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e37,Parameters.cutoff,AQ.reserve]
theorem GCM:AM.AW e37.cutoff 131071 1521 27 13 93=132654335540103:=by decide+kernel
theorem rank_e37:AR.rankBound 68 1521 27 13 93=505781927:=by decide+kernel
theorem GUX:Dimension e37 66638068615:=by
  exact AZ e37 66638068615 132654335540103 505781927
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e37 GCM rank_e37 (by decide)

def e38:Parameters:=⟨52,885,22,10,71,1,2⟩
theorem shape_e38:Shape e38:=by constructor<;>decide+kernel
theorem middle_e38 (h:ℕ) (hh:h≤10):71≤(e38.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e38,Parameters.cutoff,AQ.reserve]
theorem GBM:AM.AW e38.cutoff 131071 885 22 10 71=30109469417054:=by decide+kernel
theorem rank_e38:AR.rankBound 52 885 22 10 71=114761978:=by decide+kernel
theorem GWI:Dimension e38 25305456222:=by
  exact AZ e38 25305456222 30109469417054 114761978
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e38 GBM rank_e38 (by decide)

def e39:Parameters:=⟨84,2194,34,15,115,3,4⟩
theorem shape_e39:Shape e39:=by constructor<;>decide+kernel
theorem middle_e39 (h:ℕ) (hh:h≤15):115≤(e39.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e39,Parameters.cutoff,AQ.reserve]
theorem FZU:AM.AW e39.cutoff 131071 2194 34 15 115=441311685093290:=by decide+kernel
theorem rank_e39:AR.rankBound 84 2194 34 15 115=1682072005:=by decide+kernel
theorem GTK:Dimension e39 366601414570:=by
  exact AZ e39 366601414570 441311685093290 1682072005
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e39 FZU rank_e39 (by decide)

def e40:Parameters:=⟨86,2224,36,17,117,3,4⟩
theorem shape_e40:Shape e40:=by constructor<;>decide+kernel
theorem middle_e40 (h:ℕ) (hh:h≤17):117≤(e40.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e40,Parameters.cutoff,AQ.reserve]
theorem GBC:AM.AW e40.cutoff 131071 2224 36 17 117=521248713223491:=by decide+kernel
theorem rank_e40:AR.rankBound 86 2224 36 17 117=1985148009:=by decide+kernel
theorem GTU:Dimension e40 854073552195:=by
  exact AZ e40 854073552195 521248713223491 1985148009
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e40 GBC rank_e40 (by decide)

def e41:Parameters:=⟨84,2170,34,15,115,3,4⟩
theorem shape_e41:Shape e41:=by constructor<;>decide+kernel
theorem middle_e41 (h:ℕ) (hh:h≤15):115≤(e41.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e41,Parameters.cutoff,AQ.reserve]
theorem GEC:AM.AW e41.cutoff 131071 2170 34 15 115=436376962910858:=by decide+kernel
theorem rank_e41:AR.rankBound 84 2170 34 15 115=1663334821:=by decide+kernel
theorem GVY:Dimension e41 343719594634:=by
  exact AZ e41 343719594634 436376962910858 1663334821
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e41 GEC rank_e41 (by decide)

def e42:Parameters:=⟨86,2170,36,17,117,3,4⟩
theorem shape_e42:Shape e42:=by constructor<;>decide+kernel
theorem middle_e42 (h:ℕ) (hh:h≤17):117≤(e42.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e42,Parameters.cutoff,AQ.reserve]
theorem FZB:AM.AW e42.cutoff 131071 2170 36 17 117=508306155829911:=by decide+kernel
theorem rank_e42:AR.rankBound 86 2170 36 17 117=1936043217:=by decide+kernel
theorem GWD:Dimension e42 784042752663:=by
  exact AZ e42 784042752663 508306155829911 1936043217
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e42 FZB rank_e42 (by decide)

def e43:Parameters:=⟨68,1829,27,13,93,2,3⟩
theorem shape_e43:Shape e43:=by constructor<;>decide+kernel
theorem middle_e43 (h:ℕ) (hh:h≤13):93≤(e43.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e43,Parameters.cutoff,AQ.reserve]
theorem GAQ:AM.AW e43.cutoff 131071 1829 27 13 93=160209180109971:=by decide+kernel
theorem rank_e43:AR.rankBound 68 1829 27 13 93=610369179:=by decide+kernel
theorem GWQ:Dimension e43 204562050195:=by
  exact AZ e43 204562050195 160209180109971 610369179
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e43 GAQ rank_e43 (by decide)

def e44:Parameters:=⟨66,1752,28,14,90,2,3⟩
theorem shape_e44:Shape e44:=by constructor<;>decide+kernel
theorem middle_e44 (h:ℕ) (hh:h≤14):90≤(e44.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e44,Parameters.cutoff,AQ.reserve]
theorem GDH:AM.AW e44.cutoff 131071 1752 28 14 90=151370518242965:=by decide+kernel
theorem rank_e44:AR.rankBound 66 1752 28 14 90=576842885:=by decide+kernel
theorem GUD:Dimension e44 154616997525:=by
  exact AZ e44 154616997525 151370518242965 576842885
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e44 GDH rank_e44 (by decide)

def e45:Parameters:=⟨48,1368,20,9,65,1,2⟩
theorem shape_e45:Shape e45:=by constructor<;>decide+kernel
theorem middle_e45 (h:ℕ) (hh:h≤9):65≤(e45.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e45,Parameters.cutoff,AQ.reserve]
theorem GAW:AM.AW e45.cutoff 131071 1368 20 9 65=33943566918063:=by decide+kernel
theorem rank_e45:AR.rankBound 48 1368 20 9 65=129351364:=by decide+kernel
theorem GTI:Dimension e45 34882953647:=by
  exact AZ e45 34882953647 33943566918063 129351364
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e45 GAW rank_e45 (by decide)

def e46:Parameters:=⟨66,1729,28,14,90,2,3⟩
theorem shape_e46:Shape e46:=by constructor<;>decide+kernel
theorem middle_e46 (h:ℕ) (hh:h≤14):90≤(e46.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e46,Parameters.cutoff,AQ.reserve]
theorem GFB:AM.AW e46.cutoff 131071 1729 28 14 90=149339797828690:=by decide+kernel
theorem rank_e46:AR.rankBound 66 1729 28 14 90=569132365:=by decide+kernel
theorem GWV:Dimension e46 145163138130:=by
  exact AZ e46 145163138130 149339797828690 569132365
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e46 GFB rank_e46 (by decide)

def e47:Parameters:=⟨86,2115,36,17,117,3,4⟩
theorem shape_e47:Shape e47:=by constructor<;>decide+kernel
theorem middle_e47 (h:ℕ) (hh:h≤17):117≤(e47.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e47,Parameters.cutoff,AQ.reserve]
theorem FZI:AM.AW e47.cutoff 131071 2115 36 17 117=495123921447561:=by decide+kernel
theorem rank_e47:AR.rankBound 86 2115 36 17 117=1886029077:=by decide+kernel
theorem GUC:Dimension e47 712715086473:=by
  exact AZ e47 712715086473 495123921447561 1886029077
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e47 FZI rank_e47 (by decide)

def e48:Parameters:=⟨68,1800,27,13,93,2,3⟩
theorem shape_e48:Shape e48:=by constructor<;>decide+kernel
theorem middle_e48 (h:ℕ) (hh:h≤13):93≤(e48.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e48,Parameters.cutoff,AQ.reserve]
theorem FZZ:AM.AW e48.cutoff 131071 1800 27 13 93=157614730458912:=by decide+kernel
theorem rank_e48:AR.rankBound 68 1800 27 13 93=600521678:=by decide+kernel
theorem GXC:Dimension e48 191575701280:=by
  exact AZ e48 191575701280 157614730458912 600521678
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e48 FZZ rank_e48 (by decide)

def e49:Parameters:=⟨66,1706,28,14,90,2,3⟩
theorem shape_e49:Shape e49:=by constructor<;>decide+kernel
theorem middle_e49 (h:ℕ) (hh:h≤14):90≤(e49.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e49,Parameters.cutoff,AQ.reserve]
theorem GDS:AM.AW e49.cutoff 131071 1706 28 14 90=147309077414415:=by decide+kernel
theorem rank_e49:AR.rankBound 66 1706 28 14 90=561421845:=by decide+kernel
theorem GWU:Dimension e49 135709278735:=by
  exact AZ e49 135709278735 147309077414415 561421845
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e49 GDS rank_e49 (by decide)

def e50:Parameters:=⟨48,1338,20,9,65,1,2⟩
theorem shape_e50:Shape e50:=by constructor<;>decide+kernel
theorem middle_e50 (h:ℕ) (hh:h≤9):65≤(e50.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e50,Parameters.cutoff,AQ.reserve]
theorem GDM:AM.AW e50.cutoff 131071 1338 20 9 65=33184271988483:=by decide+kernel
theorem rank_e50:AR.rankBound 48 1338 20 9 65=126467734:=by decide+kernel
theorem GXU:Dimension e50 31514326787:=by
  exact AZ e50 31514326787 33184271988483 126467734
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e50 GDM rank_e50 (by decide)

def e51:Parameters:=⟨66,1683,28,14,90,2,3⟩
theorem shape_e51:Shape e51:=by constructor<;>decide+kernel
theorem middle_e51 (h:ℕ) (hh:h≤14):90≤(e51.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e51,Parameters.cutoff,AQ.reserve]
theorem FZG:AM.AW e51.cutoff 131071 1683 28 14 90=145278357000140:=by decide+kernel
theorem rank_e51:AR.rankBound 66 1683 28 14 90=553711325:=by decide+kernel
theorem GYN:Dimension e51 126255419340:=by
  exact AZ e51 126255419340 145278357000140 553711325
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e51 FZG rank_e51 (by decide)

def e52:Parameters:=⟨52,910,22,10,71,1,2⟩
theorem shape_e52:Shape e52:=by constructor<;>decide+kernel
theorem middle_e52 (h:ℕ) (hh:h≤10):71≤(e52.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e52,Parameters.cutoff,AQ.reserve]
theorem GBG:AM.AW e52.cutoff 131071 910 22 10 71=30989186188029:=by decide+kernel
theorem rank_e52:AR.rankBound 52 910 22 10 71=118095703:=by decide+kernel
theorem GTS:Dimension e52 31106220797:=by
  exact AZ e52 31106220797 30989186188029 118095703
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e52 GBG rank_e52 (by decide)

def e53:Parameters:=⟨68,1489,27,13,93,2,3⟩
theorem shape_e53:Shape e53:=by constructor<;>decide+kernel
theorem middle_e53 (h:ℕ) (hh:h≤13):93≤(e53.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e53,Parameters.cutoff,AQ.reserve]
theorem GAU:AM.AW e53.cutoff 131071 1489 27 13 93=129791494545831:=by decide+kernel
theorem rank_e53:AR.rankBound 68 1489 27 13 93=494915719:=by decide+kernel
theorem GXB:Dimension e53 52308304295:=by
  exact AZ e53 52308304295 129791494545831 494915719
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e53 GAU rank_e53 (by decide)

def e54:Parameters:=⟨50,1404,20,9,68,1,2⟩
theorem shape_e54:Shape e54:=by constructor<;>decide+kernel
theorem middle_e54 (h:ℕ) (hh:h≤9):68≤(e54.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e54,Parameters.cutoff,AQ.reserve]
theorem GEJ:AM.AW e54.cutoff 131071 1404 20 9 68=38301083275513:=by decide+kernel
theorem rank_e54:AR.rankBound 50 1404 20 9 68=145848249:=by decide+kernel
theorem GVL:Dimension e54 67839889657:=by
  exact AZ e54 67839889657 38301083275513 145848249
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e54 GEJ rank_e54 (by decide)

def e55:Parameters:=⟨52,887,22,10,71,1,2⟩
theorem shape_e55:Shape e55:=by constructor<;>decide+kernel
theorem middle_e55 (h:ℕ) (hh:h≤10):71≤(e55.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e55,Parameters.cutoff,AQ.reserve]
theorem GEP:AM.AW e55.cutoff 131071 887 22 10 71=30179846758732:=by decide+kernel
theorem rank_e55:AR.rankBound 52 887 22 10 71=115028676:=by decide+kernel
theorem GXJ:Dimension e55 25769517388:=by
  exact AZ e55 25769517388 30179846758732 115028676
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e55 GEP rank_e55 (by decide)

def e56:Parameters:=⟨52,858,22,10,71,1,2⟩
theorem shape_e56:Shape e56:=by constructor<;>decide+kernel
theorem middle_e56 (h:ℕ) (hh:h≤10):71≤(e56.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e56,Parameters.cutoff,AQ.reserve]
theorem GCZ:AM.AW e56.cutoff 131071 858 22 10 71=29159375304401:=by decide+kernel
theorem rank_e56:AR.rankBound 52 858 22 10 71=111161555:=by decide+kernel
theorem GWC:Dimension e56 19040630481:=by
  exact AZ e56 19040630481 29159375304401 111161555
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e56 GCZ rank_e56 (by decide)

def e57:Parameters:=⟨68,1479,28,12,93,2,3⟩
theorem shape_e57:Shape e57:=by constructor<;>decide+kernel
theorem middle_e57 (h:ℕ) (hh:h≤12):93≤(e57.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e57,Parameters.cutoff,AQ.reserve]
theorem GEF:AM.AW e57.cutoff 131071 1479 28 12 93=134006887646705:=by decide+kernel
theorem rank_e57:AR.rankBound 68 1479 28 12 93=510815027:=by decide+kernel
theorem GWM:Dimension e57 99793208817:=by
  exact AZ e57 99793208817 134006887646705 510815027
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e57 GEF rank_e57 (by decide)

def e58:Parameters:=⟨60,602,26,12,82,1,2⟩
theorem shape_e58:Shape e58:=by constructor<;>decide+kernel
theorem middle_e58 (h:ℕ) (hh:h≤12):82≤(e58.cutoff h+26-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e58,Parameters.cutoff,AQ.reserve]
theorem GBL:AM.AW e58.cutoff 131071 602 26 12 82=35924157157770:=by decide+kernel
theorem rank_e58:AR.rankBound 60 602 26 12 82=137028377:=by decide+kernel
theorem GXO:Dimension e58 2990297482:=by
  exact AZ e58 2990297482 35924157157770 137028377
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e58 GBL rank_e58 (by decide)

def e59:Parameters:=⟨60,616,26,12,82,1,2⟩
theorem shape_e59:Shape e59:=by constructor<;>decide+kernel
theorem middle_e59 (h:ℕ) (hh:h≤12):82≤(e59.cutoff h+26-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e59,Parameters.cutoff,AQ.reserve]
theorem GAH:AM.AW e59.cutoff 131071 616 26 12 82=36810021743670:=by decide+kernel
theorem rank_e59:AR.rankBound 60 616 26 12 82=140373943:=by decide+kernel
theorem GYG:Dimension e59 11834829878:=by
  exact AZ e59 11834829878 36810021743670 140373943
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e59 GAH rank_e59 (by decide)

def e60:Parameters:=⟨100,2494,42,19,136,4,5⟩
theorem shape_e60:Shape e60:=by constructor<;>decide+kernel
theorem middle_e60 (h:ℕ) (hh:h≤19):136≤(e60.cutoff h+42-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e60,Parameters.cutoff,AQ.reserve]
theorem GBD:AM.AW e60.cutoff 131071 2494 42 19 136=1047696605119571:=by decide+kernel
theorem rank_e60:AR.rankBound 100 2494 42 19 136=3993999694:=by decide+kernel
theorem GXZ:Dimension e60 693549335635:=by
  exact AZ e60 693549335635 1047696605119571 3993999694
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e60 GBD rank_e60 (by decide)

def e61:Parameters:=⟨88,1932,36,17,120,3,4⟩
theorem shape_e61:Shape e61:=by constructor<;>decide+kernel
theorem middle_e61 (h:ℕ) (hh:h≤17):120≤(e61.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e61,Parameters.cutoff,AQ.reserve]
theorem GAC:AM.AW e61.cutoff 131071 1932 36 17 120=476061542083821:=by decide+kernel
theorem rank_e61:AR.rankBound 88 1932 36 17 120=1813664720:=by decide+kernel
theorem GWR:Dimension e61 620217724141:=by
  exact AZ e61 620217724141 476061542083821 1813664720
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e61 GAC rank_e61 (by decide)

def e62:Parameters:=⟨100,2484,42,19,136,4,5⟩
theorem shape_e62:Shape e62:=by constructor<;>decide+kernel
theorem middle_e62 (h:ℕ) (hh:h≤19):136≤(e62.cutoff h+42-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e62,Parameters.cutoff,AQ.reserve]
theorem GDY:AM.AW e62.cutoff 131071 2484 42 19 136=1043396719529171:=by decide+kernel
theorem rank_e62:AR.rankBound 100 2484 42 19 136=3977671884:=by decide+kernel
theorem GYK:Dimension e62 673901169875:=by
  exact AZ e62 673901169875 1043396719529171 3977671884
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e62 GDY rank_e62 (by decide)

def e63:Parameters:=⟨88,1919,36,17,120,3,4⟩
theorem shape_e63:Shape e63:=by constructor<;>decide+kernel
theorem middle_e63 (h:ℕ) (hh:h≤17):120≤(e63.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e63,Parameters.cutoff,AQ.reserve]
theorem GBY:AM.AW e63.cutoff 131071 1919 36 17 120=472772867958786:=by decide+kernel
theorem rank_e63:AR.rankBound 88 1919 36 17 120=1801192533:=by decide+kernel
theorem GTA:Dimension e63 601052588034:=by
  exact AZ e63 601052588034 472772867958786 1801192533
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e63 GBY rank_e63 (by decide)

def e64:Parameters:=⟨84,2374,34,15,115,3,4⟩
theorem shape_e64:Shape e64:=by constructor<;>decide+kernel
theorem middle_e64 (h:ℕ) (hh:h≤15):115≤(e64.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e64,Parameters.cutoff,AQ.reserve]
theorem GED:AM.AW e64.cutoff 131071 2374 34 15 115=478322101461530:=by decide+kernel
theorem rank_e64:AR.rankBound 84 2374 34 15 115=1822600885:=by decide+kernel
theorem GVT:Dimension e64 538215064090:=by
  exact AZ e64 538215064090 478322101461530 1822600885
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e64 GED rank_e64 (by decide)

def e65:Parameters:=⟨84,2363,34,15,115,3,4⟩
theorem shape_e65:Shape e65:=by constructor<;>decide+kernel
theorem middle_e65 (h:ℕ) (hh:h≤15):115≤(e65.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e65,Parameters.cutoff,AQ.reserve]
theorem GEG:AM.AW e65.cutoff 131071 2363 34 15 115=476060353794582:=by decide+kernel
theorem rank_e65:AR.rankBound 84 2363 34 15 115=1814013009:=by decide+kernel
theorem GWK:Dimension e65 527727563286:=by
  exact AZ e65 527727563286 476060353794582 1814013009
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e65 GEG rank_e65 (by decide)

def e66:Parameters:=⟨88,2045,36,17,120,3,4⟩
theorem shape_e66:Shape e66:=by constructor<;>decide+kernel
theorem middle_e66 (h:ℕ) (hh:h≤17):120≤(e66.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e66,Parameters.cutoff,AQ.reserve]
theorem GBS:AM.AW e66.cutoff 131071 2045 36 17 120=504647709478356:=by decide+kernel
theorem rank_e66:AR.rankBound 88 2045 36 17 120=1922076807:=by decide+kernel
theorem GUF:Dimension e66 786806984148:=by
  exact AZ e66 786806984148 504647709478356 1922076807
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e66 GBS rank_e66 (by decide)

def e67:Parameters:=⟨84,2353,34,15,115,3,4⟩
theorem shape_e67:Shape e67:=by constructor<;>decide+kernel
theorem middle_e67 (h:ℕ) (hh:h≤15):115≤(e67.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e67,Parameters.cutoff,AQ.reserve]
theorem GBO:AM.AW e67.cutoff 131071 2353 34 15 115=474004219551902:=by decide+kernel
theorem rank_e67:AR.rankBound 84 2353 34 15 115=1806205849:=by decide+kernel
theorem GVZ:Dimension e67 518193471646:=by
  exact AZ e67 518193471646 474004219551902 1806205849
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e67 GBO rank_e67 (by decide)

def e68:Parameters:=⟨88,2032,36,17,120,3,4⟩
theorem shape_e68:Shape e68:=by constructor<;>decide+kernel
theorem middle_e68 (h:ℕ) (hh:h≤17):120≤(e68.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e68,Parameters.cutoff,AQ.reserve]
theorem FZP:AM.AW e68.cutoff 131071 2032 36 17 120=501359035353321:=by decide+kernel
theorem rank_e68:AR.rankBound 88 2032 36 17 120=1909604620:=by decide+kernel
theorem GXK:Dimension e68 767641848041:=by
  exact AZ e68 767641848041 501359035353321 1909604620
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e68 FZP rank_e68 (by decide)

def e69:Parameters:=⟨84,2342,34,15,115,3,4⟩
theorem shape_e69:Shape e69:=by constructor<;>decide+kernel
theorem middle_e69 (h:ℕ) (hh:h≤15):115≤(e69.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e69,Parameters.cutoff,AQ.reserve]
theorem GAX:AM.AW e69.cutoff 131071 2342 34 15 115=471742471884954:=by decide+kernel
theorem rank_e69:AR.rankBound 84 2342 34 15 115=1797617973:=by decide+kernel
theorem GUK:Dimension e69 507705970842:=by
  exact AZ e69 507705970842 471742471884954 1797617973
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e69 GAX rank_e69 (by decide)

def e70:Parameters:=⟨88,2019,36,17,120,3,4⟩
theorem shape_e70:Shape e70:=by constructor<;>decide+kernel
theorem middle_e70 (h:ℕ) (hh:h≤17):120≤(e70.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e70,Parameters.cutoff,AQ.reserve]
theorem GAE:AM.AW e70.cutoff 131071 2019 36 17 120=498070361228286:=by decide+kernel
theorem rank_e70:AR.rankBound 88 2019 36 17 120=1897132433:=by decide+kernel
theorem GTO:Dimension e70 748476711934:=by
  exact AZ e70 748476711934 498070361228286 1897132433
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e70 GAE rank_e70 (by decide)

def e71:Parameters:=⟨84,2332,34,15,115,3,4⟩
theorem shape_e71:Shape e71:=by constructor<;>decide+kernel
theorem middle_e71 (h:ℕ) (hh:h≤15):115≤(e71.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e71,Parameters.cutoff,AQ.reserve]
theorem GBW:AM.AW e71.cutoff 131071 2332 34 15 115=469686337642274:=by decide+kernel
theorem rank_e71:AR.rankBound 84 2332 34 15 115=1789810813:=by decide+kernel
theorem GXS:Dimension e71 498171879202:=by
  exact AZ e71 498171879202 469686337642274 1789810813
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e71 GBW rank_e71 (by decide)

def e72:Parameters:=⟨88,2007,36,17,120,3,4⟩
theorem shape_e72:Shape e72:=by constructor<;>decide+kernel
theorem middle_e72 (h:ℕ) (hh:h≤17):120≤(e72.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e72,Parameters.cutoff,AQ.reserve]
theorem FZN:AM.AW e72.cutoff 131071 2007 36 17 120=495034662035946:=by decide+kernel
theorem rank_e72:AR.rankBound 88 2007 36 17 120=1885619645:=by decide+kernel
theorem GXG:Dimension e72 730785817066:=by
  exact AZ e72 730785817066 495034662035946 1885619645
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e72 FZN rank_e72 (by decide)

def e73:Parameters:=⟨84,2321,34,15,115,3,4⟩
theorem shape_e73:Shape e73:=by constructor<;>decide+kernel
theorem middle_e73 (h:ℕ) (hh:h≤15):115≤(e73.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e73,Parameters.cutoff,AQ.reserve]
theorem GCN:AM.AW e73.cutoff 131071 2321 34 15 115=467424589975326:=by decide+kernel
theorem rank_e73:AR.rankBound 84 2321 34 15 115=1781222937:=by decide+kernel
theorem GVJ:Dimension e73 487684378398:=by
  exact AZ e73 487684378398 467424589975326 1781222937
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e73 GCN rank_e73 (by decide)

def e74:Parameters:=⟨88,1994,36,17,120,3,4⟩
theorem shape_e74:Shape e74:=by constructor<;>decide+kernel
theorem middle_e74 (h:ℕ) (hh:h≤17):120≤(e74.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e74,Parameters.cutoff,AQ.reserve]
theorem GAV:AM.AW e74.cutoff 131071 1994 36 17 120=491745987910911:=by decide+kernel
theorem rank_e74:AR.rankBound 88 1994 36 17 120=1873147458:=by decide+kernel
theorem GVH:Dimension e74 711620680959:=by
  exact AZ e74 711620680959 491745987910911 1873147458
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e74 GAV rank_e74 (by decide)

def e75:Parameters:=⟨84,2310,34,15,115,3,4⟩
theorem shape_e75:Shape e75:=by constructor<;>decide+kernel
theorem middle_e75 (h:ℕ) (hh:h≤15):115≤(e75.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e75,Parameters.cutoff,AQ.reserve]
theorem GDX:AM.AW e75.cutoff 131071 2310 34 15 115=465162842308378:=by decide+kernel
theorem rank_e75:AR.rankBound 84 2310 34 15 115=1772635061:=by decide+kernel
theorem GTH:Dimension e75 477196877594:=by
  exact AZ e75 477196877594 465162842308378 1772635061
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e75 GDX rank_e75 (by decide)

def e76:Parameters:=⟨88,1981,36,17,120,3,4⟩
theorem shape_e76:Shape e76:=by constructor<;>decide+kernel
theorem middle_e76 (h:ℕ) (hh:h≤17):120≤(e76.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e76,Parameters.cutoff,AQ.reserve]
theorem FZT:AM.AW e76.cutoff 131071 1981 36 17 120=488457313785876:=by decide+kernel
theorem rank_e76:AR.rankBound 88 1981 36 17 120=1860675271:=by decide+kernel
theorem GYL:Dimension e76 692455544852:=by
  exact AZ e76 692455544852 488457313785876 1860675271
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e76 FZT rank_e76 (by decide)

def e77:Parameters:=⟨84,2300,34,15,115,3,4⟩
theorem shape_e77:Shape e77:=by constructor<;>decide+kernel
theorem middle_e77 (h:ℕ) (hh:h≤15):115≤(e77.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e77,Parameters.cutoff,AQ.reserve]
theorem GBH:AM.AW e77.cutoff 131071 2300 34 15 115=463106708065698:=by decide+kernel
theorem rank_e77:AR.rankBound 84 2300 34 15 115=1764827901:=by decide+kernel
theorem GVN:Dimension e77 467662785954:=by
  exact AZ e77 467662785954 463106708065698 1764827901
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e77 GBH rank_e77 (by decide)

def e78:Parameters:=⟨88,1968,36,17,120,3,4⟩
theorem shape_e78:Shape e78:=by constructor<;>decide+kernel
theorem middle_e78 (h:ℕ) (hh:h≤17):120≤(e78.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e78,Parameters.cutoff,AQ.reserve]
theorem GAD:AM.AW e78.cutoff 131071 1968 36 17 120=485168639660841:=by decide+kernel
theorem rank_e78:AR.rankBound 88 1968 36 17 120=1848203084:=by decide+kernel
theorem GVO:Dimension e78 673290408745:=by
  exact AZ e78 673290408745 485168639660841 1848203084
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e78 GAD rank_e78 (by decide)

def e79:Parameters:=⟨52,928,22,10,71,1,2⟩
theorem shape_e79:Shape e79:=by constructor<;>decide+kernel
theorem middle_e79 (h:ℕ) (hh:h≤10):71≤(e79.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e79,Parameters.cutoff,AQ.reserve]
theorem GDD:AM.AW e79.cutoff 131071 928 22 10 71=31622582263131:=by decide+kernel
theorem rank_e79:AR.rankBound 52 928 22 10 71=120495985:=by decide+kernel
theorem GWH:Dimension e79 35282771291:=by
  exact AZ e79 35282771291 31622582263131 120495985
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e79 GDD rank_e79 (by decide)

def e80:Parameters:=⟨68,1552,27,13,93,2,3⟩
theorem shape_e80:Shape e80:=by constructor<;>decide+kernel
theorem middle_e80 (h:ℕ) (hh:h≤13):93≤(e80.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e80,Parameters.cutoff,AQ.reserve]
theorem GDK:AM.AW e80.cutoff 131071 1552 27 13 93=135427712753304:=by decide+kernel
theorem rank_e80:AR.rankBound 68 1552 27 13 93=516308566:=by decide+kernel
theorem GWL:Dimension e80 80520027800:=by
  exact AZ e80 80520027800 135427712753304 516308566
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e80 GDK rank_e80 (by decide)

def e81:Parameters:=⟨86,1812,38,17,117,3,4⟩
theorem shape_e81:Shape e81:=by constructor<;>decide+kernel
theorem middle_e81 (h:ℕ) (hh:h≤17):117≤(e81.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e81,Parameters.cutoff,AQ.reserve]
theorem GAZ:AM.AW e81.cutoff 131071 1812 38 17 117=455695335198240:=by decide+kernel
theorem rank_e81:AR.rankBound 86 1812 38 17 117=1736775390:=by decide+kernel
theorem GUU:Dimension e81 410087362080:=by
  exact AZ e81 410087362080 455695335198240 1736775390
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e81 GAZ rank_e81 (by decide)

def e82:Parameters:=⟨84,2291,34,15,115,3,4⟩
theorem shape_e82:Shape e82:=by constructor<;>decide+kernel
theorem middle_e82 (h:ℕ) (hh:h≤15):115≤(e82.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e82,Parameters.cutoff,AQ.reserve]
theorem GES:AM.AW e82.cutoff 131071 2291 34 15 115=461256187247286:=by decide+kernel
theorem rank_e82:AR.rankBound 84 2291 34 15 115=1757801457:=by decide+kernel
theorem GXI:Dimension e82 459082103478:=by
  exact AZ e82 459082103478 461256187247286 1757801457
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e82 GES rank_e82 (by decide)

def e83:Parameters:=⟨88,1957,36,17,120,3,4⟩
theorem shape_e83:Shape e83:=by constructor<;>decide+kernel
theorem middle_e83 (h:ℕ) (hh:h≤17):120≤(e83.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e83,Parameters.cutoff,AQ.reserve]
theorem GBT:AM.AW e83.cutoff 131071 1957 36 17 120=482385915401196:=by decide+kernel
theorem rank_e83:AR.rankBound 88 1957 36 17 120=1837649695:=by decide+kernel
theorem GWX:Dimension e83 657073755116:=by
  exact AZ e83 657073755116 482385915401196 1837649695
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e83 GBT rank_e83 (by decide)

def e84:Parameters:=⟨84,2279,34,15,115,3,4⟩
theorem shape_e84:Shape e84:=by constructor<;>decide+kernel
theorem middle_e84 (h:ℕ) (hh:h≤15):115≤(e84.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e84,Parameters.cutoff,AQ.reserve]
theorem GDR:AM.AW e84.cutoff 131071 2279 34 15 115=458788826156070:=by decide+kernel
theorem rank_e84:AR.rankBound 84 2279 34 15 115=1748432865:=by decide+kernel
theorem GTF:Dimension e84 447641193510:=by
  exact AZ e84 447641193510 458788826156070 1748432865
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e84 GDR rank_e84 (by decide)

def e85:Parameters:=⟨84,2267,34,15,115,3,4⟩
theorem shape_e85:Shape e85:=by constructor<;>decide+kernel
theorem middle_e85 (h:ℕ) (hh:h≤15):115≤(e85.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e85,Parameters.cutoff,AQ.reserve]
theorem GEA:AM.AW e85.cutoff 131071 2267 34 15 115=456321465064854:=by decide+kernel
theorem rank_e85:AR.rankBound 84 2267 34 15 115=1739064273:=by decide+kernel
theorem GUZ:Dimension e85 436200283542:=by
  exact AZ e85 436200283542 456321465064854 1739064273
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e85 GEA rank_e85 (by decide)

def e86:Parameters:=⟨48,1427,20,9,65,1,2⟩
theorem shape_e86:Shape e86:=by constructor<;>decide+kernel
theorem middle_e86 (h:ℕ) (hh:h≤9):65≤(e86.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e86,Parameters.cutoff,AQ.reserve]
theorem GBP:AM.AW e86.cutoff 131071 1427 20 9 65=35436846946237:=by decide+kernel
theorem rank_e86:AR.rankBound 48 1427 20 9 65=135022503:=by decide+kernel
theorem GWN:Dimension e86 41507919805:=by
  exact AZ e86 41507919805 35436846946237 135022503
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e86 GBP rank_e86 (by decide)

def e87:Parameters:=⟨66,1821,28,14,90,2,3⟩
theorem shape_e87:Shape e87:=by constructor<;>decide+kernel
theorem middle_e87 (h:ℕ) (hh:h≤14):90≤(e87.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e87,Parameters.cutoff,AQ.reserve]
theorem GCC:AM.AW e87.cutoff 131071 1821 28 14 90=157462679485790:=by decide+kernel
theorem rank_e87:AR.rankBound 66 1821 28 14 90=599974445:=by decide+kernel
theorem GXA:Dimension e87 182978575710:=by
  exact AZ e87 182978575710 157462679485790 599974445
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e87 GCC rank_e87 (by decide)

def e88:Parameters:=⟨48,1413,20,9,65,1,2⟩
theorem shape_e88:Shape e88:=by constructor<;>decide+kernel
theorem middle_e88 (h:ℕ) (hh:h≤9):65≤(e88.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e88,Parameters.cutoff,AQ.reserve]
theorem GEB:AM.AW e88.cutoff 131071 1413 20 9 65=35082509312433:=by decide+kernel
theorem rank_e88:AR.rankBound 48 1413 20 9 65=133676809:=by decide+kernel
theorem GYB:Dimension e88 39935893937:=by
  exact AZ e88 39935893937 35082509312433 133676809
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e88 GEB rank_e88 (by decide)

def e89:Parameters:=⟨86,1774,38,17,117,3,4⟩
theorem shape_e89:Shape e89:=by constructor<;>decide+kernel
theorem middle_e89 (h:ℕ) (hh:h≤17):117≤(e89.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e89,Parameters.cutoff,AQ.reserve]
theorem FZV:AM.AW e89.cutoff 131071 1774 38 17 117=445868929363500:=by decide+kernel
theorem rank_e89:AR.rankBound 86 1774 38 17 117=1699493058:=by decide+kernel
theorem GWG:Dimension e89 357021167148:=by
  exact AZ e89 357021167148 445868929363500 1699493058
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e89 FZV rank_e89 (by decide)

def e90:Parameters:=⟨84,2243,34,15,115,3,4⟩
theorem shape_e90:Shape e90:=by constructor<;>decide+kernel
theorem middle_e90 (h:ℕ) (hh:h≤15):115≤(e90.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e90,Parameters.cutoff,AQ.reserve]
theorem GEY:AM.AW e90.cutoff 131071 2243 34 15 115=451386742882422:=by decide+kernel
theorem rank_e90:AR.rankBound 84 2243 34 15 115=1720327089:=by decide+kernel
theorem GVD:Dimension e90 413318463606:=by
  exact AZ e90 413318463606 451386742882422 1720327089
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e90 GEY rank_e90 (by decide)

def e91:Parameters:=⟨68,1889,27,13,93,2,3⟩
theorem shape_e91:Shape e91:=by constructor<;>decide+kernel
theorem middle_e91 (h:ℕ) (hh:h≤13):93≤(e91.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e91,Parameters.cutoff,AQ.reserve]
theorem GAS:AM.AW e91.cutoff 131071 1889 27 13 93=165577006974231:=by decide+kernel
theorem rank_e91:AR.rankBound 68 1889 27 13 93=630743319:=by decide+kernel
theorem GUT:Dimension e91 231430358295:=by
  exact AZ e91 231430358295 165577006974231 630743319
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e91 GAS rank_e91 (by decide)

def e92:Parameters:=⟨48,1398,20,9,65,1,2⟩
theorem shape_e92:Shape e92:=by constructor<;>decide+kernel
theorem middle_e92 (h:ℕ) (hh:h≤9):65≤(e92.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e92,Parameters.cutoff,AQ.reserve]
theorem GDV:AM.AW e92.cutoff 131071 1398 20 9 65=34702861847643:=by decide+kernel
theorem rank_e92:AR.rankBound 48 1398 20 9 65=132234994:=by decide+kernel
theorem GVB:Dimension e92 38251580507:=by
  exact AZ e92 38251580507 34702861847643 132234994
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e92 GDV rank_e92 (by decide)

def e93:Parameters:=⟨66,1775,28,14,90,2,3⟩
theorem shape_e93:Shape e93:=by constructor<;>decide+kernel
theorem middle_e93 (h:ℕ) (hh:h≤14):90≤(e93.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e93,Parameters.cutoff,AQ.reserve]
theorem GEO:AM.AW e93.cutoff 131071 1775 28 14 90=153401238657240:=by decide+kernel
theorem rank_e93:AR.rankBound 66 1775 28 14 90=584553405:=by decide+kernel
theorem GVK:Dimension e93 164070856920:=by
  exact AZ e93 164070856920 153401238657240 584553405
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e93 GEO rank_e93 (by decide)

def e94:Parameters:=⟨48,1383,20,9,65,1,2⟩
theorem shape_e94:Shape e94:=by constructor<;>decide+kernel
theorem middle_e94 (h:ℕ) (hh:h≤9):65≤(e94.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e94,Parameters.cutoff,AQ.reserve]
theorem FZY:AM.AW e94.cutoff 131071 1383 20 9 65=34323214382853:=by decide+kernel
theorem rank_e94:AR.rankBound 48 1383 20 9 65=130793179:=by decide+kernel
theorem GXL:Dimension e94 36567267077:=by
  exact AZ e94 36567267077 34323214382853 130793179
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e94 FZY rank_e94 (by decide)

def e95:Parameters:=⟨76,1230,31,14,104,2,3⟩
theorem shape_e95:Shape e95:=by constructor<;>decide+kernel
theorem middle_e95 (h:ℕ) (hh:h≤14):104≤(e95.cutoff h+31-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e95,Parameters.cutoff,AQ.reserve]
theorem FYZ:AM.AW e95.cutoff 131071 1230 31 14 104=169010552523529:=by decide+kernel
theorem rank_e95:AR.rankBound 76 1230 31 14 104=643660422:=by decide+kernel
theorem GTJ:Dimension e95 278834858761:=by
  exact AZ e95 278834858761 169010552523529 643660422
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e95 FYZ rank_e95 (by decide)

def e96:Parameters:=⟨86,1736,38,17,117,3,4⟩
theorem shape_e96:Shape e96:=by constructor<;>decide+kernel
theorem middle_e96 (h:ℕ) (hh:h≤17):117≤(e96.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e96,Parameters.cutoff,AQ.reserve]
theorem FZM:AM.AW e96.cutoff 131071 1736 38 17 117=436042523528760:=by decide+kernel
theorem rank_e96:AR.rankBound 86 1736 38 17 117=1662210726:=by decide+kernel
theorem GUN:Dimension e96 303954972216:=by
  exact AZ e96 303954972216 436042523528760 1662210726
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e96 FZM rank_e96 (by decide)

def e97:Parameters:=⟨68,1859,27,13,93,2,3⟩
theorem shape_e97:Shape e97:=by constructor<;>decide+kernel
theorem middle_e97 (h:ℕ) (hh:h≤13):93≤(e97.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e97,Parameters.cutoff,AQ.reserve]
theorem GEM:AM.AW e97.cutoff 131071 1859 27 13 93=162893093542101:=by decide+kernel
theorem rank_e97:AR.rankBound 68 1859 27 13 93=620556249:=by decide+kernel
theorem GVS:Dimension e97 217996204245:=by
  exact AZ e97 217996204245 162893093542101 620556249
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e97 GEM rank_e97 (by decide)

def e98:Parameters:=⟨68,1502,28,12,93,2,3⟩
theorem shape_e98:Shape e98:=by constructor<;>decide+kernel
theorem middle_e98 (h:ℕ) (hh:h≤12):93≤(e98.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e98,Parameters.cutoff,AQ.reserve]
theorem GDT:AM.AW e98.cutoff 131071 1502 28 12 93=136146542483638:=by decide+kernel
theorem rank_e98:AR.rankBound 68 1502 28 12 93=518933981:=by decide+kernel
theorem GUG:Dimension e98 111112968374:=by
  exact AZ e98 111112968374 136146542483638 518933981
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e98 GDT rank_e98 (by decide)

def e99:Parameters:=⟨48,1353,20,9,65,1,2⟩
theorem shape_e99:Shape e99:=by constructor<;>decide+kernel
theorem middle_e99 (h:ℕ) (hh:h≤9):65≤(e99.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e99,Parameters.cutoff,AQ.reserve]
theorem FYX:AM.AW e99.cutoff 131071 1353 20 9 65=33563919453273:=by decide+kernel
theorem rank_e99:AR.rankBound 48 1353 20 9 65=127909549:=by decide+kernel
theorem GWA:Dimension e99 33198640217:=by
  exact AZ e99 33198640217 33563919453273 127909549
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e99 FYX rank_e99 (by decide)

def e100:Parameters:=⟨87,1683,38,17,119,3,4⟩
theorem shape_e100:Shape e100:=by constructor<;>decide+kernel
theorem middle_e100 (h:ℕ) (hh:h≤17):119≤(e100.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e100,Parameters.cutoff,AQ.reserve]
theorem FQD:AM.AW e100.cutoff 131071 1683 38 17 119=433962570598026:=by decide+kernel
theorem rank_e100:AR.rankBound 87 1683 38 17 119=1654134543:=by decide+kernel
theorem GRP:Dimension e100 341124957834:=by
  exact AZ e100 341124957834 433962570598026 1654134543
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e100 FQD rank_e100 (by decide)

def e101:Parameters:=⟨84,2146,34,15,115,3,4⟩
theorem shape_e101:Shape e101:=by constructor<;>decide+kernel
theorem middle_e101 (h:ℕ) (hh:h≤15):115≤(e101.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e101,Parameters.cutoff,AQ.reserve]
theorem FQO:AM.AW e101.cutoff 131071 2146 34 15 115=431442240728426:=by decide+kernel
theorem rank_e101:AR.rankBound 84 2146 34 15 115=1644597637:=by decide+kernel
theorem GMY:Dimension e101 320837774698:=by
  exact AZ e101 320837774698 431442240728426 1644597637
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e101 FQO rank_e101 (by decide)

def e102:Parameters:=⟨140,1193,60,28,192,4,5⟩
theorem shape_e102:Shape e102:=by constructor<;>decide+kernel
theorem middle_e102 (h:ℕ) (hh:h≤28):192≤(e102.cutoff h+60-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e102,Parameters.cutoff,AQ.reserve]
theorem FVI:AM.AW e102.cutoff 131071 1193 60 28 192=1858566156402180:=by decide+kernel
theorem rank_e102:AR.rankBound 140 1193 60 28 192=7089579150:=by decide+kernel
theorem GMQ:Dimension e102 75519704580:=by
  exact AZ e102 75519704580 1858566156402180 7089579150
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e102 FVI rank_e102 (by decide)

def e103:Parameters:=⟨68,1770,27,13,93,2,3⟩
theorem shape_e103:Shape e103:=by constructor<;>decide+kernel
theorem middle_e103 (h:ℕ) (hh:h≤13):93≤(e103.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e103,Parameters.cutoff,AQ.reserve]
theorem FWC:AM.AW e103.cutoff 131071 1770 27 13 93=154930817026782:=by decide+kernel
theorem rank_e103:AR.rankBound 68 1770 27 13 93=590334608:=by decide+kernel
theorem GPO:Dimension e103 178141547230:=by
  exact AZ e103 178141547230 154930817026782 590334608
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e103 FWC rank_e103 (by decide)

def e104:Parameters:=⟨68,1470,28,12,93,2,3⟩
theorem shape_e104:Shape e104:=by constructor<;>decide+kernel
theorem middle_e104 (h:ℕ) (hh:h≤12):93≤(e104.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e104,Parameters.cutoff,AQ.reserve]
theorem FOO:AM.AW e104.cutoff 131071 1470 28 12 93=133169631406166:=by decide+kernel
theorem rank_e104:AR.rankBound 68 1470 28 12 93=507638045:=by decide+kernel
theorem GMF:Dimension e104 95363737686:=by
  exact AZ e104 95363737686 133169631406166 507638045
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e104 FOO rank_e104 (by decide)

def e105:Parameters:=⟨48,1323,20,9,65,1,2⟩
theorem shape_e105:Shape e105:=by constructor<;>decide+kernel
theorem middle_e105 (h:ℕ) (hh:h≤9):65≤(e105.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e105,Parameters.cutoff,AQ.reserve]
theorem FQE:AM.AW e105.cutoff 131071 1323 20 9 65=32804624523693:=by decide+kernel
theorem rank_e105:AR.rankBound 48 1323 20 9 65=125025919:=by decide+kernel
theorem GQZ:Dimension e105 29830013357:=by
  exact AZ e105 29830013357 32804624523693 125025919
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e105 FQE rank_e105 (by decide)

def e106:Parameters:=⟨76,1181,31,14,104,2,3⟩
theorem shape_e106:Shape e106:=by constructor<;>decide+kernel
theorem middle_e106 (h:ℕ) (hh:h≤14):104≤(e106.cutoff h+31-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e106,Parameters.cutoff,AQ.reserve]
theorem FUR:AM.AW e106.cutoff 131071 1181 31 14 104=162032859428037:=by decide+kernel
theorem rank_e106:AR.rankBound 76 1181 31 14 104=617252068:=by decide+kernel
theorem GKA:Dimension e106 223933314245:=by
  exact AZ e106 223933314245 162032859428037 617252068
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e106 FUR rank_e106 (by decide)

def e107:Parameters:=⟨68,1364,28,12,93,2,3⟩
theorem shape_e107:Shape e107:=by constructor<;>decide+kernel
theorem middle_e107 (h:ℕ) (hh:h≤12):93≤(e107.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e107,Parameters.cutoff,AQ.reserve]
theorem FRW:AM.AW e107.cutoff 131071 1364 28 12 93=123308613462040:=by decide+kernel
theorem rank_e107:AR.rankBound 68 1364 28 12 93=470220257:=by decide+kernel
theorem GKX:Dimension e107 43194411032:=by
  exact AZ e107 43194411032 123308613462040 470220257
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e107 FRW rank_e107 (by decide)

def e108:Parameters:=⟨68,1462,28,12,93,2,3⟩
theorem shape_e108:Shape e108:=by constructor<;>decide+kernel
theorem middle_e108 (h:ℕ) (hh:h≤12):93≤(e108.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e108,Parameters.cutoff,AQ.reserve]
theorem FOW:AM.AW e108.cutoff 131071 1462 28 12 93=132425403636798:=by decide+kernel
theorem rank_e108:AR.rankBound 68 1462 28 12 93=504814061:=by decide+kernel
theorem GMN:Dimension e108 91426430014:=by
  exact AZ e108 91426430014 132425403636798 504814061
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e108 FOW rank_e108 (by decide)

def e109:Parameters:=⟨76,1242,31,14,104,2,3⟩
theorem shape_e109:Shape e109:=by constructor<;>decide+kernel
theorem middle_e109 (h:ℕ) (hh:h≤14):104≤(e109.cutoff h+31-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e109,Parameters.cutoff,AQ.reserve]
theorem FTY:AM.AW e109.cutoff 131071 1242 31 14 104=170719375322425:=by decide+kernel
theorem rank_e109:AR.rankBound 76 1242 31 14 104=650127774:=by decide+kernel
theorem GQP:Dimension e109 292280134969:=by
  exact AZ e109 292280134969 170719375322425 650127774
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e109 FTY rank_e109 (by decide)

def e110:Parameters:=⟨76,1107,32,15,104,2,3⟩
theorem shape_e110:Shape e110:=by constructor<;>decide+kernel
theorem middle_e110 (h:ℕ) (hh:h≤15):104≤(e110.cutoff h+32-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e110,Parameters.cutoff,AQ.reserve]
theorem FVW:AM.AW e110.cutoff 131071 1107 32 15 104=159796438347092:=by decide+kernel
theorem rank_e110:AR.rankBound 76 1107 32 15 104=608799151:=by decide+kernel
theorem GNP:Dimension e110 203393707348:=by
  exact AZ e110 203393707348 159796438347092 608799151
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e110 FVW rank_e110 (by decide)

def e111:Parameters:=⟨52,974,22,10,71,1,2⟩
theorem shape_e111:Shape e111:=by constructor<;>decide+kernel
theorem middle_e111 (h:ℕ) (hh:h≤10):71≤(e111.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e111,Parameters.cutoff,AQ.reserve]
theorem FQI:AM.AW e111.cutoff 131071 974 22 10 71=33241261121725:=by decide+kernel
theorem rank_e111:AR.rankBound 52 974 22 10 71=126630039:=by decide+kernel
theorem GOU:Dimension e111 45956178109:=by
  exact AZ e111 45956178109 33241261121725 126630039
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e111 FQI rank_e111 (by decide)

def e112:Parameters:=⟨50,1374,20,9,68,1,2⟩
theorem shape_e112:Shape e112:=by constructor<;>decide+kernel
theorem middle_e112 (h:ℕ) (hh:h≤9):68≤(e112.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e112,Parameters.cutoff,AQ.reserve]
theorem FYN:AM.AW e112.cutoff 131071 1374 20 9 68=37466137306843:=by decide+kernel
theorem rank_e112:AR.rankBound 50 1374 20 9 68=142680129:=by decide+kernel
theorem GPH:Dimension e112 63397570267:=by
  exact AZ e112 63397570267 37466137306843 142680129
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e112 FYN rank_e112 (by decide)

def e113:Parameters:=⟨50,1019,20,9,68,1,2⟩
theorem shape_e113:Shape e113:=by constructor<;>decide+kernel
theorem middle_e113 (h:ℕ) (hh:h≤9):68≤(e113.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e113,Parameters.cutoff,AQ.reserve]
theorem FUO:AM.AW e113.cutoff 131071 1019 20 9 68=27585943344248:=by decide+kernel
theorem rank_e113:AR.rankBound 50 1019 20 9 68=105190709:=by decide+kernel
theorem GQW:Dimension e113 10830124152:=by
  exact AZ e113 10830124152 27585943344248 105190709
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e113 FUO rank_e113 (by decide)

def e114:Parameters:=⟨52,954,22,10,71,1,2⟩
theorem shape_e114:Shape e114:=by constructor<;>decide+kernel
theorem middle_e114 (h:ℕ) (hh:h≤10):71≤(e114.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e114,Parameters.cutoff,AQ.reserve]
theorem FTU:AM.AW e114.cutoff 131071 954 22 10 71=32537487704945:=by decide+kernel
theorem rank_e114:AR.rankBound 52 954 22 10 71=123963059:=by decide+kernel
theorem GKC:Dimension e114 41315566449:=by
  exact AZ e114 41315566449 32537487704945 123963059
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e114 FTU rank_e114 (by decide)

def e115:Parameters:=⟨78,942,34,16,107,2,3⟩
theorem shape_e115:Shape e115:=by constructor<;>decide+kernel
theorem middle_e115 (h:ℕ) (hh:h≤16):107≤(e115.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e115,Parameters.cutoff,AQ.reserve]
theorem FOT:AM.AW e115.cutoff 131071 942 34 16 107=157266311932685:=by decide+kernel
theorem rank_e115:AR.rankBound 78 942 34 16 107=599563266:=by decide+kernel
theorem GSD:Dimension e115 94399130381:=by
  exact AZ e115 94399130381 157266311932685 599563266
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e115 FOT rank_e115 (by decide)

def e116:Parameters:=⟨80,883,34,15,109,2,3⟩
theorem shape_e116:Shape e116:=by constructor<;>decide+kernel
theorem middle_e116 (h:ℕ) (hh:h≤15):109≤(e116.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e116,Parameters.cutoff,AQ.reserve]
theorem FPW:AM.AW e116.cutoff 131071 883 34 15 109=154347275315306:=by decide+kernel
theorem rank_e116:AR.rankBound 80 883 34 15 109=588692801:=by decide+kernel
theorem GRQ:Dimension e116 24989689962:=by
  exact AZ e116 24989689962 154347275315306 588692801
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e116 FPW rank_e116 (by decide)

def e117:Parameters:=⟨82,853,36,16,112,2,3⟩
theorem shape_e117:Shape e117:=by constructor<;>decide+kernel
theorem middle_e117 (h:ℕ) (hh:h≤16):112≤(e117.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e117,Parameters.cutoff,AQ.reserve]
theorem FPM:AM.AW e117.cutoff 131071 853 36 16 112=172087089029947:=by decide+kernel
theorem rank_e117:AR.rankBound 82 853 36 16 112=656228818:=by decide+kernel
theorem GOP:Dimension e117 60641764155:=by
  exact AZ e117 60641764155 172087089029947 656228818
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e117 FPM rank_e117 (by decide)

def e118:Parameters:=⟨82,841,36,16,112,2,3⟩
theorem shape_e118:Shape e118:=by constructor<;>decide+kernel
theorem middle_e118 (h:ℕ) (hh:h≤16):112≤(e118.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e118,Parameters.cutoff,AQ.reserve]
theorem FUT:AM.AW e118.cutoff 131071 841 36 16 112=169523719962595:=by decide+kernel
theorem rank_e118:AR.rankBound 82 841 36 16 112=646546426:=by decide+kernel
theorem GJS:Dimension e118 35453665251:=by
  exact AZ e118 35453665251 169523719962595 646546426
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e118 FUT rank_e118 (by decide)

def e119:Parameters:=⟨85,802,37,17,116,2,3⟩
theorem shape_e119:Shape e119:=by constructor<;>decide+kernel
theorem middle_e119 (h:ℕ) (hh:h≤17):116≤(e119.cutoff h+37-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e119,Parameters.cutoff,AQ.reserve]
theorem FXO:AM.AW e119.cutoff 131071 802 37 17 116=183536971534689:=by decide+kernel
theorem rank_e119:AR.rankBound 85 802 37 17 116=700100805:=by decide+kernel
theorem GOI:Dimension e119 9746108769:=by
  exact AZ e119 9746108769 183536971534689 700100805
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e119 FXO rank_e119 (by decide)

def e120:Parameters:=⟨78,946,34,15,107,2,3⟩
theorem shape_e120:Shape e120:=by constructor<;>decide+kernel
theorem middle_e120 (h:ℕ) (hh:h≤15):107≤(e120.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e120,Parameters.cutoff,AQ.reserve]
theorem FPV:AM.AW e120.cutoff 131071 946 34 15 107=156514951038662:=by decide+kernel
theorem rank_e120:AR.rankBound 78 946 34 15 107=596693596:=by decide+kernel
theorem GQG:Dimension e120 95305008838:=by
  exact AZ e120 95305008838 156514951038662 596693596
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e120 FPV rank_e120 (by decide)

def e121:Parameters:=⟨82,839,36,16,112,2,3⟩
theorem shape_e121:Shape e121:=by constructor<;>decide+kernel
theorem middle_e121 (h:ℕ) (hh:h≤16):112≤(e121.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e121,Parameters.cutoff,AQ.reserve]
theorem FRY:AM.AW e121.cutoff 131071 839 36 16 112=169096491784703:=by decide+kernel
theorem rank_e121:AR.rankBound 82 839 36 16 112=644932694:=by decide+kernel
theorem GOX:Dimension e121 31255648767:=by
  exact AZ e121 31255648767 169096491784703 644932694
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e121 FRY rank_e121 (by decide)

def e122:Parameters:=⟨76,1024,34,16,104,2,3⟩
theorem shape_e122:Shape e122:=by constructor<;>decide+kernel
theorem middle_e122 (h:ℕ) (hh:h≤16):104≤(e122.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e122,Parameters.cutoff,AQ.reserve]
theorem FWI:AM.AW e122.cutoff 131071 1024 34 16 104=161560634678996:=by decide+kernel
theorem rank_e122:AR.rankBound 76 1024 34 16 104=615744752:=by decide+kernel
theorem GQB:Dimension e122 146842410708:=by
  exact AZ e122 146842410708 161560634678996 615744752
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e122 FWI rank_e122 (by decide)

def e123:Parameters:=⟨100,2460,42,19,136,4,5⟩
theorem shape_e123:Shape e123:=by constructor<;>decide+kernel
theorem middle_e123 (h:ℕ) (hh:h≤19):136≤(e123.cutoff h+42-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e123,Parameters.cutoff,AQ.reserve]
theorem FRK:AM.AW e123.cutoff 131071 2460 42 19 136=1033076994112211:=by decide+kernel
theorem rank_e123:AR.rankBound 100 2460 42 19 136=3938485140:=by decide+kernel
theorem GQN:Dimension e123 626745572051:=by
  exact AZ e123 626745572051 1033076994112211 3938485140
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e123 FRK rank_e123 (by decide)

def e124:Parameters:=⟨52,896,22,10,71,1,2⟩
theorem shape_e124:Shape e124:=by constructor<;>decide+kernel
theorem middle_e124 (h:ℕ) (hh:h≤10):71≤(e124.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e124,Parameters.cutoff,AQ.reserve]
theorem FSI:AM.AW e124.cutoff 131071 896 22 10 71=30496544796283:=by decide+kernel
theorem rank_e124:AR.rankBound 52 896 22 10 71=116228817:=by decide+kernel
theorem GJB:Dimension e124 27857792635:=by
  exact AZ e124 27857792635 30496544796283 116228817
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e124 FSI rank_e124 (by decide)

def e125:Parameters:=⟨58,637,25,11,79,1,2⟩
theorem shape_e125:Shape e125:=by constructor<;>decide+kernel
theorem middle_e125 (h:ℕ) (hh:h≤11):79≤(e125.cutoff h+25-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e125,Parameters.cutoff,AQ.reserve]
theorem FXP:AM.AW e125.cutoff 131071 637 25 11 79=33036296022259:=by decide+kernel
theorem rank_e125:AR.rankBound 58 637 25 11 79=126004445:=by decide+kernel
theorem GPN:Dimension e125 4986792179:=by
  exact AZ e125 4986792179 33036296022259 126004445
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e125 FXP rank_e125 (by decide)

def e126:Parameters:=⟨84,1911,36,17,115,3,4⟩
theorem shape_e126:Shape e126:=by constructor<;>decide+kernel
theorem middle_e126 (h:ℕ) (hh:h≤17):115≤(e126.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e126,Parameters.cutoff,AQ.reserve]
theorem FYH:AM.AW e126.cutoff 131071 1911 36 17 115=422372617086876:=by decide+kernel
theorem rank_e126:AR.rankBound 84 1911 36 17 115=1610175981:=by decide+kernel
theorem GQL:Dimension e126 274644723612:=by
  exact AZ e126 274644723612 422372617086876 1610175981
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e126 FYH rank_e126 (by decide)

def e127:Parameters:=⟨84,1896,36,17,115,3,4⟩
theorem shape_e127:Shape e127:=by constructor<;>decide+kernel
theorem middle_e127 (h:ℕ) (hh:h≤17):115≤(e127.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e127,Parameters.cutoff,AQ.reserve]
theorem FSA:AM.AW e127.cutoff 131071 1896 36 17 115=418971395859576:=by decide+kernel
theorem rank_e127:AR.rankBound 84 1896 36 17 115=1597264761:=by decide+kernel
theorem GPI:Dimension e127 258022351992:=by
  exact AZ e127 258022351992 418971395859576 1597264761
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e127 FSA rank_e127 (by decide)

def e128:Parameters:=⟨84,2436,34,15,115,3,4⟩
theorem shape_e128:Shape e128:=by constructor<;>decide+kernel
theorem middle_e128 (h:ℕ) (hh:h≤15):115≤(e128.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e128,Parameters.cutoff,AQ.reserve]
theorem FQQ:AM.AW e128.cutoff 131071 2436 34 15 115=491070133766146:=by decide+kernel
theorem rank_e128:AR.rankBound 84 2436 34 15 115=1871005277:=by decide+kernel
theorem GQM:Dimension e128 597326432258:=by
  exact AZ e128 597326432258 491070133766146 1871005277
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e128 FQQ rank_e128 (by decide)

def e129:Parameters:=⟨84,2109,34,15,115,3,4⟩
theorem shape_e129:Shape e129:=by constructor<;>decide+kernel
theorem middle_e129 (h:ℕ) (hh:h≤15):115≤(e129.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e129,Parameters.cutoff,AQ.reserve]
theorem FTX:AM.AW e129.cutoff 131071 2109 34 15 115=423834544030510:=by decide+kernel
theorem rank_e129:AR.rankBound 84 2109 34 15 115=1615711145:=by decide+kernel
theorem GOO:Dimension e129 285561635630:=by
  exact AZ e129 285561635630 423834544030510 1615711145
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e129 FTX rank_e129 (by decide)

def e130:Parameters:=⟨84,2425,34,15,115,3,4⟩
theorem shape_e130:Shape e130:=by constructor<;>decide+kernel
theorem middle_e130 (h:ℕ) (hh:h≤15):115≤(e130.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e130,Parameters.cutoff,AQ.reserve]
theorem FVJ:AM.AW e130.cutoff 131071 2425 34 15 115=488808386099198:=by decide+kernel
theorem rank_e130:AR.rankBound 84 2425 34 15 115=1862417401:=by decide+kernel
theorem GSA:Dimension e130 586838931454:=by
  exact AZ e130 586838931454 488808386099198 1862417401
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e130 FVJ rank_e130 (by decide)

def e131:Parameters:=⟨84,2104,34,15,115,3,4⟩
theorem shape_e131:Shape e131:=by constructor<;>decide+kernel
theorem middle_e131 (h:ℕ) (hh:h≤15):115≤(e131.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e131,Parameters.cutoff,AQ.reserve]
theorem FSL:AM.AW e131.cutoff 131071 2104 34 15 115=422806476909170:=by decide+kernel
theorem rank_e131:AR.rankBound 84 2104 34 15 115=1611807565:=by decide+kernel
theorem GMC:Dimension e131 280794589810:=by
  exact AZ e131 280794589810 422806476909170 1611807565
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e131 FSL rank_e131 (by decide)

def e132:Parameters:=⟨84,2415,34,15,115,3,4⟩
theorem shape_e132:Shape e132:=by constructor<;>decide+kernel
theorem middle_e132 (h:ℕ) (hh:h≤15):115≤(e132.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e132,Parameters.cutoff,AQ.reserve]
theorem FYO:AM.AW e132.cutoff 131071 2415 34 15 115=486752251856518:=by decide+kernel
theorem rank_e132:AR.rankBound 84 2415 34 15 115=1854610241:=by decide+kernel
theorem GJR:Dimension e132 577304839814:=by
  exact AZ e132 577304839814 486752251856518 1854610241
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e132 FYO rank_e132 (by decide)

def e133:Parameters:=⟨84,2099,34,15,115,3,4⟩
theorem shape_e133:Shape e133:=by constructor<;>decide+kernel
theorem middle_e133 (h:ℕ) (hh:h≤15):115≤(e133.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e133,Parameters.cutoff,AQ.reserve]
theorem FYF:AM.AW e133.cutoff 131071 2099 34 15 115=421778409787830:=by decide+kernel
theorem rank_e133:AR.rankBound 84 2099 34 15 115=1607903985:=by decide+kernel
theorem GLK:Dimension e133 276027543990:=by
  exact AZ e133 276027543990 421778409787830 1607903985
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e133 FYF rank_e133 (by decide)

def e134:Parameters:=⟨84,2404,34,15,115,3,4⟩
theorem shape_e134:Shape e134:=by constructor<;>decide+kernel
theorem middle_e134 (h:ℕ) (hh:h≤15):115≤(e134.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e134,Parameters.cutoff,AQ.reserve]
theorem FPF:AM.AW e134.cutoff 131071 2404 34 15 115=484490504189570:=by decide+kernel
theorem rank_e134:AR.rankBound 84 2404 34 15 115=1846022365:=by decide+kernel
theorem GPJ:Dimension e134 566817339010:=by
  exact AZ e134 566817339010 484490504189570 1846022365
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e134 FPF rank_e134 (by decide)

def e135:Parameters:=⟨84,2094,34,15,115,3,4⟩
theorem shape_e135:Shape e135:=by constructor<;>decide+kernel
theorem middle_e135 (h:ℕ) (hh:h≤15):115≤(e135.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e135,Parameters.cutoff,AQ.reserve]
theorem FUA:AM.AW e135.cutoff 131071 2094 34 15 115=420750342666490:=by decide+kernel
theorem rank_e135:AR.rankBound 84 2094 34 15 115=1604000405:=by decide+kernel
theorem GIZ:Dimension e135 271260498170:=by
  exact AZ e135 271260498170 420750342666490 1604000405
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e135 FUA rank_e135 (by decide)

def e136:Parameters:=⟨84,2393,34,15,115,3,4⟩
theorem shape_e136:Shape e136:=by constructor<;>decide+kernel
theorem middle_e136 (h:ℕ) (hh:h≤15):115≤(e136.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e136,Parameters.cutoff,AQ.reserve]
theorem FTA:AM.AW e136.cutoff 131071 2393 34 15 115=482228756522622:=by decide+kernel
theorem rank_e136:AR.rankBound 84 2393 34 15 115=1837434489:=by decide+kernel
theorem GJC:Dimension e136 556329838206:=by
  exact AZ e136 556329838206 482228756522622 1837434489
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e136 FTA rank_e136 (by decide)

def e137:Parameters:=⟨84,2089,34,15,115,3,4⟩
theorem shape_e137:Shape e137:=by constructor<;>decide+kernel
theorem middle_e137 (h:ℕ) (hh:h≤15):115≤(e137.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e137,Parameters.cutoff,AQ.reserve]
theorem FRB:AM.AW e137.cutoff 131071 2089 34 15 115=419722275545150:=by decide+kernel
theorem rank_e137:AR.rankBound 84 2089 34 15 115=1600096825:=by decide+kernel
theorem GSF:Dimension e137 266493452350:=by
  exact AZ e137 266493452350 419722275545150 1600096825
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e137 FRB rank_e137 (by decide)

def e138:Parameters:=⟨84,2383,34,15,115,3,4⟩
theorem shape_e138:Shape e138:=by constructor<;>decide+kernel
theorem middle_e138 (h:ℕ) (hh:h≤15):115≤(e138.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e138,Parameters.cutoff,AQ.reserve]
theorem FQB:AM.AW e138.cutoff 131071 2383 34 15 115=480172622279942:=by decide+kernel
theorem rank_e138:AR.rankBound 84 2383 34 15 115=1829627329:=by decide+kernel
theorem GKM:Dimension e138 546795746566:=by
  exact AZ e138 546795746566 480172622279942 1829627329
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e138 FQB rank_e138 (by decide)

def e139:Parameters:=⟨84,2084,34,15,115,3,4⟩
theorem shape_e139:Shape e139:=by constructor<;>decide+kernel
theorem middle_e139 (h:ℕ) (hh:h≤15):115≤(e139.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e139,Parameters.cutoff,AQ.reserve]
theorem FTD:AM.AW e139.cutoff 131071 2084 34 15 115=418694208423810:=by decide+kernel
theorem rank_e139:AR.rankBound 84 2084 34 15 115=1596193245:=by decide+kernel
theorem GPF:Dimension e139 261726406530:=by
  exact AZ e139 261726406530 418694208423810 1596193245
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e139 FTD rank_e139 (by decide)

def e140:Parameters:=⟨84,1881,36,16,115,3,4⟩
theorem shape_e140:Shape e140:=by constructor<;>decide+kernel
theorem middle_e140 (h:ℕ) (hh:h≤16):115≤(e140.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e140,Parameters.cutoff,AQ.reserve]
theorem FQC:AM.AW e140.cutoff 131071 1881 36 16 115=412145957069159:=by decide+kernel
theorem rank_e140:AR.rankBound 84 1881 36 16 115=1571298939:=by decide+kernel
theorem GPX:Dimension e140 239368003943:=by
  exact AZ e140 239368003943 412145957069159 1571298939
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e140 FQC rank_e140 (by decide)

def e141:Parameters:=⟨84,1863,36,16,115,3,4⟩
theorem shape_e141:Shape e141:=by constructor<;>decide+kernel
theorem middle_e141 (h:ℕ) (hh:h≤16):115≤(e141.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e141,Parameters.cutoff,AQ.reserve]
theorem FWN:AM.AW e141.cutoff 131071 1863 36 16 115=408098135493347:=by decide+kernel
theorem rank_e141:AR.rankBound 84 1863 36 16 115=1555933221:=by decide+kernel
theorem GPK:Dimension e141 219577207523:=by
  exact AZ e141 219577207523 408098135493347 1555933221
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e141 FWN rank_e141 (by decide)

def e142:Parameters:=⟨88,2058,36,17,120,3,4⟩
theorem shape_e142:Shape e142:=by constructor<;>decide+kernel
theorem middle_e142 (h:ℕ) (hh:h≤17):120≤(e142.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e142,Parameters.cutoff,AQ.reserve]
theorem FRI:AM.AW e142.cutoff 131071 2058 36 17 120=507936383603391:=by decide+kernel
theorem rank_e142:AR.rankBound 88 2058 36 17 120=1934548994:=by decide+kernel
theorem GJT:Dimension e142 805972120255:=by
  exact AZ e142 805972120255 507936383603391 1934548994
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e142 FRI rank_e142 (by decide)

def e143:Parameters:=⟨84,2168,34,15,115,3,4⟩
theorem shape_e143:Shape e143:=by constructor<;>decide+kernel
theorem middle_e143 (h:ℕ) (hh:h≤15):115≤(e143.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e143,Parameters.cutoff,AQ.reserve]
theorem FTB:AM.AW e143.cutoff 131071 2168 34 15 115=435965736062322:=by decide+kernel
theorem rank_e143:AR.rankBound 84 2168 34 15 115=1661773389:=by decide+kernel
theorem GOD:Dimension e143 341812776306:=by
  exact AZ e143 341812776306 435965736062322 1661773389
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e143 FTB rank_e143 (by decide)

def e144:Parameters:=⟨84,2315,34,15,115,3,4⟩
theorem shape_e144:Shape e144:=by constructor<;>decide+kernel
theorem middle_e144 (h:ℕ) (hh:h≤15):115≤(e144.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e144,Parameters.cutoff,AQ.reserve]
theorem FWM:AM.AW e144.cutoff 131071 2315 34 15 115=466190909429718:=by decide+kernel
theorem rank_e144:AR.rankBound 84 2315 34 15 115=1776538641:=by decide+kernel
theorem GPL:Dimension e144 481963923414:=by
  exact AZ e144 481963923414 466190909429718 1776538641
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e144 FWM rank_e144 (by decide)

def e145:Parameters:=⟨84,2164,34,15,115,3,4⟩
theorem shape_e145:Shape e145:=by constructor<;>decide+kernel
theorem middle_e145 (h:ℕ) (hh:h≤15):115≤(e145.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e145,Parameters.cutoff,AQ.reserve]
theorem FUH:AM.AW e145.cutoff 131071 2164 34 15 115=435143282365250:=by decide+kernel
theorem rank_e145:AR.rankBound 84 2164 34 15 115=1658650525:=by decide+kernel
theorem GNJ:Dimension e145 337999139650:=by
  exact AZ e145 337999139650 435143282365250 1658650525
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e145 FUH rank_e145 (by decide)

def e146:Parameters:=⟨84,2161,34,15,115,3,4⟩
theorem shape_e146:Shape e146:=by constructor<;>decide+kernel
theorem middle_e146 (h:ℕ) (hh:h≤15):115≤(e146.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e146,Parameters.cutoff,AQ.reserve]
theorem FWK:AM.AW e146.cutoff 131071 2161 34 15 115=434526442092446:=by decide+kernel
theorem rank_e146:AR.rankBound 84 2161 34 15 115=1656308377:=by decide+kernel
theorem GMI:Dimension e146 335138912158:=by
  exact AZ e146 335138912158 434526442092446 1656308377
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e146 FWK rank_e146 (by decide)

def e147:Parameters:=⟨84,2304,34,15,115,3,4⟩
theorem shape_e147:Shape e147:=by constructor<;>decide+kernel
theorem middle_e147 (h:ℕ) (hh:h≤15):115≤(e147.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e147,Parameters.cutoff,AQ.reserve]
theorem FXS:AM.AW e147.cutoff 131071 2304 34 15 115=463929161762770:=by decide+kernel
theorem rank_e147:AR.rankBound 84 2304 34 15 115=1767950765:=by decide+kernel
theorem GLL:Dimension e147 471476422610:=by
  exact AZ e147 471476422610 463929161762770 1767950765
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e147 FXS rank_e147 (by decide)

def e148:Parameters:=⟨84,2156,34,15,115,3,4⟩
theorem shape_e148:Shape e148:=by constructor<;>decide+kernel
theorem middle_e148 (h:ℕ) (hh:h≤15):115≤(e148.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e148,Parameters.cutoff,AQ.reserve]
theorem FUV:AM.AW e148.cutoff 131071 2156 34 15 115=433498374971106:=by decide+kernel
theorem rank_e148:AR.rankBound 84 2156 34 15 115=1652404797:=by decide+kernel
theorem GND:Dimension e148 330371866338:=by
  exact AZ e148 330371866338 433498374971106 1652404797
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e148 FUV rank_e148 (by decide)

def e149:Parameters:=⟨84,2153,34,15,115,3,4⟩
theorem shape_e149:Shape e149:=by constructor<;>decide+kernel
theorem middle_e149 (h:ℕ) (hh:h≤15):115≤(e149.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e149,Parameters.cutoff,AQ.reserve]
theorem FYE:AM.AW e149.cutoff 131071 2153 34 15 115=432881534698302:=by decide+kernel
theorem rank_e149:AR.rankBound 84 2153 34 15 115=1650062649:=by decide+kernel
theorem GNK:Dimension e149 327511638846:=by
  exact AZ e149 327511638846 432881534698302 1650062649
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e149 FYE rank_e149 (by decide)

def e150:Parameters:=⟨68,1322,28,12,93,2,3⟩
theorem shape_e150:Shape e150:=by constructor<;>decide+kernel
theorem middle_e150 (h:ℕ) (hh:h≤12):93≤(e150.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e150,Parameters.cutoff,AQ.reserve]
theorem FSW:AM.AW e150.cutoff 131071 1322 28 12 93=119401417672858:=by decide+kernel
theorem rank_e150:AR.rankBound 68 1322 28 12 93=455394341:=by decide+kernel
theorem GJZ:Dimension e150 22523545754:=by
  exact AZ e150 22523545754 119401417672858 455394341
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e150 FSW rank_e150 (by decide)

def e151:Parameters:=⟨87,1713,38,17,119,3,4⟩
theorem shape_e151:Shape e151:=by constructor<;>decide+kernel
theorem middle_e151 (h:ℕ) (hh:h≤17):119≤(e151.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e151,Parameters.cutoff,AQ.reserve]
theorem FTK:AM.AW e151.cutoff 131071 1713 38 17 119=441936114765306:=by decide+kernel
theorem rank_e151:AR.rankBound 87 1713 38 17 119=1684376613:=by decide+kernel
theorem GLM:Dimension e151 386891927034:=by
  exact AZ e151 386891927034 441936114765306 1684376613
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e151 FTK rank_e151 (by decide)

def e152:Parameters:=⟨68,1320,28,12,93,2,3⟩
theorem shape_e152:Shape e152:=by constructor<;>decide+kernel
theorem middle_e152 (h:ℕ) (hh:h≤12):93≤(e152.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e152,Parameters.cutoff,AQ.reserve]
theorem FXN:AM.AW e152.cutoff 131071 1320 28 12 93=119215360730516:=by decide+kernel
theorem rank_e152:AR.rankBound 68 1320 28 12 93=454688345:=by decide+kernel
theorem GQJ:Dimension e152 21539218836:=by
  exact AZ e152 21539218836 119215360730516 454688345
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e152 FXN rank_e152 (by decide)

def e153:Parameters:=⟨84,2147,34,15,115,3,4⟩
theorem shape_e153:Shape e153:=by constructor<;>decide+kernel
theorem middle_e153 (h:ℕ) (hh:h≤15):115≤(e153.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e153,Parameters.cutoff,AQ.reserve]
theorem FWQ:AM.AW e153.cutoff 131071 2147 34 15 115=431647854152694:=by decide+kernel
theorem rank_e153:AR.rankBound 84 2147 34 15 115=1645378353:=by decide+kernel
theorem GPU:Dimension e153 321791183862:=by
  exact AZ e153 321791183862 431647854152694 1645378353
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e153 FWQ rank_e153 (by decide)

def e154:Parameters:=⟨84,2285,34,15,115,3,4⟩
theorem shape_e154:Shape e154:=by constructor<;>decide+kernel
theorem middle_e154 (h:ℕ) (hh:h≤15):115≤(e154.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e154,Parameters.cutoff,AQ.reserve]
theorem FPH:AM.AW e154.cutoff 131071 2285 34 15 115=460022506701678:=by decide+kernel
theorem rank_e154:AR.rankBound 84 2285 34 15 115=1753117161:=by decide+kernel
theorem GMZ:Dimension e154 453361648494:=by
  exact AZ e154 453361648494 460022506701678 1753117161
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e154 FPH rank_e154 (by decide)

def e155:Parameters:=⟨86,1957,36,17,117,3,4⟩
theorem shape_e155:Shape e155:=by constructor<;>decide+kernel
theorem middle_e155 (h:ℕ) (hh:h≤17):117≤(e155.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e155,Parameters.cutoff,AQ.reserve]
theorem FRZ:AM.AW e155.cutoff 131071 1957 36 17 117=457254957221901:=by decide+kernel
theorem rank_e155:AR.rankBound 86 1957 36 17 117=1742352093:=by decide+kernel
theorem GOS:Dimension e155 507810154509:=by
  exact AZ e155 507810154509 457254957221901 1742352093
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e155 FRZ rank_e155 (by decide)

def e156:Parameters:=⟨84,2348,36,17,115,3,4⟩
theorem shape_e156:Shape e156:=by constructor<;>decide+kernel
theorem middle_e156 (h:ℕ) (hh:h≤17):115≤(e156.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e156,Parameters.cutoff,AQ.reserve]
theorem FVO:AM.AW e156.cutoff 131071 2348 36 17 115=521461528842216:=by decide+kernel
theorem rank_e156:AR.rankBound 84 2348 36 17 115=1986322857:=by decide+kernel
theorem GNZ:Dimension e156 758909816808:=by
  exact AZ e156 758909816808 521461528842216 1986322857
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e156 FVO rank_e156 (by decide)

def e157:Parameters:=⟨86,1950,36,17,117,3,4⟩
theorem shape_e157:Shape e157:=by constructor<;>decide+kernel
theorem middle_e157 (h:ℕ) (hh:h≤17):117≤(e157.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e157,Parameters.cutoff,AQ.reserve]
theorem FQH:AM.AW e157.cutoff 131071 1950 36 17 117=455577218300511:=by decide+kernel
theorem rank_e157:AR.rankBound 86 1950 36 17 117=1735986657:=by decide+kernel
theorem GSE:Dimension e157 498732087903:=by
  exact AZ e157 498732087903 455577218300511 1735986657
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e157 FQH rank_e157 (by decide)

def e158:Parameters:=⟨84,2337,36,17,115,3,4⟩
theorem shape_e158:Shape e158:=by constructor<;>decide+kernel
theorem middle_e158 (h:ℕ) (hh:h≤17):115≤(e158.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e158,Parameters.cutoff,AQ.reserve]
theorem FUN:AM.AW e158.cutoff 131071 2337 36 17 115=518967299942196:=by decide+kernel
theorem rank_e158:AR.rankBound 84 2337 36 17 115=1976854629:=by decide+kernel
theorem GSL:Dimension e158 746720077620:=by
  exact AZ e158 746720077620 518967299942196 1976854629
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e158 FUN rank_e158 (by decide)

def e159:Parameters:=⟨86,1944,36,17,117,3,4⟩
theorem shape_e159:Shape e159:=by constructor<;>decide+kernel
theorem middle_e159 (h:ℕ) (hh:h≤17):117≤(e159.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e159,Parameters.cutoff,AQ.reserve]
theorem FVY:AM.AW e159.cutoff 131071 1944 36 17 117=454139156367891:=by decide+kernel
theorem rank_e159:AR.rankBound 86 1944 36 17 117=1730530569:=by decide+kernel
theorem GON:Dimension e159 490950887955:=by
  exact AZ e159 490950887955 454139156367891 1730530569
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e159 FVY rank_e159 (by decide)

def e160:Parameters:=⟨84,2327,36,17,115,3,4⟩
theorem shape_e160:Shape e160:=by constructor<;>decide+kernel
theorem middle_e160 (h:ℕ) (hh:h≤17):115≤(e160.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e160,Parameters.cutoff,AQ.reserve]
theorem FQV:AM.AW e160.cutoff 131071 2327 36 17 115=516699819123996:=by decide+kernel
theorem rank_e160:AR.rankBound 84 2327 36 17 115=1968247149:=by decide+kernel
theorem GRO:Dimension e160 735638496540:=by
  exact AZ e160 735638496540 516699819123996 1968247149
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e160 FQV rank_e160 (by decide)

def e161:Parameters:=⟨86,1937,36,17,117,3,4⟩
theorem shape_e161:Shape e161:=by constructor<;>decide+kernel
theorem middle_e161 (h:ℕ) (hh:h≤17):117≤(e161.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e161,Parameters.cutoff,AQ.reserve]
theorem FYA:AM.AW e161.cutoff 131071 1937 36 17 117=452461417446501:=by decide+kernel
theorem rank_e161:AR.rankBound 86 1937 36 17 117=1724165133:=by decide+kernel
theorem GQE:Dimension e161 481872821349:=by
  exact AZ e161 481872821349 452461417446501 1724165133
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e161 FYA rank_e161 (by decide)

def e162:Parameters:=⟨68,1549,28,12,93,2,3⟩
theorem shape_e162:Shape e162:=by constructor<;>decide+kernel
theorem middle_e162 (h:ℕ) (hh:h≤12):93≤(e162.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e162,Parameters.cutoff,AQ.reserve]
theorem FTR:AM.AW e162.cutoff 131071 1549 28 12 93=140518880628675:=by decide+kernel
theorem rank_e162:AR.rankBound 68 1549 28 12 93=535524887:=by decide+kernel
theorem GLQ:Dimension e162 134244650947:=by
  exact AZ e162 134244650947 140518880628675 535524887
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e162 FTR rank_e162 (by decide)

def e163:Parameters:=⟨86,1931,36,17,117,3,4⟩
theorem shape_e163:Shape e163:=by constructor<;>decide+kernel
theorem middle_e163 (h:ℕ) (hh:h≤17):117≤(e163.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e163,Parameters.cutoff,AQ.reserve]
theorem FSC:AM.AW e163.cutoff 131071 1931 36 17 117=451023355513881:=by decide+kernel
theorem rank_e163:AR.rankBound 86 1931 36 17 117=1718709045:=by decide+kernel
theorem GLP:Dimension e163 474091621401:=by
  exact AZ e163 474091621401 451023355513881 1718709045
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e163 FSC rank_e163 (by decide)

def e164:Parameters:=⟨84,2306,36,17,115,3,4⟩
theorem shape_e164:Shape e164:=by constructor<;>decide+kernel
theorem middle_e164 (h:ℕ) (hh:h≤17):115≤(e164.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e164,Parameters.cutoff,AQ.reserve]
theorem FXV:AM.AW e164.cutoff 131071 2306 36 17 115=511938109405776:=by decide+kernel
theorem rank_e164:AR.rankBound 84 2306 36 17 115=1950171441:=by decide+kernel
theorem GLX:Dimension e164 712367176272:=by
  exact AZ e164 712367176272 511938109405776 1950171441
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e164 FXV rank_e164 (by decide)

def e165:Parameters:=⟨86,1924,36,17,117,3,4⟩
theorem shape_e165:Shape e165:=by constructor<;>decide+kernel
theorem middle_e165 (h:ℕ) (hh:h≤17):117≤(e165.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e165,Parameters.cutoff,AQ.reserve]
theorem FOU:AM.AW e165.cutoff 131071 1924 36 17 117=449345616592491:=by decide+kernel
theorem rank_e165:AR.rankBound 86 1924 36 17 117=1712343609:=by decide+kernel
theorem GOZ:Dimension e165 465013554795:=by
  exact AZ e165 465013554795 449345616592491 1712343609
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e165 FOU rank_e165 (by decide)

def e166:Parameters:=⟨84,2296,36,17,115,3,4⟩
theorem shape_e166:Shape e166:=by constructor<;>decide+kernel
theorem middle_e166 (h:ℕ) (hh:h≤17):115≤(e166.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e166,Parameters.cutoff,AQ.reserve]
theorem FWF:AM.AW e166.cutoff 131071 2296 36 17 115=509670628587576:=by decide+kernel
theorem rank_e166:AR.rankBound 84 2296 36 17 115=1941563961:=by decide+kernel
theorem GKR:Dimension e166 701285595192:=by
  exact AZ e166 701285595192 509670628587576 1941563961
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e166 FWF rank_e166 (by decide)

def e167:Parameters:=⟨68,1533,28,12,93,2,3⟩
theorem shape_e167:Shape e167:=by constructor<;>decide+kernel
theorem middle_e167 (h:ℕ) (hh:h≤12):93≤(e167.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e167,Parameters.cutoff,AQ.reserve]
theorem FPK:AM.AW e167.cutoff 131071 1533 28 12 93=139030425089939:=by decide+kernel
theorem rank_e167:AR.rankBound 68 1533 28 12 93=529876919:=by decide+kernel
theorem GMR:Dimension e167 126370035603:=by
  exact AZ e167 126370035603 139030425089939 529876919
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e167 FPK rank_e167 (by decide)

def e168:Parameters:=⟨68,1518,28,12,93,2,3⟩
theorem shape_e168:Shape e168:=by constructor<;>decide+kernel
theorem middle_e168 (h:ℕ) (hh:h≤12):93≤(e168.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e168,Parameters.cutoff,AQ.reserve]
theorem FXG:AM.AW e168.cutoff 131071 1518 28 12 93=137634998022374:=by decide+kernel
theorem rank_e168:AR.rankBound 68 1518 28 12 93=524581949:=by decide+kernel
theorem GLR:Dimension e168 118987583718:=by
  exact AZ e168 118987583718 137634998022374 524581949
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e168 FXG rank_e168 (by decide)

def e169:Parameters:=⟨84,2182,34,15,115,3,4⟩
theorem shape_e169:Shape e169:=by constructor<;>decide+kernel
theorem middle_e169 (h:ℕ) (hh:h≤15):115≤(e169.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e169,Parameters.cutoff,AQ.reserve]
theorem FRM:AM.AW e169.cutoff 131071 2182 34 15 115=438844324002074:=by decide+kernel
theorem rank_e169:AR.rankBound 84 2182 34 15 115=1672703413:=by decide+kernel
theorem GLJ:Dimension e169 355160504602:=by
  exact AZ e169 355160504602 438844324002074 1672703413
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e169 FRM rank_e169 (by decide)

def e170:Parameters:=⟨88,1826,36,17,120,3,4⟩
theorem shape_e170:Shape e170:=by constructor<;>decide+kernel
theorem middle_e170 (h:ℕ) (hh:h≤17):120≤(e170.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e170,Parameters.cutoff,AQ.reserve]
theorem FTZ:AM.AW e170.cutoff 131071 1826 36 17 120=449246199218151:=by decide+kernel
theorem rank_e170:AR.rankBound 88 1826 36 17 120=1711968426:=by decide+kernel
theorem GSR:Dimension e170 463948152807:=by
  exact AZ e170 463948152807 449246199218151 1711968426
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e170 FTZ rank_e170 (by decide)

def e171:Parameters:=⟨88,1812,36,17,120,3,4⟩
theorem shape_e171:Shape e171:=by constructor<;>decide+kernel
theorem middle_e171 (h:ℕ) (hh:h≤17):120≤(e171.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e171,Parameters.cutoff,AQ.reserve]
theorem FXY:AM.AW e171.cutoff 131071 1812 36 17 120=445704550160421:=by decide+kernel
theorem rank_e171:AR.rankBound 88 1812 36 17 120=1698536840:=by decide+kernel
theorem GPV:Dimension e171 443308775461:=by
  exact AZ e171 443308775461 445704550160421 1698536840
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e171 FXY rank_e171 (by decide)

def e172:Parameters:=⟨84,2158,34,15,115,3,4⟩
theorem shape_e172:Shape e172:=by constructor<;>decide+kernel
theorem middle_e172 (h:ℕ) (hh:h≤15):115≤(e172.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e172,Parameters.cutoff,AQ.reserve]
theorem FVA:AM.AW e172.cutoff 131071 2158 34 15 115=433909601819642:=by decide+kernel
theorem rank_e172:AR.rankBound 84 2158 34 15 115=1653966229:=by decide+kernel
theorem GMB:Dimension e172 332278684666:=by
  exact AZ e172 332278684666 433909601819642 1653966229
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e172 FVA rank_e172 (by decide)

def e173:Parameters:=⟨88,1797,36,17,120,3,4⟩
theorem shape_e173:Shape e173:=by constructor<;>decide+kernel
theorem middle_e173 (h:ℕ) (hh:h≤17):120≤(e173.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e173,Parameters.cutoff,AQ.reserve]
theorem FPD:AM.AW e173.cutoff 131071 1797 36 17 120=441909926169996:=by decide+kernel
theorem rank_e173:AR.rankBound 88 1797 36 17 120=1684145855:=by decide+kernel
theorem GOV:Dimension e173 421195156876:=by
  exact AZ e173 421195156876 441909926169996 1684145855
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e173 FPD rank_e173 (by decide)

def e174:Parameters:=⟨86,2143,36,17,117,3,4⟩
theorem shape_e174:Shape e174:=by constructor<;>decide+kernel
theorem middle_e174 (h:ℕ) (hh:h≤17):117≤(e174.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e174,Parameters.cutoff,AQ.reserve]
theorem FSE:AM.AW e174.cutoff 131071 2143 36 17 117=501834877133121:=by decide+kernel
theorem rank_e174:AR.rankBound 86 2143 36 17 117=1911490821:=by decide+kernel
theorem GMD:Dimension e174 749027352897:=by
  exact AZ e174 749027352897 501834877133121 1911490821
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e174 FSE rank_e174 (by decide)

def e175:Parameters:=⟨68,1486,28,12,93,2,3⟩
theorem shape_e175:Shape e175:=by constructor<;>decide+kernel
theorem middle_e175 (h:ℕ) (hh:h≤12):93≤(e175.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e175,Parameters.cutoff,AQ.reserve]
theorem FQJ:AM.AW e175.cutoff 131071 1486 28 12 93=134658086944902:=by decide+kernel
theorem rank_e175:AR.rankBound 68 1486 28 12 93=513286013:=by decide+kernel
theorem GLD:Dimension e175 103238353030:=by
  exact AZ e175 103238353030 134658086944902 513286013
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e175 FQJ rank_e175 (by decide)

def e176:Parameters:=⟨66,1843,28,12,90,2,3⟩
theorem shape_e176:Shape e176:=by constructor<;>decide+kernel
theorem middle_e176 (h:ℕ) (hh:h≤12):90≤(e176.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e176,Parameters.cutoff,AQ.reserve]
theorem FWP:AM.AW e176.cutoff 131071 1843 28 12 90=156600114578645:=by decide+kernel
theorem rank_e176:AR.rankBound 66 1843 28 12 90=596675390:=by decide+kernel
theorem GJD:Dimension e176 185241142485:=by
  exact AZ e176 185241142485 156600114578645 596675390
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e176 FWP rank_e176 (by decide)

def e177:Parameters:=⟨88,1782,36,17,120,3,4⟩
theorem shape_e177:Shape e177:=by constructor<;>decide+kernel
theorem middle_e177 (h:ℕ) (hh:h≤17):120≤(e177.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e177,Parameters.cutoff,AQ.reserve]
theorem FXC:AM.AW e177.cutoff 131071 1782 36 17 120=438115302179571:=by decide+kernel
theorem rank_e177:AR.rankBound 88 1782 36 17 120=1669754870:=by decide+kernel
theorem GNU:Dimension e177 399081538291:=by
  exact AZ e177 399081538291 438115302179571 1669754870
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e177 FXC rank_e177 (by decide)

def e178:Parameters:=⟨68,1455,28,12,93,2,3⟩
theorem shape_e178:Shape e178:=by constructor<;>decide+kernel
theorem middle_e178 (h:ℕ) (hh:h≤12):93≤(e178.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e178,Parameters.cutoff,AQ.reserve]
theorem FYG:AM.AW e178.cutoff 131071 1455 28 12 93=131774204338601:=by decide+kernel
theorem rank_e178:AR.rankBound 68 1455 28 12 93=502343075:=by decide+kernel
theorem _Q26:Dimension e178 87981285801:=by
  exact AZ e178 87981285801 131774204338601 502343075
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e178 FYG rank_e178 (by decide)

def e179:Parameters:=⟨68,1497,27,13,93,2,3⟩
theorem shape_e179:Shape e179:=by constructor<;>decide+kernel
theorem middle_e179 (h:ℕ) (hh:h≤13):93≤(e179.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e179,Parameters.cutoff,AQ.reserve]
theorem FPE:AM.AW e179.cutoff 131071 1497 27 13 93=130507204794399:=by decide+kernel
theorem rank_e179:AR.rankBound 68 1497 27 13 93=497632271:=by decide+kernel
theorem GRX:Dimension e179 55890745375:=by
  exact AZ e179 55890745375 130507204794399 497632271
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e179 FPE rank_e179 (by decide)

def e180:Parameters:=⟨68,1371,28,12,93,2,3⟩
theorem shape_e180:Shape e180:=by constructor<;>decide+kernel
theorem middle_e180 (h:ℕ) (hh:h≤12):93≤(e180.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e180,Parameters.cutoff,AQ.reserve]
theorem FUQ:AM.AW e180.cutoff 131071 1371 28 12 93=123959812760237:=by decide+kernel
theorem rank_e180:AR.rankBound 68 1371 28 12 93=472691243:=by decide+kernel
theorem GQR:Dimension e180 46639555245:=by
  exact AZ e180 46639555245 123959812760237 472691243
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e180 FUQ rank_e180 (by decide)

def e181:Parameters:=⟨76,1139,32,15,104,2,3⟩
theorem shape_e181:Shape e181:=by constructor<;>decide+kernel
theorem middle_e181 (h:ℕ) (hh:h≤15):104≤(e181.cutoff h+32-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e181,Parameters.cutoff,AQ.reserve]
theorem FYQ:AM.AW e181.cutoff 131071 1139 32 15 104=164604306406932:=by decide+kernel
theorem rank_e181:AR.rankBound 76 1139 32 15 104=626991471:=by decide+kernel
theorem GNQ:Dimension e181 242254233108:=by
  exact AZ e181 242254233108 164604306406932 626991471
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e181 FYQ rank_e181 (by decide)

def e182:Parameters:=⟨52,994,22,10,71,1,2⟩
theorem shape_e182:Shape e182:=by constructor<;>decide+kernel
theorem middle_e182 (h:ℕ) (hh:h≤10):71≤(e182.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e182,Parameters.cutoff,AQ.reserve]
theorem FSS:AM.AW e182.cutoff 131071 994 22 10 71=33945034538505:=by decide+kernel
theorem rank_e182:AR.rankBound 52 994 22 10 71=129297019:=by decide+kernel
theorem GQT:Dimension e182 50596789769:=by
  exact AZ e182 50596789769 33945034538505 129297019
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e182 FSS rank_e182 (by decide)

def e183:Parameters:=⟨50,1177,20,9,68,1,2⟩
theorem shape_e183:Shape e183:=by constructor<;>decide+kernel
theorem middle_e183 (h:ℕ) (hh:h≤9):68≤(e183.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e183,Parameters.cutoff,AQ.reserve]
theorem FXA:AM.AW e183.cutoff 131071 1177 20 9 68=31983325445910:=by decide+kernel
theorem rank_e183:AR.rankBound 50 1177 20 9 68=121876141:=by decide+kernel
theorem GOW:Dimension e183 34226339606:=by
  exact AZ e183 34226339606 31983325445910 121876141
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e183 FXA rank_e183 (by decide)

def e184:Parameters:=⟨50,1065,20,9,68,1,2⟩
theorem shape_e184:Shape e184:=by constructor<;>decide+kernel
theorem middle_e184 (h:ℕ) (hh:h≤9):68≤(e184.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e184,Parameters.cutoff,AQ.reserve]
theorem FSJ:AM.AW e184.cutoff 131071 1065 20 9 68=28866193829542:=by decide+kernel
theorem rank_e184:AR.rankBound 50 1065 20 9 68=110048493:=by decide+kernel
theorem GSC:Dimension e184 17641680550:=by
  exact AZ e184 17641680550 28866193829542 110048493
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e184 FSJ rank_e184 (by decide)

def e185:Parameters:=⟨50,1024,20,9,68,1,2⟩
theorem shape_e185:Shape e185:=by constructor<;>decide+kernel
theorem middle_e185 (h:ℕ) (hh:h≤9):68≤(e185.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e185,Parameters.cutoff,AQ.reserve]
theorem FRU:AM.AW e185.cutoff 131071 1024 20 9 68=27725101005693:=by decide+kernel
theorem rank_e185:AR.rankBound 50 1024 20 9 68=105718729:=by decide+kernel
theorem GLC:Dimension e185 11570510717:=by
  exact AZ e185 11570510717 27725101005693 105718729
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e185 FRU rank_e185 (by decide)

def e186:Parameters:=⟨52,856,22,10,71,1,2⟩
theorem shape_e186:Shape e186:=by constructor<;>decide+kernel
theorem middle_e186 (h:ℕ) (hh:h≤10):71≤(e186.cutoff h+22-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e186,Parameters.cutoff,AQ.reserve]
theorem FUY:AM.AW e186.cutoff 131071 856 22 10 71=29088997962723:=by decide+kernel
theorem rank_e186:AR.rankBound 52 856 22 10 71=110894857:=by decide+kernel
theorem GJY:Dimension e186 18576569315:=by
  exact AZ e186 18576569315 29088997962723 110894857
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e186 FUY rank_e186 (by decide)

def e187:Parameters:=⟨78,926,34,15,107,2,3⟩
theorem shape_e187:Shape e187:=by constructor<;>decide+kernel
theorem middle_e187 (h:ℕ) (hh:h≤15):107≤(e187.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e187,Parameters.cutoff,AQ.reserve]
theorem FXL:AM.AW e187.cutoff 131071 926 34 15 107=153040926745102:=by decide+kernel
theorem rank_e187:AR.rankBound 78 926 34 15 107=583556416:=by decide+kernel
theorem GRG:Dimension e187 65113629198:=by
  exact AZ e187 65113629198 153040926745102 583556416
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e187 FXL rank_e187 (by decide)

def e188:Parameters:=⟨82,826,36,16,112,2,3⟩
theorem shape_e188:Shape e188:=by constructor<;>decide+kernel
theorem middle_e188 (h:ℕ) (hh:h≤16):112≤(e188.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e188,Parameters.cutoff,AQ.reserve]
theorem FXB:AM.AW e188.cutoff 131071 826 36 16 112=166319508628405:=by decide+kernel
theorem rank_e188:AR.rankBound 82 826 36 16 112=634443436:=by decide+kernel
theorem GPZ:Dimension e188 3968541621:=by
  exact AZ e188 3968541621 166319508628405 634443436
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e188 FXB rank_e188 (by decide)

def e189:Parameters:=⟨60,599,26,12,82,1,2⟩
theorem shape_e189:Shape e189:=by constructor<;>decide+kernel
theorem middle_e189 (h:ℕ) (hh:h≤12):82≤(e189.cutoff h+26-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e189,Parameters.cutoff,AQ.reserve]
theorem FSD:AM.AW e189.cutoff 131071 599 26 12 82=35734329032220:=by decide+kernel
theorem rank_e189:AR.rankBound 60 599 26 12 82=136311470:=by decide+kernel
theorem GME:Dimension e189 1095040540:=by
  exact AZ e189 1095040540 35734329032220 136311470
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e189 FSD rank_e189 (by decide)

def e190:Parameters:=⟨78,925,34,15,107,2,3⟩
theorem shape_e190:Shape e190:=by constructor<;>decide+kernel
theorem middle_e190 (h:ℕ) (hh:h≤15):107≤(e190.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e190,Parameters.cutoff,AQ.reserve]
theorem FVN:AM.AW e190.cutoff 131071 925 34 15 107=152867225530424:=by decide+kernel
theorem rank_e190:AR.rankBound 78 925 34 15 107=582899557:=by decide+kernel
theorem GPT:Dimension e190 63604060216:=by
  exact AZ e190 63604060216 152867225530424 582899557
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e190 FVN rank_e190 (by decide)

def e191:Parameters:=⟨82,836,36,16,112,2,3⟩
theorem shape_e191:Shape e191:=by constructor<;>decide+kernel
theorem middle_e191 (h:ℕ) (hh:h≤16):112≤(e191.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e191,Parameters.cutoff,AQ.reserve]
theorem FWL:AM.AW e191.cutoff 131071 836 36 16 112=168455649517865:=by decide+kernel
theorem rank_e191:AR.rankBound 82 836 36 16 112=642512096:=by decide+kernel
theorem GSJ:Dimension e191 24958624041:=by
  exact AZ e191 24958624041 168455649517865 642512096
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e191 FWL rank_e191 (by decide)

def e192:Parameters:=⟨85,801,37,17,116,2,3⟩
theorem shape_e192:Shape e192:=by constructor<;>decide+kernel
theorem middle_e192 (h:ℕ) (hh:h≤17):116≤(e192.cutoff h+37-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e192,Parameters.cutoff,AQ.reserve]
theorem FYP:AM.AW e192.cutoff 131071 801 37 17 116=183293195531790:=by decide+kernel
theorem rank_e192:AR.rankBound 85 801 37 17 116=699180756:=by decide+kernel
theorem GQY:Dimension e192 7155430926:=by
  exact AZ e192 7155430926 183293195531790 699180756
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e192 FYP rank_e192 (by decide)

def e193:Parameters:=⟨84,2457,34,15,115,3,4⟩
theorem shape_e193:Shape e193:=by constructor<;>decide+kernel
theorem middle_e193 (h:ℕ) (hh:h≤15):115≤(e193.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e193,Parameters.cutoff,AQ.reserve]
theorem FQP:AM.AW e193.cutoff 131071 2457 34 15 115=495388015675774:=by decide+kernel
theorem rank_e193:AR.rankBound 84 2457 34 15 115=1887400313:=by decide+kernel
theorem GNM:Dimension e193 617348024702:=by
  exact AZ e193 617348024702 495388015675774 1887400313
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e193 FQP rank_e193 (by decide)

def e194:Parameters:=⟨84,2118,34,15,115,3,4⟩
theorem shape_e194:Shape e194:=by constructor<;>decide+kernel
theorem middle_e194 (h:ℕ) (hh:h≤15):115≤(e194.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e194,Parameters.cutoff,AQ.reserve]
theorem FPU:AM.AW e194.cutoff 131071 2118 34 15 115=425685064848922:=by decide+kernel
theorem rank_e194:AR.rankBound 84 2118 34 15 115=1622737589:=by decide+kernel
theorem GPP:Dimension e194 294142318106:=by
  exact AZ e194 294142318106 425685064848922 1622737589
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e194 FPU rank_e194 (by decide)

def e195:Parameters:=⟨84,2446,34,15,115,3,4⟩
theorem shape_e195:Shape e195:=by constructor<;>decide+kernel
theorem middle_e195 (h:ℕ) (hh:h≤15):115≤(e195.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e195,Parameters.cutoff,AQ.reserve]
theorem FTV:AM.AW e195.cutoff 131071 2446 34 15 115=493126268008826:=by decide+kernel
theorem rank_e195:AR.rankBound 84 2446 34 15 115=1878812437:=by decide+kernel
theorem GOQ:Dimension e195 606860523898:=by
  exact AZ e195 606860523898 493126268008826 1878812437
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e195 FTV rank_e195 (by decide)

def e196:Parameters:=⟨84,2114,34,15,115,3,4⟩
theorem shape_e196:Shape e196:=by constructor<;>decide+kernel
theorem middle_e196 (h:ℕ) (hh:h≤15):115≤(e196.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e196,Parameters.cutoff,AQ.reserve]
theorem FYJ:AM.AW e196.cutoff 131071 2114 34 15 115=424862611151850:=by decide+kernel
theorem rank_e196:AR.rankBound 84 2114 34 15 115=1619614725:=by decide+kernel
theorem GRK:Dimension e196 290328681450:=by
  exact AZ e196 290328681450 424862611151850 1619614725
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e196 FYJ rank_e196 (by decide)

def e197:Parameters:=⟨84,2190,34,15,115,3,4⟩
theorem shape_e197:Shape e197:=by constructor<;>decide+kernel
theorem middle_e197 (h:ℕ) (hh:h≤15):115≤(e197.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e197,Parameters.cutoff,AQ.reserve]
theorem FUX:AM.AW e197.cutoff 131071 2190 34 15 115=440489231396218:=by decide+kernel
theorem rank_e197:AR.rankBound 84 2190 34 15 115=1678949141:=by decide+kernel
theorem GNG:Dimension e197 362787777914:=by
  exact AZ e197 362787777914 440489231396218 1678949141
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e197 FUX rank_e197 (by decide)

def e198:Parameters:=⟨84,2347,34,15,115,3,4⟩
theorem shape_e198:Shape e198:=by constructor<;>decide+kernel
theorem middle_e198 (h:ℕ) (hh:h≤15):115≤(e198.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e198,Parameters.cutoff,AQ.reserve]
theorem FQK:AM.AW e198.cutoff 131071 2347 34 15 115=472770539006294:=by decide+kernel
theorem rank_e198:AR.rankBound 84 2347 34 15 115=1801521553:=by decide+kernel
theorem GQU:Dimension e198 512473016662:=by
  exact AZ e198 512473016662 472770539006294 1801521553
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e198 FQK rank_e198 (by decide)

def e199:Parameters:=⟨84,2186,34,15,115,3,4⟩
theorem shape_e199:Shape e199:=by constructor<;>decide+kernel
theorem middle_e199 (h:ℕ) (hh:h≤15):115≤(e199.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e199,Parameters.cutoff,AQ.reserve]
theorem FQU:AM.AW e199.cutoff 131071 2186 34 15 115=439666777699146:=by decide+kernel
theorem rank_e199:AR.rankBound 84 2186 34 15 115=1675826277:=by decide+kernel
theorem GKH:Dimension e199 358974141258:=by
  exact AZ e199 358974141258 439666777699146 1675826277
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e199 FQU rank_e199 (by decide)

def e200:Parameters:=⟨84,2183,34,15,115,3,4⟩
theorem shape_e200:Shape e200:=by constructor<;>decide+kernel
theorem middle_e200 (h:ℕ) (hh:h≤15):115≤(e200.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e200,Parameters.cutoff,AQ.reserve]
theorem FRO:AM.AW e200.cutoff 131071 2183 34 15 115=439049937426342:=by decide+kernel
theorem rank_e200:AR.rankBound 84 2183 34 15 115=1673484129:=by decide+kernel
theorem GJO:Dimension e200 356113913766:=by
  exact AZ e200 356113913766 439049937426342 1673484129
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e200 FRO rank_e200 (by decide)

def e201:Parameters:=⟨84,2336,34,15,115,3,4⟩
theorem shape_e201:Shape e201:=by constructor<;>decide+kernel
theorem middle_e201 (h:ℕ) (hh:h≤15):115≤(e201.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e201,Parameters.cutoff,AQ.reserve]
theorem FRT:AM.AW e201.cutoff 131071 2336 34 15 115=470508791339346:=by decide+kernel
theorem rank_e201:AR.rankBound 84 2336 34 15 115=1792933677:=by decide+kernel
theorem GQF:Dimension e201 501985515858:=by
  exact AZ e201 501985515858 470508791339346 1792933677
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e201 FRT rank_e201 (by decide)

def e202:Parameters:=⟨84,2179,34,15,115,3,4⟩
theorem shape_e202:Shape e202:=by constructor<;>decide+kernel
theorem middle_e202 (h:ℕ) (hh:h≤15):115≤(e202.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e202,Parameters.cutoff,AQ.reserve]
theorem FWT:AM.AW e202.cutoff 131071 2179 34 15 115=438227483729270:=by decide+kernel
theorem rank_e202:AR.rankBound 84 2179 34 15 115=1670361265:=by decide+kernel
theorem GJM:Dimension e202 352300277110:=by
  exact AZ e202 352300277110 438227483729270 1670361265
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e202 FWT rank_e202 (by decide)

def e203:Parameters:=⟨87,1742,38,17,119,3,4⟩
theorem shape_e203:Shape e203:=by constructor<;>decide+kernel
theorem middle_e203 (h:ℕ) (hh:h≤17):119≤(e203.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e203,Parameters.cutoff,AQ.reserve]
theorem FRJ:AM.AW e203.cutoff 131071 1742 38 17 119=449643874127010:=by decide+kernel
theorem rank_e203:AR.rankBound 87 1742 38 17 119=1713610614:=by decide+kernel
theorem GRY:Dimension e203 431133330594:=by
  exact AZ e203 431133330594 449643874127010 1713610614
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e203 FRJ rank_e203 (by decide)

def e204:Parameters:=⟨68,1324,28,12,93,2,3⟩
theorem shape_e204:Shape e204:=by constructor<;>decide+kernel
theorem middle_e204 (h:ℕ) (hh:h≤12):93≤(e204.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e204,Parameters.cutoff,AQ.reserve]
theorem FSP:AM.AW e204.cutoff 131071 1324 28 12 93=119587474615200:=by decide+kernel
theorem rank_e204:AR.rankBound 68 1324 28 12 93=456100337:=by decide+kernel
theorem GKF:Dimension e204 23507872672:=by
  exact AZ e204 23507872672 119587474615200 456100337
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e204 FSP rank_e204 (by decide)

def e205:Parameters:=⟨84,2175,34,15,115,3,4⟩
theorem shape_e205:Shape e205:=by constructor<;>decide+kernel
theorem middle_e205 (h:ℕ) (hh:h≤15):115≤(e205.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e205,Parameters.cutoff,AQ.reserve]
theorem FPL:AM.AW e205.cutoff 131071 2175 34 15 115=437405030032198:=by decide+kernel
theorem rank_e205:AR.rankBound 84 2175 34 15 115=1667238401:=by decide+kernel
theorem GJP:Dimension e205 348486640454:=by
  exact AZ e205 348486640454 437405030032198 1667238401
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e205 FPL rank_e205 (by decide)

def e206:Parameters:=⟨84,2326,34,15,115,3,4⟩
theorem shape_e206:Shape e206:=by constructor<;>decide+kernel
theorem middle_e206 (h:ℕ) (hh:h≤15):115≤(e206.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e206,Parameters.cutoff,AQ.reserve]
theorem FON:AM.AW e206.cutoff 131071 2326 34 15 115=468452657096666:=by decide+kernel
theorem rank_e206:AR.rankBound 84 2326 34 15 115=1785126517:=by decide+kernel
theorem GOA:Dimension e206 492451424218:=by
  exact AZ e206 492451424218 468452657096666 1785126517
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e206 FON rank_e206 (by decide)

def e207:Parameters:=⟨84,2171,34,15,115,3,4⟩
theorem shape_e207:Shape e207:=by constructor<;>decide+kernel
theorem middle_e207 (h:ℕ) (hh:h≤15):115≤(e207.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e207,Parameters.cutoff,AQ.reserve]
theorem FTG:AM.AW e207.cutoff 131071 2171 34 15 115=436582576335126:=by decide+kernel
theorem rank_e207:AR.rankBound 84 2171 34 15 115=1664115537:=by decide+kernel
theorem GPS:Dimension e207 344673003798:=by
  exact AZ e207 344673003798 436582576335126 1664115537
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e207 FTG rank_e207 (by decide)

def e208:Parameters:=⟨68,1277,28,12,93,2,3⟩
theorem shape_e208:Shape e208:=by constructor<;>decide+kernel
theorem middle_e208 (h:ℕ) (hh:h≤12):93≤(e208.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e208,Parameters.cutoff,AQ.reserve]
theorem FVT:AM.AW e208.cutoff 131071 1277 28 12 93=115215136470163:=by decide+kernel
theorem rank_e208:AR.rankBound 68 1277 28 12 93=439509431:=by decide+kernel
theorem GRT:Dimension e208 376190099:=by
  exact AZ e208 376190099 115215136470163 439509431
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e208 FVT rank_e208 (by decide)

def e209:Parameters:=⟨86,1982,36,17,117,3,4⟩
theorem shape_e209:Shape e209:=by constructor<;>decide+kernel
theorem middle_e209 (h:ℕ) (hh:h≤17):117≤(e209.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e209,Parameters.cutoff,AQ.reserve]
theorem FVE:AM.AW e209.cutoff 131071 1982 36 17 117=463246881941151:=by decide+kernel
theorem rank_e209:AR.rankBound 86 1982 36 17 117=1765085793:=by decide+kernel
theorem GSK:Dimension e209 540231820959:=by
  exact AZ e209 540231820959 463246881941151 1765085793
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e209 FVE rank_e209 (by decide)

def e210:Parameters:=⟨84,2389,36,17,115,3,4⟩
theorem shape_e210:Shape e210:=by constructor<;>decide+kernel
theorem middle_e210 (h:ℕ) (hh:h≤17):115≤(e210.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e210,Parameters.cutoff,AQ.reserve]
theorem FVQ:AM.AW e210.cutoff 131071 2389 36 17 115=530758200196836:=by decide+kernel
theorem rank_e210:AR.rankBound 84 2389 36 17 115=2021613525:=by decide+kernel
theorem GOL:Dimension e210 804344299236:=by
  exact AZ e210 804344299236 530758200196836 2021613525
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e210 FVQ rank_e210 (by decide)

def e211:Parameters:=⟨86,1976,36,17,117,3,4⟩
theorem shape_e211:Shape e211:=by constructor<;>decide+kernel
theorem middle_e211 (h:ℕ) (hh:h≤17):117≤(e211.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e211,Parameters.cutoff,AQ.reserve]
theorem FUB:AM.AW e211.cutoff 131071 1976 36 17 117=461808820008531:=by decide+kernel
theorem rank_e211:AR.rankBound 86 1976 36 17 117=1759629705:=by decide+kernel
theorem GKD:Dimension e211 532450621011:=by
  exact AZ e211 532450621011 461808820008531 1759629705
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e211 FUB rank_e211 (by decide)

def e212:Parameters:=⟨84,2379,36,17,115,3,4⟩
theorem shape_e212:Shape e212:=by constructor<;>decide+kernel
theorem middle_e212 (h:ℕ) (hh:h≤17):115≤(e212.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e212,Parameters.cutoff,AQ.reserve]
theorem FUP:AM.AW e212.cutoff 131071 2379 36 17 115=528490719378636:=by decide+kernel
theorem rank_e212:AR.rankBound 84 2379 36 17 115=2013006045:=by decide+kernel
theorem GMK:Dimension e212 793262718156:=by
  exact AZ e212 793262718156 528490719378636 2013006045
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e212 FUP rank_e212 (by decide)

def e213:Parameters:=⟨86,1969,36,17,117,3,4⟩
theorem shape_e213:Shape e213:=by constructor<;>decide+kernel
theorem middle_e213 (h:ℕ) (hh:h≤17):117≤(e213.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e213,Parameters.cutoff,AQ.reserve]
theorem FWS:AM.AW e213.cutoff 131071 1969 36 17 117=460131081087141:=by decide+kernel
theorem rank_e213:AR.rankBound 86 1969 36 17 117=1753264269:=by decide+kernel
theorem GLY:Dimension e213 523372554405:=by
  exact AZ e213 523372554405 460131081087141 1753264269
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e213 FWS rank_e213 (by decide)

def e214:Parameters:=⟨84,2368,36,17,115,3,4⟩
theorem shape_e214:Shape e214:=by constructor<;>decide+kernel
theorem middle_e214 (h:ℕ) (hh:h≤17):115≤(e214.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e214,Parameters.cutoff,AQ.reserve]
theorem FUL:AM.AW e214.cutoff 131071 2368 36 17 115=525996490478616:=by decide+kernel
theorem rank_e214:AR.rankBound 84 2368 36 17 115=2003537817:=by decide+kernel
theorem GRV:Dimension e214 781072978968:=by
  exact AZ e214 781072978968 525996490478616 2003537817
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e214 FUL rank_e214 (by decide)

def e215:Parameters:=⟨86,1963,36,17,117,3,4⟩
theorem shape_e215:Shape e215:=by constructor<;>decide+kernel
theorem middle_e215 (h:ℕ) (hh:h≤17):117≤(e215.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e215,Parameters.cutoff,AQ.reserve]
theorem FQG:AM.AW e215.cutoff 131071 1963 36 17 117=458693019154521:=by decide+kernel
theorem rank_e215:AR.rankBound 86 1963 36 17 117=1747808181:=by decide+kernel
theorem GQI:Dimension e215 515591354457:=by
  exact AZ e215 515591354457 458693019154521 1747808181
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e215 FQG rank_e215 (by decide)

def e216:Parameters:=⟨68,1565,28,12,93,2,3⟩
theorem shape_e216:Shape e216:=by constructor<;>decide+kernel
theorem middle_e216 (h:ℕ) (hh:h≤12):93≤(e216.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e216,Parameters.cutoff,AQ.reserve]
theorem FUK:AM.AW e216.cutoff 131071 1565 28 12 93=142007336167411:=by decide+kernel
theorem rank_e216:AR.rankBound 68 1565 28 12 93=541172855:=by decide+kernel
theorem GKB:Dimension e216 142119266291:=by
  exact AZ e216 142119266291 142007336167411 541172855
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e216 FUK rank_e216 (by decide)

def e217:Parameters:=⟨84,2206,34,15,115,3,4⟩
theorem shape_e217:Shape e217:=by constructor<;>decide+kernel
theorem middle_e217 (h:ℕ) (hh:h≤15):115≤(e217.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e217,Parameters.cutoff,AQ.reserve]
theorem FTN:AM.AW e217.cutoff 131071 2206 34 15 115=443779046184506:=by decide+kernel
theorem rank_e217:AR.rankBound 84 2206 34 15 115=1691440597:=by decide+kernel
theorem GPW:Dimension e217 378042324538:=by
  exact AZ e217 378042324538 443779046184506 1691440597
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e217 FTN rank_e217 (by decide)

def e218:Parameters:=⟨88,1855,36,17,120,3,4⟩
theorem shape_e218:Shape e218:=by constructor<;>decide+kernel
theorem middle_e218 (h:ℕ) (hh:h≤17):120≤(e218.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e218,Parameters.cutoff,AQ.reserve]
theorem FRF:AM.AW e218.cutoff 131071 1855 36 17 120=456582472266306:=by decide+kernel
theorem rank_e218:AR.rankBound 88 1855 36 17 120=1739790997:=by decide+kernel
theorem GOY:Dimension e218 506701148738:=by
  exact AZ e218 506701148738 456582472266306 1739790997
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e218 FRF rank_e218 (by decide)

def e219:Parameters:=⟨88,1841,36,17,120,3,4⟩
theorem shape_e219:Shape e219:=by constructor<;>decide+kernel
theorem middle_e219 (h:ℕ) (hh:h≤17):120≤(e219.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e219,Parameters.cutoff,AQ.reserve]
theorem FRC:AM.AW e219.cutoff 131071 1841 36 17 120=453040823208576:=by decide+kernel
theorem rank_e219:AR.rankBound 88 1841 36 17 120=1726359411:=by decide+kernel
theorem GNR:Dimension e219 486061771392:=by
  exact AZ e219 486061771392 453040823208576 1726359411
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e219 FRC rank_e219 (by decide)

def e220:Parameters:=⟨88,1955,36,17,120,3,4⟩
theorem shape_e220:Shape e220:=by constructor<;>decide+kernel
theorem middle_e220 (h:ℕ) (hh:h≤17):120≤(e220.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e220,Parameters.cutoff,AQ.reserve]
theorem FTW:AM.AW e220.cutoff 131071 1955 36 17 120=481879965535806:=by decide+kernel
theorem rank_e220:AR.rankBound 88 1955 36 17 120=1835730897:=by decide+kernel
theorem GRD:Dimension e220 654125272638:=by
  exact AZ e220 654125272638 481879965535806 1835730897
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e220 FTW rank_e220 (by decide)

def e221:Parameters:=⟨88,1944,36,17,120,3,4⟩
theorem shape_e221:Shape e221:=by constructor<;>decide+kernel
theorem middle_e221 (h:ℕ) (hh:h≤17):120≤(e221.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e221,Parameters.cutoff,AQ.reserve]
theorem FTO:AM.AW e221.cutoff 131071 1944 36 17 120=479097241276161:=by decide+kernel
theorem rank_e221:AR.rankBound 88 1944 36 17 120=1825177508:=by decide+kernel
theorem GRJ:Dimension e221 637908619009:=by
  exact AZ e221 637908619009 479097241276161 1825177508
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e221 FTO rank_e221 (by decide)

def e222:Parameters:=⟨84,2152,34,15,115,3,4⟩
theorem shape_e222:Shape e222:=by constructor<;>decide+kernel
theorem middle_e222 (h:ℕ) (hh:h≤15):115≤(e222.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e222,Parameters.cutoff,AQ.reserve]
theorem FOZ:AM.AW e222.cutoff 131071 2152 34 15 115=432675921274034:=by decide+kernel
theorem rank_e222:AR.rankBound 84 2152 34 15 115=1649281933:=by decide+kernel
theorem GNE:Dimension e222 326558229682:=by
  exact AZ e222 326558229682 432675921274034 1649281933
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e222 FOZ rank_e222 (by decide)

def e223:Parameters:=⟨87,1816,38,17,119,3,4⟩
theorem shape_e223:Shape e223:=by constructor<;>decide+kernel
theorem middle_e223 (h:ℕ) (hh:h≤17):119≤(e223.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e223,Parameters.cutoff,AQ.reserve]
theorem FOY:AM.AW e223.cutoff 131071 1816 38 17 119=469311949739634:=by decide+kernel
theorem rank_e223:AR.rankBound 87 1816 38 17 119=1788207720:=by decide+kernel
theorem GRZ:Dimension e223 544025187954:=by
  exact AZ e223 544025187954 469311949739634 1788207720
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e223 FOY rank_e223 (by decide)

def e224:Parameters:=⟨86,2156,36,17,117,3,4⟩
theorem shape_e224:Shape e224:=by constructor<;>decide+kernel
theorem middle_e224 (h:ℕ) (hh:h≤17):117≤(e224.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e224,Parameters.cutoff,AQ.reserve]
theorem FVC:AM.AW e224.cutoff 131071 2156 36 17 117=504950677987131:=by decide+kernel
theorem rank_e224:AR.rankBound 86 2156 36 17 117=1923312345:=by decide+kernel
theorem GSM:Dimension e224 765886619451:=by
  exact AZ e224 765886619451 504950677987131 1923312345
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e224 FVC rank_e224 (by decide)

def e225:Parameters:=⟨87,1806,38,17,119,3,4⟩
theorem shape_e225:Shape e225:=by constructor<;>decide+kernel
theorem middle_e225 (h:ℕ) (hh:h≤17):119≤(e225.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e225,Parameters.cutoff,AQ.reserve]
theorem FPT:AM.AW e225.cutoff 131071 1806 38 17 119=466654101683874:=by decide+kernel
theorem rank_e225:AR.rankBound 87 1806 38 17 119=1778127030:=by decide+kernel
theorem GRL:Dimension e225 528769531554:=by
  exact AZ e225 528769531554 466654101683874 1778127030
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e225 FPT rank_e225 (by decide)

def e226:Parameters:=⟨87,1657,38,17,119,3,4⟩
theorem shape_e226:Shape e226:=by constructor<;>decide+kernel
theorem middle_e226 (h:ℕ) (hh:h≤17):119≤(e226.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e226,Parameters.cutoff,AQ.reserve]
theorem FWR:AM.AW e226.cutoff 131071 1657 38 17 119=427052165653050:=by decide+kernel
theorem rank_e226:AR.rankBound 87 1657 38 17 119=1627924749:=by decide+kernel
theorem GMX:Dimension e226 301460251194:=by
  exact AZ e226 301460251194 427052165653050 1627924749
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e226 FWR rank_e226 (by decide)

def e227:Parameters:=⟨66,1861,28,14,90,2,3⟩
theorem shape_e227:Shape e227:=by constructor<;>decide+kernel
theorem middle_e227 (h:ℕ) (hh:h≤14):90≤(e227.cutoff h+28-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e227,Parameters.cutoff,AQ.reserve]
theorem FQT:AM.AW e227.cutoff 131071 1861 28 14 90=160994367162790:=by decide+kernel
theorem rank_e227:AR.rankBound 66 1861 28 14 90=613384045:=by decide+kernel
theorem GMU:Dimension e227 199420070310:=by
  exact AZ e227 199420070310 160994367162790 613384045
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e227 FQT rank_e227 (by decide)

def e228:Parameters:=⟨88,1922,36,17,120,3,4⟩
theorem shape_e228:Shape e228:=by constructor<;>decide+kernel
theorem middle_e228 (h:ℕ) (hh:h≤17):120≤(e228.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e228,Parameters.cutoff,AQ.reserve]
theorem FXF:AM.AW e228.cutoff 131071 1922 36 17 120=473531792756871:=by decide+kernel
theorem rank_e228:AR.rankBound 88 1922 36 17 120=1804070730:=by decide+kernel
theorem GJX:Dimension e228 605475311751:=by
  exact AZ e228 605475311751 473531792756871 1804070730
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e228 FXF rank_e228 (by decide)

def e229:Parameters:=⟨140,1192,60,28,192,4,5⟩
theorem shape_e229:Shape e229:=by constructor<;>decide+kernel
theorem middle_e229 (h:ℕ) (hh:h≤28):192≤(e229.cutoff h+60-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e229,Parameters.cutoff,AQ.reserve]
theorem FWU:AM.AW e229.cutoff 131071 1192 60 28 192=1856894101512680:=by decide+kernel
theorem rank_e229:AR.rankBound 140 1192 60 28 192=7083277265:=by decide+kernel
theorem GNY:Dimension e229 55466156520:=by
  exact AZ e229 55466156520 1856894101512680 7083277265
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e229 FWU rank_e229 (by decide)

def e230:Parameters:=⟨68,2013,27,13,93,2,3⟩
theorem shape_e230:Shape e230:=by constructor<;>decide+kernel
theorem middle_e230 (h:ℕ) (hh:h≤13):93≤(e230.cutoff h+27-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e230,Parameters.cutoff,AQ.reserve]
theorem FXW:AM.AW e230.cutoff 131071 2013 27 13 93=176670515827035:=by decide+kernel
theorem rank_e230:AR.rankBound 68 2013 27 13 93=672849875:=by decide+kernel
theorem GKQ:Dimension e230 286958195035:=by
  exact AZ e230 286958195035 176670515827035 672849875
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e230 FXW rank_e230 (by decide)

def e231:Parameters:=⟨50,1193,20,9,68,1,2⟩
theorem shape_e231:Shape e231:=by constructor<;>decide+kernel
theorem middle_e231 (h:ℕ) (hh:h≤9):68≤(e231.cutoff h+20-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e231,Parameters.cutoff,AQ.reserve]
theorem FVM:AM.AW e231.cutoff 131071 1193 20 9 68=32428629962534:=by decide+kernel
theorem rank_e231:AR.rankBound 50 1193 20 9 68=123565805:=by decide+kernel
theorem GRI:Dimension e231 36595576614:=by
  exact AZ e231 36595576614 32428629962534 123565805
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e231 FVM rank_e231 (by decide)

def e232:Parameters:=⟨78,922,34,16,107,2,3⟩
theorem shape_e232:Shape e232:=by constructor<;>decide+kernel
theorem middle_e232 (h:ℕ) (hh:h≤16):107≤(e232.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e232,Parameters.cutoff,AQ.reserve]
theorem FUZ:AM.AW e232.cutoff 131071 922 34 16 107=153760018443405:=by decide+kernel
theorem rank_e232:AR.rankBound 78 922 34 16 107=586304366:=by decide+kernel
theorem GNX:Dimension e232 63846722701:=by
  exact AZ e232 63846722701 153760018443405 586304366
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e232 FUZ rank_e232 (by decide)

def e233:Parameters:=⟨84,2357,34,15,115,3,4⟩
theorem shape_e233:Shape e233:=by constructor<;>decide+kernel
theorem middle_e233 (h:ℕ) (hh:h≤15):115≤(e233.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e233,Parameters.cutoff,AQ.reserve]
theorem FSQ:AM.AW e233.cutoff 131071 2357 34 15 115=474826673248974:=by decide+kernel
theorem rank_e233:AR.rankBound 84 2357 34 15 115=1809328713:=by decide+kernel
theorem GKP:Dimension e233 522007108302:=by
  exact AZ e233 522007108302 474826673248974 1809328713
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e233 FSQ rank_e233 (by decide)

def e234:Parameters:=⟨84,2193,34,15,115,3,4⟩
theorem shape_e234:Shape e234:=by constructor<;>decide+kernel
theorem middle_e234 (h:ℕ) (hh:h≤15):115≤(e234.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e234,Parameters.cutoff,AQ.reserve]
theorem FWB:AM.AW e234.cutoff 131071 2193 34 15 115=441106071669022:=by decide+kernel
theorem rank_e234:AR.rankBound 84 2193 34 15 115=1681291289:=by decide+kernel
theorem GMA:Dimension e234 365648005406:=by
  exact AZ e234 365648005406 441106071669022 1681291289
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e234 FWB rank_e234 (by decide)

def e235:Parameters:=⟨82,2436,34,15,112,3,4⟩
theorem shape_e235:Shape e235:=by constructor<;>decide+kernel
theorem middle_e235 (h:ℕ) (hh:h≤15):112≤(e235.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e235,Parameters.cutoff,AQ.reserve]
theorem FXX:AM.AW e235.cutoff 131071 2436 34 15 112=464285774623918:=by decide+kernel
theorem rank_e235:AR.rankBound 82 2436 34 15 112=1769458685:=by decide+kernel
theorem GSP:Dimension e235 432797103278:=by
  exact AZ e235 432797103278 464285774623918 1769458685
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e235 FXX rank_e235 (by decide)

def e236:Parameters:=⟨86,1992,36,17,117,3,4⟩
theorem shape_e236:Shape e236:=by constructor<;>decide+kernel
theorem middle_e236 (h:ℕ) (hh:h≤17):117≤(e236.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e236,Parameters.cutoff,AQ.reserve]
theorem FOV:AM.AW e236.cutoff 131071 1992 36 17 117=465643651828851:=by decide+kernel
theorem rank_e236:AR.rankBound 86 1992 36 17 117=1774179273:=by decide+kernel
theorem GRR:Dimension e236 553200487539:=by
  exact AZ e236 553200487539 465643651828851 1774179273
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e236 FOV rank_e236 (by decide)

def e237:Parameters:=⟨82,2441,34,15,112,3,4⟩
theorem shape_e237:Shape e237:=by constructor<;>decide+kernel
theorem middle_e237 (h:ℕ) (hh:h≤15):112≤(e237.cutoff h+34-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e237,Parameters.cutoff,AQ.reserve]
theorem FST:AM.AW e237.cutoff 131071 2441 34 15 112=465257384732478:=by decide+kernel
theorem rank_e237:AR.rankBound 82 2441 34 15 112=1773149435:=by decide+kernel
theorem GJL:Dimension e237 436899243838:=by
  exact AZ e237 436899243838 465257384732478 1773149435
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e237 FST rank_e237 (by decide)

def e238:Parameters:=⟨86,1997,36,17,117,3,4⟩
theorem shape_e238:Shape e238:=by constructor<;>decide+kernel
theorem middle_e238 (h:ℕ) (hh:h≤17):117≤(e238.cutoff h+36-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e238,Parameters.cutoff,AQ.reserve]
theorem FXE:AM.AW e238.cutoff 131071 1997 36 17 117=466842036772701:=by decide+kernel
theorem rank_e238:AR.rankBound 86 1997 36 17 117=1778726013:=by decide+kernel
theorem GNW:Dimension e238 559684820829:=by
  exact AZ e238 559684820829 466842036772701 1778726013
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e238 FXE rank_e238 (by decide)

def e239:Parameters:=⟨130,3502,54,24,177,6,8⟩
theorem shape_e239:Shape e239:=by constructor<;>decide+kernel
theorem middle_e239 (h:ℕ) (hh:h≤24):177≤(e239.cutoff h+54-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e239,Parameters.cutoff,AQ.reserve]
theorem FWX:AM.AW e239.cutoff 131071 3502 54 24 177=4016743174066017:=by decide+kernel
theorem rank_e239:AR.rankBound 130 3502 54 24 177=15322652525:=by decide+kernel
theorem GPQ:Dimension e239 1750552417:=by
  exact AZ e239 1750552417 4016743174066017 15322652525
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e239 FWX rank_e239 (by decide)

def e240:Parameters:=⟨133,3505,53,24,181,6,8⟩
theorem shape_e240:Shape e240:=by constructor<;>decide+kernel
theorem middle_e240 (h:ℕ) (hh:h≤24):181≤(e240.cutoff h+53-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e240,Parameters.cutoff,AQ.reserve]
theorem FWJ:AM.AW e240.cutoff 131071 3505 53 24 181=4129750355260400:=by decide+kernel
theorem rank_e240:AR.rankBound 133 3505 53 24 181=15753747086:=by decide+kernel
theorem GNI:Dimension e240 79148016:=by
  exact AZ e240 79148016 4129750355260400 15753747086
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e240 FWJ rank_e240 (by decide)

def e241:Parameters:=⟨115,3098,47,21,156,5,7⟩
theorem shape_e241:Shape e241:=by constructor<;>decide+kernel
theorem middle_e241 (h:ℕ) (hh:h≤21):156≤(e241.cutoff h+47-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e241,Parameters.cutoff,AQ.reserve]
theorem FUM:AM.AW e241.cutoff 131071 3098 47 21 156=2147563842499398:=by decide+kernel
theorem rank_e241:AR.rankBound 115 3098 47 21 156=8192297966:=by decide+kernel
theorem GKS:Dimension e241 2084500294:=by
  exact AZ e241 2084500294 2147563842499398 8192297966
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e241 FUM rank_e241 (by decide)

def e242:Parameters:=⟨114,3354,46,21,155,5,7⟩
theorem shape_e242:Shape e242:=by constructor<;>decide+kernel
theorem middle_e242 (h:ℕ) (hh:h≤21):155≤(e242.cutoff h+46-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e242,Parameters.cutoff,AQ.reserve]
theorem FRP:AM.AW e242.cutoff 131071 3354 46 21 155=2213703506034786:=by decide+kernel
theorem rank_e242:AR.rankBound 114 3354 46 21 155=8444604797:=by decide+kernel
theorem GKT:Dimension e242 1026130018:=by
  exact AZ e242 1026130018 2213703506034786 8444604797
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e242 FRP rank_e242 (by decide)

def e243:Parameters:=⟨131,3615,53,24,178,6,8⟩
theorem shape_e243:Shape e243:=by constructor<;>decide+kernel
theorem middle_e243 (h:ℕ) (hh:h≤24):178≤(e243.cutoff h+53-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e243,Parameters.cutoff,AQ.reserve]
theorem FPQ:AM.AW e243.cutoff 131071 3615 53 24 178=4114382719837948:=by decide+kernel
theorem rank_e243:AR.rankBound 131 3615 53 24 178=15695119118:=by decide+kernel
theorem GSS:Dimension e243 1413768956:=by
  exact AZ e243 1413768956 4114382719837948 15695119118
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e243 FPQ rank_e243 (by decide)

def e244:Parameters:=⟨130,3666,53,24,177,6,8⟩
theorem shape_e244:Shape e244:=by constructor<;>decide+kernel
theorem middle_e244 (h:ℕ) (hh:h≤24):177≤(e244.cutoff h+53-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e244,Parameters.cutoff,AQ.reserve]
theorem FTT:AM.AW e244.cutoff 131071 3666 53 24 177=4099763288934857:=by decide+kernel
theorem rank_e244:AR.rankBound 130 3666 53 24 177=15639342340:=by decide+kernel
theorem GST:Dimension e244 3530557897:=by
  exact AZ e244 3530557897 4099763288934857 15639342340
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e244 FTT rank_e244 (by decide)

def e245:Parameters:=⟨87,782,38,18,119,2,3⟩
theorem shape_e245:Shape e245:=by constructor<;>decide+kernel
theorem middle_e245 (h:ℕ) (hh:h≤18):119≤(e245.cutoff h+38-1)/131071:=by
  interval_cases h<;>first | decide | norm_num [e245,Parameters.cutoff,AQ.reserve]
theorem FXR:AM.AW e245.cutoff 131071 782 38 18 119=196988603037079:=by decide+kernel
theorem rank_e245:AR.rankBound 87 782 38 18 119=751444889:=by decide+kernel
theorem GNA:Dimension e245 1834055063:=by
  exact AZ e245 1834055063 196988603037079 751444889
    (by decide) (by decide) (by decide) (by decide) (by decide)
    middle_e245 FXR rank_e245 (by decide)

end BED

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace CN
open FF EZ BED
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
def profile:Fin 321→Parameters:= ![source0,source1,source2,source3,source4,source5,source6,source7,source8,source9,source10,source11,source12,source13,source14,source15,source16,source17,source18,source19,source20,source21,source22,source23,source24,source25,source26,source27,source28,source29,source30,source31,source32,source33,source34,source35,source36,source37,source38,source39,source40,source41,source42,source43,source44,source45,source46,source47,source48,source49,source50,source51,source52,source53,source54,source55,source56,source57,source58,source59,source60,source61,source62,source63,source64,source65,source66,source67,source68,source69,source70,source71,source72,source73,source74,e0,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,e11,e12,e13,e14,e15,e16,e17,e18,e19,e20,e21,e22,e23,e24,e25,e26,e27,e28,e29,e30,e31,e32,e33,e34,e35,e36,e37,e38,e39,e40,e41,e42,e43,e44,e45,e46,e47,e48,e49,e50,e51,e52,e53,e54,e55,e56,e57,e58,e59,e60,e61,e62,e63,e64,e65,e66,e67,e68,e69,e70,e71,e72,e73,e74,e75,e76,e77,e78,e79,e80,e81,e82,e83,e84,e85,e86,e87,e88,e89,e90,e91,e92,e93,e94,e95,e96,e97,e98,e99,e100,e101,e102,e103,e104,e105,e106,e107,e108,e109,e110,e111,e112,e113,e114,e115,e116,e117,e118,e119,e120,e121,e122,e123,e124,e125,e126,e127,e128,e129,e130,e131,e132,e133,e134,e135,e136,e137,e138,e139,e140,e141,e142,e143,e144,e145,e146,e147,e148,e149,e150,e151,e152,e153,e154,e155,e156,e157,e158,e159,e160,e161,e162,e163,e164,e165,e166,e167,e168,e169,e170,e171,e172,e173,e174,e175,e176,e177,e178,e179,e180,e181,e182,e183,e184,e185,e186,e187,e188,e189,e190,e191,e192,e193,e194,e195,e196,e197,e198,e199,e200,e201,e202,e203,e204,e205,e206,e207,e208,e209,e210,e211,e212,e213,e214,e215,e216,e217,e218,e219,e220,e221,e222,e223,e224,e225,e226,e227,e228,e229,e230,e231,e232,e233,e234,e235,e236,e237,e238,e239,e240,e241,e242,e243,e244,e245]
def kernel:Fin 321→ℕ:= ![7260213395,13643593099,40155413534,58535993077,141765009677,224994026277,308223042877,472006313,86754580641,187083155441,287411730241,227417347516,463288226,359487914,129218435499,124283931406,160107929851,154734661680,82271006165,66948285,362908635,12453647280,57234160780,102014674280,119926879680,137839085080,200194554453,965817129,590338538,1191135456,179530509,202162972,1214286957,1151425470,180411005730,1672002055,265429768430,1869533379,235343146221,384716188686,778958213,262457266433,521936597273,518439507372,660283745196,1974075240,709797541282,703637019867,627938057064,944024694,923820114,565670798298,759333723,642298602619,2927226213,1246555353,2345224732,324163819347,3136685820,3011184782,525479572736,488081982222,463711421491,714523966607,587428160452,573180551244,566447428719,557681210056,17923557169,17923557169,15359060400,15359060400,15359060400,15700646896,35838130011,272105016,5351324841,4902174593,63822533000,74250755910,47812422773,59473186455,20480303,531820662834,650323370963,575990486971,509917345806,550928385908,495207087474,89408419,493508783566,528814767323,476279793214,503752666260,452491249554,459050802862,478690565197,441821812510,455102705373,409775411634,86789299690,30874190214,425413250270,431514845549,769991397888,258298666395,192432435105,723448757352,244864512345,389483234506,678014274924,173524716315,66638068615,25305456222,366601414570,854073552195,343719594634,784042752663,204562050195,154616997525,34882953647,145163138130,712715086473,191575701280,135709278735,31514326787,126255419340,31106220797,52308304295,67839889657,25769517388,19040630481,99793208817,2990297482,11834829878,693549335635,620217724141,673901169875,601052588034,538215064090,527727563286,786806984148,518193471646,767641848041,507705970842,748476711934,498171879202,730785817066,487684378398,711620680959,477196877594,692455544852,467662785954,673290408745,35282771291,80520027800,410087362080,459082103478,657073755116,447641193510,436200283542,41507919805,182978575710,39935893937,357021167148,413318463606,231430358295,38251580507,164070856920,36567267077,278834858761,303954972216,217996204245,111112968374,33198640217,341124957834,320837774698,75519704580,178141547230,95363737686,29830013357,223933314245,43194411032,91426430014,292280134969,203393707348,45956178109,63397570267,10830124152,41315566449,94399130381,24989689962,60641764155,35453665251,9746108769,95305008838,31255648767,146842410708,626745572051,27857792635,4986792179,274644723612,258022351992,597326432258,285561635630,586838931454,280794589810,577304839814,276027543990,566817339010,271260498170,556329838206,266493452350,546795746566,261726406530,239368003943,219577207523,805972120255,341812776306,481963923414,337999139650,335138912158,471476422610,330371866338,327511638846,22523545754,386891927034,21539218836,321791183862,453361648494,507810154509,758909816808,498732087903,746720077620,490950887955,735638496540,481872821349,134244650947,474091621401,712367176272,465013554795,701285595192,126370035603,118987583718,355160504602,463948152807,443308775461,332278684666,421195156876,749027352897,103238353030,185241142485,399081538291,87981285801,55890745375,46639555245,242254233108,50596789769,34226339606,17641680550,11570510717,18576569315,65113629198,3968541621,1095040540,63604060216,24958624041,7155430926,617348024702,294142318106,606860523898,290328681450,362787777914,512473016662,358974141258,356113913766,501985515858,352300277110,431133330594,23507872672,348486640454,492451424218,344673003798,376190099,540231820959,804344299236,532450621011,793262718156,523372554405,781072978968,515591354457,142119266291,378042324538,506701148738,486061771392,654125272638,637908619009,326558229682,544025187954,765886619451,528769531554,301460251194,199420070310,605475311751,55466156520,286958195035,36595576614,63846722701,522007108302,365648005406,432797103278,553200487539,436899243838,559684820829,1750552417,79148016,2084500294,1026130018,1413768956,3530557897,1834055063]
theorem shape (i:Fin 321):Shape (profile i):=by
  fin_cases i
  · exact shape0
  · exact shape1
  · exact shape2
  · exact shape3
  · exact shape4
  · exact shape5
  · exact shape6
  · exact shape7
  · exact shape8
  · exact shape9
  · exact shape10
  · exact shape11
  · exact shape12
  · exact shape13
  · exact shape14
  · exact shape15
  · exact shape16
  · exact shape17
  · exact shape18
  · exact shape19
  · exact shape20
  · exact shape21
  · exact shape22
  · exact shape23
  · exact shape24
  · exact shape25
  · exact shape26
  · exact shape27
  · exact shape28
  · exact shape29
  · exact shape30
  · exact shape31
  · exact shape32
  · exact shape33
  · exact shape34
  · exact shape35
  · exact shape36
  · exact shape37
  · exact shape38
  · exact shape39
  · exact shape40
  · exact shape41
  · exact shape42
  · exact shape43
  · exact shape44
  · exact shape45
  · exact shape46
  · exact shape47
  · exact shape48
  · exact shape49
  · exact shape50
  · exact shape51
  · exact shape52
  · exact shape53
  · exact shape54
  · exact shape55
  · exact shape56
  · exact shape57
  · exact shape58
  · exact shape59
  · exact shape60
  · exact shape61
  · exact shape62
  · exact shape63
  · exact shape64
  · exact shape65
  · exact shape66
  · exact shape67
  · exact shape68
  · exact shape69
  · exact shape70
  · exact shape71
  · exact shape72
  · exact shape73
  · exact shape74
  · exact shape_e0
  · exact shape_e1
  · exact shape_e2
  · exact shape_e3
  · exact shape_e4
  · exact shape_e5
  · exact shape_e6
  · exact shape_e7
  · exact shape_e8
  · exact shape_e9
  · exact shape_e10
  · exact shape_e11
  · exact shape_e12
  · exact shape_e13
  · exact shape_e14
  · exact shape_e15
  · exact shape_e16
  · exact shape_e17
  · exact shape_e18
  · exact shape_e19
  · exact shape_e20
  · exact shape_e21
  · exact shape_e22
  · exact shape_e23
  · exact shape_e24
  · exact shape_e25
  · exact shape_e26
  · exact shape_e27
  · exact shape_e28
  · exact shape_e29
  · exact shape_e30
  · exact shape_e31
  · exact shape_e32
  · exact shape_e33
  · exact shape_e34
  · exact shape_e35
  · exact shape_e36
  · exact shape_e37
  · exact shape_e38
  · exact shape_e39
  · exact shape_e40
  · exact shape_e41
  · exact shape_e42
  · exact shape_e43
  · exact shape_e44
  · exact shape_e45
  · exact shape_e46
  · exact shape_e47
  · exact shape_e48
  · exact shape_e49
  · exact shape_e50
  · exact shape_e51
  · exact shape_e52
  · exact shape_e53
  · exact shape_e54
  · exact shape_e55
  · exact shape_e56
  · exact shape_e57
  · exact shape_e58
  · exact shape_e59
  · exact shape_e60
  · exact shape_e61
  · exact shape_e62
  · exact shape_e63
  · exact shape_e64
  · exact shape_e65
  · exact shape_e66
  · exact shape_e67
  · exact shape_e68
  · exact shape_e69
  · exact shape_e70
  · exact shape_e71
  · exact shape_e72
  · exact shape_e73
  · exact shape_e74
  · exact shape_e75
  · exact shape_e76
  · exact shape_e77
  · exact shape_e78
  · exact shape_e79
  · exact shape_e80
  · exact shape_e81
  · exact shape_e82
  · exact shape_e83
  · exact shape_e84
  · exact shape_e85
  · exact shape_e86
  · exact shape_e87
  · exact shape_e88
  · exact shape_e89
  · exact shape_e90
  · exact shape_e91
  · exact shape_e92
  · exact shape_e93
  · exact shape_e94
  · exact shape_e95
  · exact shape_e96
  · exact shape_e97
  · exact shape_e98
  · exact shape_e99
  · exact shape_e100
  · exact shape_e101
  · exact shape_e102
  · exact shape_e103
  · exact shape_e104
  · exact shape_e105
  · exact shape_e106
  · exact shape_e107
  · exact shape_e108
  · exact shape_e109
  · exact shape_e110
  · exact shape_e111
  · exact shape_e112
  · exact shape_e113
  · exact shape_e114
  · exact shape_e115
  · exact shape_e116
  · exact shape_e117
  · exact shape_e118
  · exact shape_e119
  · exact shape_e120
  · exact shape_e121
  · exact shape_e122
  · exact shape_e123
  · exact shape_e124
  · exact shape_e125
  · exact shape_e126
  · exact shape_e127
  · exact shape_e128
  · exact shape_e129
  · exact shape_e130
  · exact shape_e131
  · exact shape_e132
  · exact shape_e133
  · exact shape_e134
  · exact shape_e135
  · exact shape_e136
  · exact shape_e137
  · exact shape_e138
  · exact shape_e139
  · exact shape_e140
  · exact shape_e141
  · exact shape_e142
  · exact shape_e143
  · exact shape_e144
  · exact shape_e145
  · exact shape_e146
  · exact shape_e147
  · exact shape_e148
  · exact shape_e149
  · exact shape_e150
  · exact shape_e151
  · exact shape_e152
  · exact shape_e153
  · exact shape_e154
  · exact shape_e155
  · exact shape_e156
  · exact shape_e157
  · exact shape_e158
  · exact shape_e159
  · exact shape_e160
  · exact shape_e161
  · exact shape_e162
  · exact shape_e163
  · exact shape_e164
  · exact shape_e165
  · exact shape_e166
  · exact shape_e167
  · exact shape_e168
  · exact shape_e169
  · exact shape_e170
  · exact shape_e171
  · exact shape_e172
  · exact shape_e173
  · exact shape_e174
  · exact shape_e175
  · exact shape_e176
  · exact shape_e177
  · exact shape_e178
  · exact shape_e179
  · exact shape_e180
  · exact shape_e181
  · exact shape_e182
  · exact shape_e183
  · exact shape_e184
  · exact shape_e185
  · exact shape_e186
  · exact shape_e187
  · exact shape_e188
  · exact shape_e189
  · exact shape_e190
  · exact shape_e191
  · exact shape_e192
  · exact shape_e193
  · exact shape_e194
  · exact shape_e195
  · exact shape_e196
  · exact shape_e197
  · exact shape_e198
  · exact shape_e199
  · exact shape_e200
  · exact shape_e201
  · exact shape_e202
  · exact shape_e203
  · exact shape_e204
  · exact shape_e205
  · exact shape_e206
  · exact shape_e207
  · exact shape_e208
  · exact shape_e209
  · exact shape_e210
  · exact shape_e211
  · exact shape_e212
  · exact shape_e213
  · exact shape_e214
  · exact shape_e215
  · exact shape_e216
  · exact shape_e217
  · exact shape_e218
  · exact shape_e219
  · exact shape_e220
  · exact shape_e221
  · exact shape_e222
  · exact shape_e223
  · exact shape_e224
  · exact shape_e225
  · exact shape_e226
  · exact shape_e227
  · exact shape_e228
  · exact shape_e229
  · exact shape_e230
  · exact shape_e231
  · exact shape_e232
  · exact shape_e233
  · exact shape_e234
  · exact shape_e235
  · exact shape_e236
  · exact shape_e237
  · exact shape_e238
  · exact shape_e239
  · exact shape_e240
  · exact shape_e241
  · exact shape_e242
  · exact shape_e243
  · exact shape_e244
  · exact shape_e245
theorem dimension (i:Fin 321):Dimension (profile i) (kernel i):=by
  fin_cases i
  · exact dimension0
  · exact dimension1
  · exact dimension2
  · exact dimension3
  · exact dimension4
  · exact dimension5
  · exact dimension6
  · exact dimension7
  · exact dimension8
  · exact dimension9
  · exact dimension10
  · exact dimension11
  · exact dimension12
  · exact dimension13
  · exact dimension14
  · exact dimension15
  · exact dimension16
  · exact dimension17
  · exact dimension18
  · exact dimension19
  · exact dimension20
  · exact dimension21
  · exact dimension22
  · exact dimension23
  · exact dimension24
  · exact dimension25
  · exact dimension26
  · exact dimension27
  · exact dimension28
  · exact dimension29
  · exact dimension30
  · exact dimension31
  · exact dimension32
  · exact dimension33
  · exact dimension34
  · exact dimension35
  · exact dimension36
  · exact dimension37
  · exact dimension38
  · exact dimension39
  · exact dimension40
  · exact dimension41
  · exact dimension42
  · exact dimension43
  · exact dimension44
  · exact dimension45
  · exact dimension46
  · exact dimension47
  · exact dimension48
  · exact dimension49
  · exact dimension50
  · exact dimension51
  · exact dimension52
  · exact dimension53
  · exact dimension54
  · exact dimension55
  · exact dimension56
  · exact dimension57
  · exact dimension58
  · exact dimension59
  · exact dimension60
  · exact dimension61
  · exact dimension62
  · exact dimension63
  · exact dimension64
  · exact dimension65
  · exact dimension66
  · exact dimension67
  · exact dimension68
  · exact dimension69
  · exact dimension70
  · exact dimension71
  · exact dimension72
  · exact dimension73
  · exact dimension74
  · exact dimension_e0
  · exact dimension_e1
  · exact dimension_e2
  · exact dimension_e3
  · exact dimension_e4
  · exact dimension_e5
  · exact dimension_e6
  · exact dimension_e7
  · exact dimension_e8
  · exact dimension_e9
  · exact GXY
  · exact GYD
  · exact GTZ
  · exact GYA
  · exact GVC
  · exact GTN
  · exact GXN
  · exact GVQ
  · exact GUJ
  · exact GXW
  · exact GTC
  · exact GYF
  · exact GXQ
  · exact GUW
  · exact GUH
  · exact GWB
  · exact GWZ
  · exact GTT
  · exact GUM
  · exact GWS
  · exact GTX
  · exact GUV
  · exact GYE
  · exact GXR
  · exact GXP
  · exact GUY
  · exact GTR
  · exact GUX
  · exact GWI
  · exact GTK
  · exact GTU
  · exact GVY
  · exact GWD
  · exact GWQ
  · exact GUD
  · exact GTI
  · exact GWV
  · exact GUC
  · exact GXC
  · exact GWU
  · exact GXU
  · exact GYN
  · exact GTS
  · exact GXB
  · exact GVL
  · exact GXJ
  · exact GWC
  · exact GWM
  · exact GXO
  · exact GYG
  · exact GXZ
  · exact GWR
  · exact GYK
  · exact GTA
  · exact GVT
  · exact GWK
  · exact GUF
  · exact GVZ
  · exact GXK
  · exact GUK
  · exact GTO
  · exact GXS
  · exact GXG
  · exact GVJ
  · exact GVH
  · exact GTH
  · exact GYL
  · exact GVN
  · exact GVO
  · exact GWH
  · exact GWL
  · exact GUU
  · exact GXI
  · exact GWX
  · exact GTF
  · exact GUZ
  · exact GWN
  · exact GXA
  · exact GYB
  · exact GWG
  · exact GVD
  · exact GUT
  · exact GVB
  · exact GVK
  · exact GXL
  · exact GTJ
  · exact GUN
  · exact GVS
  · exact GUG
  · exact GWA
  · exact GRP
  · exact GMY
  · exact GMQ
  · exact GPO
  · exact GMF
  · exact GQZ
  · exact GKA
  · exact GKX
  · exact GMN
  · exact GQP
  · exact GNP
  · exact GOU
  · exact GPH
  · exact GQW
  · exact GKC
  · exact GSD
  · exact GRQ
  · exact GOP
  · exact GJS
  · exact GOI
  · exact GQG
  · exact GOX
  · exact GQB
  · exact GQN
  · exact GJB
  · exact GPN
  · exact GQL
  · exact GPI
  · exact GQM
  · exact GOO
  · exact GSA
  · exact GMC
  · exact GJR
  · exact GLK
  · exact GPJ
  · exact GIZ
  · exact GJC
  · exact GSF
  · exact GKM
  · exact GPF
  · exact GPX
  · exact GPK
  · exact GJT
  · exact GOD
  · exact GPL
  · exact GNJ
  · exact GMI
  · exact GLL
  · exact GND
  · exact GNK
  · exact GJZ
  · exact GLM
  · exact GQJ
  · exact GPU
  · exact GMZ
  · exact GOS
  · exact GNZ
  · exact GSE
  · exact GSL
  · exact GON
  · exact GRO
  · exact GQE
  · exact GLQ
  · exact GLP
  · exact GLX
  · exact GOZ
  · exact GKR
  · exact GMR
  · exact GLR
  · exact GLJ
  · exact GSR
  · exact GPV
  · exact GMB
  · exact GOV
  · exact GMD
  · exact GLD
  · exact GJD
  · exact GNU
  · exact _Q26
  · exact GRX
  · exact GQR
  · exact GNQ
  · exact GQT
  · exact GOW
  · exact GSC
  · exact GLC
  · exact GJY
  · exact GRG
  · exact GPZ
  · exact GME
  · exact GPT
  · exact GSJ
  · exact GQY
  · exact GNM
  · exact GPP
  · exact GOQ
  · exact GRK
  · exact GNG
  · exact GQU
  · exact GKH
  · exact GJO
  · exact GQF
  · exact GJM
  · exact GRY
  · exact GKF
  · exact GJP
  · exact GOA
  · exact GPS
  · exact GRT
  · exact GSK
  · exact GOL
  · exact GKD
  · exact GMK
  · exact GLY
  · exact GRV
  · exact GQI
  · exact GKB
  · exact GPW
  · exact GOY
  · exact GNR
  · exact GRD
  · exact GRJ
  · exact GNE
  · exact GRZ
  · exact GSM
  · exact GRL
  · exact GMX
  · exact GMU
  · exact GJX
  · exact GNY
  · exact GKQ
  · exact GRI
  · exact GNX
  · exact GKP
  · exact GMA
  · exact GSP
  · exact GRR
  · exact GJL
  · exact GNW
  · exact GPQ
  · exact GNI
  · exact GKS
  · exact GKT
  · exact GSS
  · exact GST
  · exact GNA
theorem positive (i:Fin 321):0<kernel i:=by
  fin_cases i<;>decide+kernel
end CN

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace ER
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 25000
open scoped Classical
open RCN095 RCN135 RCN136 RCN156 RCN174 RCN234 RCN238 RCN243 RCN260 RCN319
open DU BD GZ
open BX OR
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}

def pair (t y r b u l:ℕ):DG:=⟨262144,131071,181235,y,r,t,u,b,l⟩

def Gates (t y r b u l:ℕ):Prop:=
  (pair t y r b u l).mixedCost.y<2130706433∧
  (pair t y r b u l).mixedCost.r<2130706433∧
  (pair t y r b u l).mixedCost.z<2130706433

theorem DHG (P:Packet x t y r) (Q:MvPolynomial (Fin 4) K)
    (b u l:ℕ) (hrel:IsRelPrime P.F Q)
    (hweights:wt BE Q≤b∧wt BC Q≤u∧wt AT Q≤l)
    (hgates:Gates t y r b u l)
    (hzero: ∀gamma∈P.seeds,BM K (P.selected gamma) gamma Q=0):
    P.seeds.card≤GB.FU (pair t y r b u l):=by
  have hrlo:=P.rlow
  have hrhi:=P.rhigh
  have hyhi:=P.yhigh
  have hthi:=P.thigh
  have hQ:=ZM.ATW Q b u l hweights
  have hc:=BCH.BUM (pair t y r b u l) P.F Q
    P.irreducible P.rdegree hrel 2130706433 P.IZ.1 P.IZ.2.1 P.IZ.2.2
    hQ.1 hQ.2.1 hQ.2.2 (by dsimp [pair];omega) (by dsimp [pair];omega)
    (by dsimp [pair];omega) (by dsimp [pair];omega) hgates.1 hgates.2.1 hgates.2.2
    P.selected P.seeds P.nodes x P.u0 P.u1 P.injective P.nodeCount
    (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair]) (by norm_num [pair])
    P.degree P.agreement
    (by simpa only [pair,DG.errors,Nat.reduceSub,RCN326.w] using P.noPencil)
    P.solution P.regular hzero
  exact ZM.DUQ (pair t y r b u l) P.F P.IZ.1
    P.IZ.2.1 P.IZ.2.2 P.seeds.card (by norm_num [pair,DG.gap]) hc

theorem EVD (F:MvPolynomial (Fin 4) K) (S:Source F):
    wt BE (asS S.P).leadingCoeff≤S.B-2*S.n0∧
    wt BC (asS S.P).leadingCoeff≤S.U-S.n0∧
    wt AT (asS S.P).leadingCoeff≤S.T-S.n0:=by
  have hn:=S.hn
  have hw:=OE S.P S.B S.U S.T 0 (asS S.P).natDegree S.hshape
  simp only [Function.iterate_zero,id_eq,Nat.mul_zero,Nat.sub_zero] at hw
  rw [Polynomial.leadingCoeff]
  omega

def leadingPrice {F:MvPolynomial (Fin 4) K} (S:Source F) (t y r:ℕ):ℕ:=
  GB.FU (pair t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0))

theorem DOU (P:Packet x t y r) (S:Source P.F)
    (hFT:S.T<wt AT P.F)
    (hgates:Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)):
    (P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (AL K) P.selected gamma)
      (S.leading (AL K))=0)).card≤leadingPrice S t y r:=by
  let bad:=P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (AL K) P.selected gamma)
    (S.leading (AL K))=0)
  let PB:=P.restrict bad (Finset.filter_subset _ _)
  have hnot:=AFH.CAK S.P (AHY P.F S) P.F S.T
    (fun e he=>(S.hshape e he).2.2) hFT
  have hzero: ∀gamma∈bad,BM K (P.selected gamma) gamma (asS S.P).leadingCoeff=0:=by
    intro gamma hg
    have hh:=(Finset.mem_filter.mp hg).2
    change MvPolynomial.eval (DK (AL K) P.selected gamma)
      (surfaceMap (AL K) (asS S.P).leadingCoeff)=0 at hh
    rw [RCN170.XH] at hh
    exact DI K (by simpa only [map_zero] using hh)
  exact DHG PB (asS S.P).leadingCoeff (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0)
    (P.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2) (EVD P.F S) hgates hzero

end
end ER
end MergedPart0
section MergedPart1
namespace BOE
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN057 (WeightBound)
open RCN002 RCN046 RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN327 RCN334 RCN338 RCN341
open RCN206 RCN209 RCN340 RCN344
open FA GJ ID PR
open BD HK HFreeDir6813
open DU BLL AYR
open BIO BBT _Q7
open AFA RL TW
open GZ CB
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
local notation "Ω" =>GenericField K
local notation "Ext" =>AlgebraicClosure (RatFunc Ω)

abbrev Curve (P:Packet x t y r):=(g:EX K P.F) × CM (P.stage g)

def active (P:Packet x t y r) (SZ:Source P.F):Finset (Curve P):=
  Finset.univ.filter (fun a=>SZ.leading (AL K)∉a.2.1)

def multiplicity (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1)) (a:Curve P):ℕ:=
  FO (MU (P.stage a.1))
    (DN (MU (P.stage a.1)) (P.stage_proper hp a.1)) a.2

def ordinary (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1))
    (geometry: ∀g,ABN (P.stage g)) (a:Curve P) (W:FlagDegree):ℕ:=
  (BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).weightedCost W a.2

private theorem mixed_swap (p q r:FlagDegree):flagMixed p q r=flagMixed p r q:=by
  unfold flagMixed
  ring

private theorem FPS {A:Type} [Fintype A]
    (scale:ℕ) (weight:Fin 3→ℕ) (mu:A→ℕ) (degree:Fin 3→A→ℕ):
    (∑ j:Fin 3,weight j*(scale*∑ a,mu a*degree j a))=
      scale*(∑ a,mu a*(∑ j:Fin 3,weight j*degree j a)):=by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem FOX (W:FlagDegree) (scale coeff z u v:ℕ) (fixed:Fin 3→ℕ):
    (∑ j:Fin 3,weight W j*(scale*fixed j+coeff*price (BD.direction j) z u v))=
      scale*(∑ j:Fin 3,weight W j*fixed j)+coeff*price W z u v:=by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Nat.mul_left_comm,←Finset.mul_sum]
  rw [GEV]

theorem ELK
    (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1))
    (SZ SP SQ:Source P.F) (hZd:SZ.k<2130706433)
    (hcop:IsRelPrime SP.P SQ.P) (delta:ℕ) (hd:0<delta) (hdchar:delta≤2130706433)
    (hP:delta≤SP.d) (hQ:delta≤SQ.d)
    (hz:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433):
    ∃(geometry: ∀g,ABN (P.stage g))
      (budget: ∀a:Curve P,RD a.2.1 (baseH P.F) (baseG P.F)),
      (∀a,(budget a).zCost=(BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).zCost a.2∧
        (budget a).yzCost=(BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).yzCost a.2∧
        (budget a).allCost=(BLJ (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1)).allCost a.2)∧
      (∑ a∈active P SZ,(multiplicity P hp a*ordinary P hp geometry a (cellNormal t y r)+
        65539*(budget a).movingCost))≤DTH SZ SP SQ delta t y r ⟨t-y,y-r,r⟩:=by
  have hrlo:=P.rlow
  have hrhi:=P.rhigh
  have hylo:=P.ylow
  have hyhi:=P.yhigh
  have hyt:=P.yt
  have hthi:=P.thigh
  have hflags (g:EX K P.F):(CO K g).yz+(CO K g).all<2130706433∧
      (CO K g).all<2130706433∧
      (CO K g).zOnly+(CO K g).yz+(CO K g).all<2130706433:=by
    have hh:=P.stage_flag g
    omega
  have hmixed (g:EX K P.F):=AQW.reduced_gate
    (CO K g) t y r (by omega) (by omega) (by omega) (by omega) (by omega)
    (P.stage_flag g).1 (P.stage_flag g).2.1
  obtain ⟨lam,mu,hlam,hmu,geometry,heq⟩:=DYG
    (KK K P.F P.selected P.seeds) x (CO K) P.stage
    (P.stage_proper hp) hflags hmixed
  let unit:=fun g=>suppliedUnit (P.stage g) (P.stage_proper hp g) (geometry g)
  let scale:=SZ.d*delta
  let zCap:=delta*flagMixed ⟨t-y,y-r,r⟩ unitZFlag SZ.flag
  let uCap:=SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag
  let vCap:=SZ.d*flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitAllFlag
  let live:=active P SZ
  have hscale:0<scale:=Nat.mul_pos (by dsimp [Source.d];omega) hd
  have hFchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by omega:r<2130706433)
  have hraw: ∀Q A:MvPolynomial (Fin 3) Ω,(2:MvPolynomial (Fin 3) Ω)*A≠0→
      BI (2 • unitAllFlag) Q→BI unitYZFlag A→
      AGN (RingHom.id Ω) P.F SZ Q A scale zCap uCap vCap:=by
    intro Q A hden hQf hAf
    exact BSF (RingHom.id Ω) P.F P.irreducible.ne_zero P.rdegree hFchar
      SP SQ hcop delta hd hP hQ (by omega) SZ hZd ⟨t-y,y-r,r⟩ (P.parent_flag _ _) (by dsimp;omega)
      Q A hden hQf hAf (by omega) (by omega)
  obtain ⟨budget,hcost,hmoving⟩:=CTF P.F SZ
    (fun a:Curve P=>a.1.val) (fun a=>(P.stage a.1).RR)
    (cellA t y) (cellB y r) (cellS r) w (by decide)
    P.support.IZ.2.1 P.support.ys_weight P.support.total_weight
    (fun a:Curve P=>suppliedBase (P.stage a.1) (geometry a.1))
    (fun a:Curve P=>CO K a.1) (TX t y r)
    (fun a:Curve P=>unit a.1) (fun a:Curve P=>a.2) (P.FDF hp)
    live (fun a ha=>(Finset.mem_filter.mp ha).2) scale zCap uCap vCap hraw
  refine ⟨geometry,budget,hcost,?_⟩
  let projection:(j:Fin 3)→(a:Curve P)→Coordinate Ω (AJ Ω a.2.1):=
    fun j a=> ![(unit a.1).zProjection a.2,(unit a.1).yzProjection a.2,(unit a.1).NV a.2] j
  have hvalue (j:Fin 3) (a:Curve P):FT Ω (AJ Ω a.2.1) (projection j a)=
      BR Ω a.2.1 (DSG lam mu j):=by
    fin_cases j
    · exact FKV (unit a.1) a.2
    · exact GDG (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam (heq a.1).1 a.2
    · exact GAA (P.stage a.1) (P.stage_proper hp a.1) (geometry a.1) lam mu (heq a.1).1 (heq a.1).2 a.2
  have hR:WeightBound BE P.F (r:ℤ):=Or.inr (by exact_mod_cast P.r_weight)
  have hYR:WeightBound BC P.F ((r+(y-r):ℕ):ℤ):=Or.inr (by exact_mod_cast (show wt BC P.F≤r+(y-r) by have:=P.y_weight;omega))
  have hAll:MvPolynomial.weightedTotalDegree AT P.F≤r+(y-r)+(t-y):=by
    have hh:MvPolynomial.weightedTotalDegree AT P.F≤t:=P.total_weight
    omega
  have hnormal (j:Fin 3):
      3*scale*(∑ a:live,multiplicity P hp a.val*DQ Ω (AJ Ω a.val.2.1) (projection j a.val))≤
        scale*flagMixed ⟨t-y,y-r,r⟩ (ASY t y r j) (BD.direction j)+
          4*(w+1)*price (BD.direction j) zCap uCap vCap:=by
    have hh:=DXA (E:=Ext)
      (fun a:live=>KK K P.F P.selected P.seeds a.val.1)
      (fun a:live=>CO K a.val.1)
      (fun a:live=>MU (P.stage a.val.1))
      P.F P.irreducible.ne_zero (fun _=>rfl) ⟨t-y,y-r,r⟩ P.parent_flag
      (fun a=>P.stage_proper hp a.val.1) (fun a:live=>a.val.2)
      (fun a b hh=>Subtype.ext (P.FDF hp hh))
      lam mu hlam hmu j (fun a=>projection j a.val) (fun a=>hvalue j a.val) (by dsimp;omega)
      SZ SP SQ (fun a=>(Finset.mem_filter.mp a.property).2) r (y-r) (t-y) (by omega) (by omega)
      hR hYR hAll (by omega) P.rdegree hFchar hcop delta hd hP hQ (by omega) hZd (by omega) (by omega)
    simpa only [multiplicity,scale,zCap,uCap,vCap,price,ASY,mixed_swap] using hh
  let normal:=cellNormal t y r
  have hordinary (a:Curve P):ordinary P hp geometry a normal=
      ∑ j:Fin 3,weight normal j*DQ Ω (AJ Ω a.2.1) (projection j a):=by
    simp only [Fin.sum_univ_three,projection,weight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      ordinary,BLJ,FE.weightedCost,unit,
      EE.toFE,QZ.toFE,
      EE.toQZ]
    rfl
  have hnormalSum:3*scale*(∑ a∈live,multiplicity P hp a*ordinary P hp geometry a normal)≤
      scale*(∑ j:Fin 3,weight normal j*flagMixed ⟨t-y,y-r,r⟩
        (ASY t y r j) (BD.direction j))+
          4*(w+1)*price normal zCap uCap vCap:=by
    have hh:=Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin 3)))=>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    rw [FPS,FOX] at hh
    rw [←Finset.sum_coe_sort live (fun a=>multiplicity P hp a*ordinary P hp geometry a normal)]
    simpa only [hordinary] using hh
  have hmove:scale*(∑ a∈live,(budget a).movingCost)≤price (rawFirstFlag t y r) zCap uCap vCap:=hmoving
  have hjoint:(3*scale)*(∑ a∈live,(multiplicity P hp a*ordinary P hp geometry a normal+
      65539*(budget a).movingCost))≤CZ scale zCap uCap vCap t y r ⟨t-y,y-r,r⟩:=by
    have hh:=Nat.add_le_add hnormalSum (Nat.mul_le_mul_left (3*65539) hmove)
    convert hh using 1
    · simp only [Finset.sum_add_distrib,←Finset.mul_sum];ring
    · rfl
  apply (Nat.le_div_iff_mul_le (by omega:0<3*scale)).mpr
  change (∑ a∈live,(multiplicity P hp a*ordinary P hp geometry a normal+
    65539*(budget a).movingCost))*(3*scale)≤CZ scale zCap uCap vCap t y r ⟨t-y,y-r,r⟩
  exact (Nat.mul_comm _ _).trans_le hjoint

end
end BOE
end MergedPart1
section MergedPart2
namespace EF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159 RCN174 RCN198
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN313 RCN327 RCN334
open RCN085 RCN087 RCN199 RCN206 RCN207 RCN271 RCN287 RCN312 RCN330 RCN332 RCN335 RCN336 RCN338 RCN339 RCN341
open FA GJ ID DU
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}

def MG (t y r:ℕ):ℕ:=
  131073*80910*IY ⟨t-y,y-r,r⟩ (cellA t y) (cellB y r) (cellS r) w/50164

theorem CNE (P:Packet x t y r) (hidentity:P.F∣numerator K P.F (w+1)):
    P.seeds.card≤MG t y r:=by
  have hrlo:=P.rlow
  have hrhi:=P.rhigh
  have hylo:=P.ylow
  have hyhi:=P.yhigh
  have hyt:=P.yt
  have hthi:=P.thigh
  let cost:=fun g:EX K P.F=>
    IY (CO K g) (cellA t y) (cellB y r) (cellS r) w
  have hsingle (g:EX K P.F):
      (KK K P.F P.selected P.seeds g).card*50164≤131073*80910*cost g:=by
    let S:=P.stage g
    have hflag:=P.stage_flag g
    have hflagChar:(CO K g).yz+(CO K g).all<2130706433∧
        (CO K g).all<2130706433∧
        (CO K g).zOnly+(CO K g).yz+(CO K g).all<2130706433:=by omega
    have hTailNumerator:S.G∣surfaceMap (AL K) (numerator K S.F (w+1)):=
      S.RR.trans (map_dvd (surfaceMap (AL K)) hidentity)
    have hmixed:=AQW.EJG (CO K g) t y r
      (by omega) (by omega) (by omega) (by omega) (by omega) hflag.1 hflag.2.1
    have hnodes:S.nodes.card=262144:=P.nodeCount
    have hprovider:=BRK.AAB S 181235
      hnodes (P.CVV g) (by decide) hTailNumerator P.D t r (by decide)
      P.Dlow P.Dchar P.box hflagChar hmixed
    have hpositive:1≤cost g:=by
      apply Lower80788.FixedStage.CVP
      have hh:=S.y_dependent
      have hd:=AHE S.G (CO K g) S.flag_support 1
      omega
    have hinc:=AQH S 181235 _ hprovider (P.CVV g)
      (by decide) (by rw [hnodes];decide) hpositive
    simpa only [cost,hnodes,RCN326.w,Nat.reduceSub,Nat.reduceAdd] using hinc
  have hb:=VD P.F P.irreducible.ne_zero
  have hc:=GX P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hz:=TO (CO K) ⟨t-y,y-r,r⟩
    (RCN203.paddedCut (cellA t y) (cellB y r) (cellS r) (w+1)) unitZFlag
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp;omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp;omega))
  have hu:=TO (CO K) ⟨t-y,y-r,r⟩
    (RCN203.paddedCut (cellA t y) (cellB y r) (cellS r) (w+1)) unitYZFlag
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp;omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp;omega))
  have hcost:(∑ g,cost g)≤IY ⟨t-y,y-r,r⟩ (cellA t y) (cellB y r) (cellS r) w:=by
    simpa only [cost,IY,Finset.sum_add_distrib] using Nat.add_le_add hz hu
  have hsum:=Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>hsingle g)
  simp only [←Finset.sum_mul,←Finset.mul_sum] at hsum
  have hfinal:=(Nat.mul_le_mul_right 50164 P.seeds_cover).trans
    (hsum.trans (Nat.mul_le_mul_left (131073*80910) hcost))
  exact (Nat.le_div_iff_mul_le (by decide:0<50164)).mpr hfinal

end
end EF
end MergedPart2
section MergedPart3
namespace BTJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334 RCN338 RCN339 RCN341
open FA GJ ID IB
open BD DU BOE
open AYR AFA TW
open GZ CB
open EF ER
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
local notation "Ω" =>GenericField K

theorem EKH
    (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1))
    (SZ SP SQ:Source P.F) (hZd:SZ.k<2130706433)
    (hcop:IsRelPrime SP.P SQ.P) (delta:ℕ) (hd:0<delta) (hdchar:delta≤2130706433)
    (hP:delta≤SP.d) (hQ:delta≤SQ.d)
    (hz:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433)
    (hgood: ∀gamma∈P.seeds,MvPolynomial.eval (DK (AL K) P.selected gamma)
      (SZ.leading (AL K))≠0):
    P.seeds.card≤DTH SZ SP SQ delta t y r ⟨t-y,y-r,r⟩:=by
  have hrlo:=P.rlow
  have hylo:=P.ylow
  have hyt:=P.yt
  obtain ⟨geometry,budget,hcost,hjoint⟩:=ELK P hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu
  let normal:=cellNormal t y r
  let cost (a:Curve P):=multiplicity P hp a*ordinary P hp geometry a normal+65539*(budget a).movingCost
  let live (g:EX K P.F):Finset (CM (P.stage g)):=
    Finset.univ.filter (fun C=>SZ.leading (AL K)∉C.1)
  have hsingle (g:EX K P.F):
      (KK K P.F P.selected P.seeds g).card≤∑ C∈live g,cost ⟨g,C⟩:=by
    let S:=P.stage g
    let B:=BLJ S (P.stage_proper hp g) (geometry g)
    let base:=suppliedBase S (geometry g)
    have htangent: ∀C:CM S,
        (∀delay,_Q2 (AL K) S.F (w+1+delay)∈C.1)→
        (HF Ω S.G (_Q2 (AL K) S.F (w+1))
          (CR (AL K) S.F) (KK K P.F P.selected P.seeds g)
          (DK (AL K) S.selected) C).card≤(80909+1)*B.yzCost C:=by
      intro C hall
      exact ALX S C (P.stage_proper hp g) (base C)
        181235 P.D t r P.nodeCount (P.CVV g) (by decide) (by decide)
        P.Dlow P.Dchar P.box B
        (EKM S (P.stage_proper hp g) (geometry g) C) hall
        (FDD S (P.stage_proper hp g) (geometry g) C)
    have hinactive: ∀C:CM S,C∉live g→
        (HF Ω S.G (_Q2 (AL K) S.F (w+1))
          (CR (AL K) S.F) (KK K P.F P.selected P.seeds g)
          (DK (AL K) S.selected) C).card=0:=by
      intro C hC
      have hmem:SZ.leading (AL K)∈C.1:=by
        simpa only [live,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hC
      exact AEF.BOK _ _ _
        (SZ.leading (AL K)) (KK K P.F P.selected P.seeds g)
        (DK (AL K) S.selected) C hmem
        (fun gamma hg=>hgood gamma (WK K P.F P.selected P.seeds g hg))
    obtain ⟨provider⟩:=APU.AYF
      t y r (by omega) (by omega) (by omega) (by decide) S (P.stage_proper hp g)
      (TX t y r) B base (fun C=>budget ⟨g,C⟩) (fun C=>hcost ⟨g,C⟩)
      (live g) (∑ C∈live g,cost ⟨g,C⟩) hinactive (le_refl _)
      (by dsimp [APU.cellNormal,JE.normalFlag,RCN327.w];omega) htangent
    exact BIF S provider
  have hsum:(∑ g,∑ C∈live g,cost ⟨g,C⟩)=∑ a∈active P SZ,cost a:=by
    simp only [live,active,Finset.sum_filter]
    rw [Fintype.sum_sigma]
  calc
    P.seeds.card≤∑ g,(KK K P.F P.selected P.seeds g).card:=P.seeds_cover
    _≤∑ g,∑ C∈live g,cost ⟨g,C⟩:=Finset.sum_le_sum (fun g _=>hsingle g)
    _=∑ a∈active P SZ,cost a:=hsum
    _≤_:=hjoint

theorem FRX
    (P:Packet x t y r) (SZ SP SQ:Source P.F)
    (hFT:SZ.T<wt AT P.F) (hZd:SZ.k<2130706433)
    (hgates:Gates t y r (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0))
    (hcop:IsRelPrime SP.P SQ.P) (delta:ℕ) (hd:0<delta) (hdchar:delta≤2130706433)
    (hP:delta≤SP.d) (hQ:delta≤SQ.d)
    (hz:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitZFlag<2130706433)
    (hu:flagMixed (ordinaryFlag SP.P) (ordinaryFlag SQ.P) unitYZFlag<2130706433):
    P.seeds.card≤max (MG t y r)
      (DTH SZ SP SQ delta t y r ⟨t-y,y-r,r⟩+leadingPrice SZ t y r):=by
  by_cases hp:P.F∣numerator K P.F (w+1)
  · exact (CNE P hp).trans (le_max_left _ _)
  let good:=P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (AL K) P.selected gamma)
    (SZ.leading (AL K))≠0)
  let bad:=P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (AL K) P.selected gamma)
    (SZ.leading (AL K))=0)
  let PG:=P.restrict good (Finset.filter_subset _ _)
  have hmain:=EKH PG hp SZ SP SQ hZd hcop delta hd hdchar hP hQ hz hu
    (fun gamma hg=>(Finset.mem_filter.mp hg).2)
  have hbad:bad.card≤leadingPrice SZ t y r:=DOU P SZ hFT hgates
  have hpartition:P.seeds.card=good.card+bad.card:=by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hmain hbad).trans (le_max_right _ _)

end
end BTJ
end MergedPart3
section MergedPart4
namespace BOP
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN332 RCN334 RCN338 RCN339 RCN341
open FA GJ ID DU
open BD HFreeDir6813
local notation "w" =>RCN326.w
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}
local notation "Ω" =>GenericField K

def BDD {F:MvPolynomial (Fin 4) K} (source:Source F) (t y r:ℕ) (fl:FlagDegree):ℕ:=
  numeratorDir (fun _=>source) (3*source.d) t y r fl

theorem EAP
    (P:Packet x t y r) (hp: ¬P.F∣numerator K P.F (w+1)) (source:Source P.F)
    (hk:source.k<2130706433)
    (hgood: ∀gamma∈P.seeds,MvPolynomial.eval (DK (AL K) P.selected gamma)
      (source.leading (AL K))≠0):
    (3*source.d)*P.seeds.card≤BDD source t y r ⟨t-y,y-r,r⟩:=by
  have hrlo:=P.rlow
  have hrhi:=P.rhigh
  have hylo:=P.ylow
  have hyhi:=P.yhigh
  have hyt:=P.yt
  have hthi:=P.thigh
  have hd:0<3*source.d:=by dsimp [Source.d];omega
  have hstage (g:EX K P.F):
      (3*source.d)*(KK K P.F P.selected P.seeds g).card≤BDD source t y r (CO K g):=by
    let S:=P.stage g
    have hflag:=P.stage_flag g
    have hc:(CO K g).yz+(CO K g).all<2130706433∧
        (CO K g).all<2130706433∧
        (CO K g).zOnly+(CO K g).yz+(CO K g).all<2130706433:=by omega
    have hm:=AQW.reduced_gate (CO K g) t y r
      (by omega) (by omega) (by omega) (by omega) (by omega) hflag.1 hflag.2.1
    have hproper:=P.stage_proper hp g
    let B:=KF.MQ S hproper hc hm
    have htangent: ∀C:CM S,
        (∀delay,_Q2 (AL K) S.F (w+1+delay)∈C.1)→
        (HF Ω S.G (_Q2 (AL K) S.F (w+1))
          (CR (AL K) S.F) (KK K P.F P.selected P.seeds g)
          (DK (AL K) S.selected) C).card≤80910*B.yzCost C:=by
      intro C hall
      exact ALX S C hproper (KF.AHP S hproper hc hm C)
        181235 P.D t r P.nodeCount (P.CVV g) (by decide) (by decide)
        P.Dlow P.Dchar P.box B (KF.ADY S hproper hc hm C) hall
        (KF.AJM S hproper hc hm C)
    have hh:=DAB t y r (3*source.d) (by omega) (by omega) (by omega)
      S (fun _=>source) hd (fun _=>dvd_rfl) (DIV S (by rw [P.support_caps.2.2];omega)) hproper hc hm
      (by omega)
      (by
        have htotal:=hflag.2.2.trans hthi
        calc
          _≤2*4100*4101:=Nat.mul_le_mul (Nat.mul_le_mul_left 2 htotal) (by omega)
          _<2130706433:=by decide)
      (by decide) (by dsimp [cellNormal,JE.normalFlag,RCN327.w];omega) htangent TI.two_ne
      (fun _=>TI.factorial_ne source.k hk)
      (fun gamma hgamma _=>hgood gamma (WK K P.F P.selected P.seeds g hgamma))
    exact (Nat.mul_comm _ _).trans_le ((Nat.le_div_iff_mul_le hd).mp hh)
  have hb:=VD P.F P.irreducible.ne_zero
  have hc:=GX P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hsum:=EHQ (fun _=>source) (3*source.d) t y r
    (CO K) ⟨t-y,y-r,r⟩
    (hb.1.trans P.r_weight)
    ((hb.2.1.trans P.y_weight).trans_eq (by dsimp;omega))
    ((hb.2.2.trans P.total_weight).trans_eq (by dsimp;omega))
  calc
    _≤(3*source.d)*(∑ g,(KK K P.F P.selected P.seeds g).card):=Nat.mul_le_mul_left _ P.seeds_cover
    _=∑ g,(3*source.d)*(KK K P.F P.selected P.seeds g).card:=Finset.mul_sum _ _ _
    _≤∑ g,BDD source t y r (CO K g):=Finset.sum_le_sum (fun g _=>hstage g)
    _≤_:=hsum

open EF ER

theorem FJO (P:Packet x t y r) (source:Source P.F)
    (hk:source.k<2130706433) (hFT:source.T<wt AT P.F)
    (hgates:Gates t y r (source.B-2*source.n0) (source.U-source.n0) (source.T-source.n0)):
    P.seeds.card≤max (MG t y r)
      (BDD source t y r ⟨t-y,y-r,r⟩/(3*source.d)+leadingPrice source t y r):=by
  by_cases hp:P.F∣numerator K P.F (w+1)
  · exact (CNE P hp).trans (le_max_left _ _)
  let good:=P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (AL K) P.selected gamma)
    (source.leading (AL K))≠0)
  let bad:=P.seeds.filter (fun gamma=>MvPolynomial.eval (DK (AL K) P.selected gamma)
    (source.leading (AL K))=0)
  let PG:=P.restrict good (Finset.filter_subset _ _)
  have hmain:=EAP PG hp source hk (fun gamma hg=>(Finset.mem_filter.mp hg).2)
  have hdiv:good.card≤BDD source t y r ⟨t-y,y-r,r⟩/(3*source.d):=by
    apply (Nat.le_div_iff_mul_le (by dsimp [Source.d];omega:0<3*source.d)).mpr
    exact (Nat.mul_comm good.card (3*source.d)).trans_le hmain
  have hbad:bad.card≤leadingPrice source t y r:=DOU P source hFT hgates
  have hpartition:P.seeds.card=good.card+bad.card:=by
    unfold good bad
    rw [Nat.add_comm]
    exact (Finset.card_filter_add_card_filter_not _).symm
  rw [hpartition]
  exact (Nat.add_le_add hdiv hbad).trans (le_max_right _ _)

end
end BOP
end MergedPart4
section MergedPart5
namespace ON
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 25000
open MvPolynomial CW DJ
open BD GZ DC
open LK CB FN
open ME NX
open BX FR DP RCN234 RCN156
variable {K:Type} [Field K] [CharP K 2130706433]

def multiplicity (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (J:Poly (K:=K)):ℕ:=
  ((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)





theorem DDZ (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hpos:0<F.degreeOf 2) (hchar:F.degreeOf 2<2130706433)
    (J:Poly (K:=K)) (m s b u t k n0:ℕ)
    (hkm:k+1≤m) (hkn:k+1≤n0) (hn:n0≤J.degreeOf 1) (hs:J.degreeOf 1≤s)
    (h2n:2*n0≤b) (hbu:b≤u) (hut:u≤t)
    (hshape: ∀e∈J.support,2*e 1+e 3≤b∧e 1+e 2+e 3≤u∧e 1+e 2+e 3+e 4≤t)
    (hroot:((asS J).map (carrierMap F)).rootMultiplicity (ratio (carrierMap F) F)=m):
    ∃S:Source F,S.P=J∧Profile S b u t s k n0:=by
  have hS: ∀e∈J.support,e 1≤s:=MvPolynomial.degreeOf_le_iff.mp hs
  have hH:=ALO F hpos hchar
  let source:Source F:={
    P:=J,B:=b,U:=u,T:=t,s:=s,k:=k,n0:=n0
    hS:=hS,hshape:=hshape,hBU:=hbu,hUT:=hut,hdn:=hkn,hB:=by omega
    hn:=by simpa only [ABW] using hn
    hdiv:=by
      intro d hd
      apply (TY F _).mp
      rw [CNM J F (carrierMap F) s d hS hH]
      have hz:((Polynomial.derivative)^[d] ((asS J).map (carrierMap F))).eval (ratio (carrierMap F) F)=0:=
        Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (by rw [hroot];omega)
      rw [hz,mul_zero]}
  exact ⟨source,rfl,by repeat' constructor⟩

end
end ON
end MergedPart5
section MergedPart6
namespace YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 25000
open MvPolynomial CW DJ
open BD GZ DC
open LK FN CB
open BX DP RCN234 RCN156
variable {K:Type} [Field K] [CharP K 2130706433]

theorem AVL (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (S:Source F) (hFT:S.T<wt AT F)
    (J:Poly (K:=K)) (hJ:Irreducible J) (hJS:J∣S.P)
    (hroot:NT (carrierMap F) (ratio (carrierMap F) F) J=0):
    (asS J).map (carrierMap F)≠0∧
    0<ON.multiplicity F J∧ON.multiplicity F J≤order J∧
    slope J≤S.B∧middle J≤S.U∧total J≤S.T∧order J≤S.s:=by
  have hP:=AHY F S
  have hne:=AKB F S.P hP S.T (fun e he=>(S.hshape e he).2.2) hFT
  have hJne:QC (carrierMap F) J≠0:=by
    intro hz
    have hd:=map_dvd (QC (carrierMap F)) hJS
    rw [hz,zero_dvd_iff] at hd
    exact hne hd
  have hm:0<ON.multiplicity F J:=(Polynomial.rootMultiplicity_pos hJne).mpr hroot
  have hms:ON.multiplicity F J≤order J:=by
    have hh:=Polynomial.natDegree_le_of_dvd
      ((QC (carrierMap F) J).pow_rootMultiplicity_dvd (ratio (carrierMap F) F)) hJne
    simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hh
    exact hh.trans (Polynomial.natDegree_map_le.trans_eq (ABW J))
  obtain ⟨Q,hEq⟩:=hJS
  have hQ:Q≠0:=by intro hz;exact hP (by rw [hEq,hz,mul_zero])
  obtain ⟨hb,hu,ht,hs⟩:=AZX.source_caps F S
  rw [hEq,weight_mul _ _ _ hJ.ne_zero hQ] at hb hu ht
  rw [hEq,degreeOf_mul_eq hJ.ne_zero hQ] at hs
  refine ⟨hJne,hm,hms,?_,?_,?_,?_⟩
  all_goals
    dsimp only [CB.slope,middle,total,order]
    omega





end
end YY
end MergedPart6
section MergedPart7
namespace BMA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open scoped Classical BigOperators
open RCN074 RCN084 RCN086 RCN095 RCN130 RCN135 RCN136 RCN156 RCN159 RCN174 RCN198 RCN199 RCN207
open RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264 RCN275 RCN312 RCN313 RCN327 RCN334
open DU EF ER
open MI DC BHE
open GF WW
open AIA CUT BTA
variable {K I:Type} [Field K] [CharP K 2130706433]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I
variable {x:I→K} {t y r:ℕ}

def linearPrice (first delay:FlagDegree) (t y r b u l:ℕ):ℕ:=
  r*GB.FU (pair t y r b u l)+
    flagMixed ⟨t-y,y-r,r⟩ first delay+
    80911*flagMixed ⟨t-y,y-r,r⟩ first unitYZFlag+
    flagMixed ⟨t-y,y-r,r⟩ first unitAllFlag

theorem packet_count
    (P:Packet x t y r) [Fact (Irreducible P.F)]
    (J:CW.Poly (K:=K)) (first delay:FlagDegree)
    (hroute:Route P.F J first delay) (b u l:ℕ)
    (hH:wt BE (linearH J)≤b∧wt BC (linearH J)≤u∧
      wt AT (linearH J)≤l)
    (hgates:Gates t y r b u l)
    (hsmall:flagMixed ⟨t-y,y-r,r⟩ first unitZFlag<2130706433):
    P.seeds.card≤max (MG t y r) (linearPrice first delay t y r b u l):=by
  by_cases hp:P.F∣numerator K P.F (RCN326.w+1)
  · exact (CNE P hp).trans (le_max_left _ _)
  let cap:=GB.FU (pair t y r b u l)
  let bad:=P.seeds.filter (fun gamma=>MvPolynomial.eval
    (DK (AL K) P.selected gamma)
    (surfaceMap (AL K) (linearH J))=0)
  let PB:=P.restrict bad (Finset.filter_subset _ _)
  have hrel:IsRelPrime P.F (linearH J):=P.irreducible.isRelPrime_iff_not_dvd.mpr
    (fun hd=>hroute.denominator ((TY P.F _).mpr hd))
  have hbad:bad.card≤cap:=by
    apply DHG PB (linearH J) b u l hrel hH hgates
    intro gamma hg
    have hh:=(Finset.mem_filter.mp hg).2
    rw [RCN170.XH] at hh
    change RCN319.BM K (P.selected gamma) gamma (linearH J)=0
    exact DI K (by simpa only [map_zero] using hh)
  have hb:=VD P.F P.irreducible.ne_zero
  have hc:=GX P.F
  rw [hc.2.2,hc.2.1,hc.1] at hb
  have hry:r≤y:=by have:=P.ylow;omega
  have hyt:=P.yt
  have hsum (W:FlagDegree):(∑ g:EX K P.F,
      flagMixed (CO K g) first W)≤flagMixed ⟨t-y,y-r,r⟩ first W:=by
    apply TO
    · exact hb.1.trans P.r_weight
    · simpa only [Nat.sub_add_cancel hry] using hb.2.1.trans P.y_weight
    · have ht:=hb.2.2.trans P.total_weight
      exact ht.trans_eq (by change t=(t-y)+(y-r)+r;omega)
  have hcard:Fintype.card (EX K P.F)≤r:=by
    have hone (g:EX K P.F):1≤(CO K g).all:=by
      have hd:=(P.stage g).y_dependent
      have hle:(P.stage g).G.degreeOf 1≤(CO K g).all:=
        MvPolynomial.degreeOf_le_iff.mpr (fun e he=>((P.stage g).flag_support e he).1)
      omega
    have hh:=(Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>hone g)).trans (hb.1.trans P.r_weight)
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using hh
  let cost (fl:FlagDegree):=flagMixed fl first delay+
    (flagMixed fl first unitYZFlag+flagMixed fl first unitAllFlag)+80910*flagMixed fl first unitYZFlag
  have hsingle (g:EX K P.F):
      (KK K P.F P.selected P.seeds g).card≤cap+cost (CO K g):=by
    let S:=P.stage g
    letI:Fact (Irreducible S.F):=⟨P.irreducible⟩
    have hfirst:=P.stage_proper hp g
    have hsmall' :flagMixed (CO K g) first unitZFlag<2130706433:=
      (ELU _ ⟨t-y,y-r,r⟩ first unitZFlag (by
        have h:=P.stage_flag g
        change _≤r∧_≤y-r+r∧_≤t-y+(y-r)+r
        omega)).trans_lt hsmall
    have hproper:=FLD S J hroute
    have hden:(BPG S J).card≤cap:=by
      apply (Finset.card_le_card (show BPG S J⊆bad from ?_)).trans hbad
      intro gamma hg
      exact Finset.mem_filter.mpr
        ⟨WK K P.F P.selected P.seeds g (Finset.mem_filter.mp hg).1,
          (Finset.mem_filter.mp hg).2⟩
    have hd:=ENS S hfirst J hroute (CO K g) S.flag_support hsmall'
    have hz:=EJI S hfirst J hroute hproper (CO K g) S.flag_support
    have ht:=EEB S hfirst J hroute hproper (CO K g)
      S.flag_support hsmall' 181235 P.D t r P.nodeCount (P.CVV g) (by decide) P.Dlow P.Dchar P.box
    have hh:=(FPI S hfirst J).trans (Nat.add_le_add hden (Nat.add_le_add hd (Nat.add_le_add hz ht)))
    exact hh.trans_eq (by dsimp only [cost];ring)
  have hcost:(∑ g:EX K P.F,cost (CO K g))≤cost ⟨t-y,y-r,r⟩:=by
    unfold cost
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact Nat.add_le_add (Nat.add_le_add (hsum delay) (Nat.add_le_add (hsum unitYZFlag) (hsum unitAllFlag)))
      (Nat.mul_le_mul_left 80910 (hsum unitYZFlag))
  have htotal:P.seeds.card≤r*cap+cost ⟨t-y,y-r,r⟩:=by
    have hh:=P.seeds_cover.trans (Finset.sum_le_sum (fun g (_:g∈Finset.univ)=>hsingle g))
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
    exact hh.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hcard) hcost)
  apply (htotal.trans_eq ?_).trans (le_max_right _ _)
  dsimp [linearPrice,cap,cost]
  ring

end
end BMA
end MergedPart7
section MergedPart8
namespace AOR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW MI NA
open ANU AIA BMA
open DU ER EF
open DC BX DP
variable {K:Type} [Field K]

theorem tail_weights (J:Poly (K:=K)) (B U L:ℕ) (hB:2≤B) (hBU:B≤U) (hUL:U≤L)
    (hshape: ∀e∈J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤L)
    (n:ℕ):
    wt BE (numerators (linearH J) (linearG J) n)≤(2*B-3)*n∧
    wt BC (numerators (linearH J) (linearG J) n)≤1+(2*U-2)*n∧
    wt AT (numerators (linearH J) (linearG J) n)≤1+(2*L-2)*n:=by
  have hh:=CQC J B U L hshape
  have hR:=EAZ BE (linearH J) (linearG J) (B-2) (B-1)
    hh.1.1 (by change _≤B-1+1;omega) (by change B-2≤B-1+0;omega)
    (by change 1+(B-2)≤B-1+0;omega) n
  have hY:=EAZ BC (linearH J) (linearG J) (U-1) (U-1)
    hh.1.2.1 (by change _≤U-1+1;omega) (by change U-1≤U-1+0;omega)
    (by change 1+(U-1)≤U-1+1;omega) n
  have hT:=EAZ AT (linearH J) (linearG J) (L-1) (L-1)
    hh.1.2.2 (by change _≤L-1+1;omega) (by change L-1≤L-1+0;omega)
    (by change 1+(L-1)≤L-1+1;omega) n
  have hr:(B-2)+(B-1)=2*B-3:=by omega
  have hy:(U-1)+(U-1)=2*U-2:=by omega
  have ht:(L-1)+(L-1)=2*L-2:=by omega
  exact ⟨by simpa only [show BE 1=0 from rfl,zero_add,hr,Nat.mul_comm] using hR,
    by simpa only [show BC 1=1 from rfl,hy,Nat.mul_comm] using hY,
    by simpa only [show AT 1=1 from rfl,ht,Nat.mul_comm] using hT⟩

variable [CharP K 2130706433] {I:Type} {x:I→K} {t y r:ℕ}

theorem BNL
    (P:Packet x t y r) [Fact (Irreducible P.F)]
    (J:Poly (K:=K)) (hJ:J≠0) (hs:J.degreeOf 1=1)
    (B U L:ℕ) (hB:2≤B) (hBU:B≤U) (hUL:U≤L)
    (hshape: ∀e∈J.support,2*e 1+e 3≤B∧e 1+e 2+e 3≤U∧e 1+e 2+e 3+e 4≤L)
    (hFT:L<wt AT P.F)
    (hroot:((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
    (hgates:Gates t y r (B-2) (U-1) (L-1))
    (hsmall:flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433):
    P.seeds.card≤max (MG t y r)
      (linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
        (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)):=by
  have hchar:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega:r<2130706433)
  have route:=GCI P.F J hJ hs P.rdegree hchar L
    (fun e he=>(hshape e he).2.2) hFT hroot (2*B-3) (2*U-2) (2*L-2)
    (by omega) (by omega) (tail_weights J B U L hB hBU hUL hshape)
  exact packet_count P J _ _ route (B-2) (U-1) (L-1)
    (CQC J B U L hshape).1 hgates hsmall

end
end AOR
end MergedPart8
section MergedPart9
namespace AJR
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open DU ER
open GF CB
open FF
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq I:=Classical.decEq I

theorem helper_count {t y r:ℕ} (p:Parameters) (nodes:I ↪ K)
    (P:Packet (nodes:I→K) t y r) (Q:MvPolynomial (Fin 4) K)
    (hh:ProperHelper p P.F Q r y t nodes P.u0 P.u1)
    (hg:Gates t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))):
    P.seeds.card≤GB.FU
      (pair t y r (p.B+p.s*(r-1)) (p.U+p.s*(y-1)) (p.L+p.s*(t-1))):=by
  classical
  apply DHG P Q _ _ _ hh.1 hh.2.1 hg
  intro gamma hgamma
  exact hh.2.2 (P.selected gamma) (P.degree gamma hgamma) gamma
    (P.nodes.filter (fun i=>(P.selected gamma).eval (nodes i)=P.u0 i+gamma*P.u1 i))
    (P.agreement gamma hgamma)
    (fun i hi=>by simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
    (P.solution gamma hgamma)



end
end AJR
end MergedPart9
section MergedPart10
namespace HI
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open scoped BigOperators
open RCN095 RCN135 RCN136 RCN156 RCN234
open BD CB
open DU ER EF
open BTJ BOP
open TW RL
open GF

structure Degrees where
  B:ℕ
  U:ℕ
  T:ℕ
  k:ℕ
  n0:ℕ
  deriving DecidableEq

def Degrees.d (z:Degrees):=z.k+1
def Degrees.flag (z:Degrees):=EJ.budgetFlag z.B z.U z.T z.d z.n0
def parent (t y r:ℕ):FlagDegree:=⟨t-y,y-r,r⟩
def leading (z:Degrees) (t y r:ℕ):ℕ:=
  GB.FU (pair t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
def pairCost (z:Degrees) (delta:ℕ) (p q:FlagDegree) (t y r:ℕ):ℕ:=
  CZ (z.d*delta) (delta*flagMixed (parent t y r) unitZFlag z.flag)
    (z.d*flagMixed p q unitYZFlag) (z.d*flagMixed p q unitAllFlag)
    t y r (parent t y r)/(3*(z.d*delta))

variable {K I:Type} [Field K] [CharP K 2130706433]
variable {F:MvPolynomial (Fin 4) K}

def Fits (S:Source F) (z:Degrees):Prop:=
  S.B=z.B∧S.U=z.U∧S.T=z.T∧S.k=z.k∧S.n0=z.n0

theorem fits_degree (S:Source F) (z:Degrees) (h:Fits S z):S.d=z.d:=by
  simp only [Source.d,Degrees.d,h.2.2.2.1]
theorem fits_flag (S:Source F) (z:Degrees) (h:Fits S z):S.flag=z.flag:=by
  simp only [Source.flag,Degrees.flag,h.1,h.2.1,h.2.2.1,h.2.2.2.2,fits_degree S z h]
theorem fits_leading (S:Source F) (z:Degrees) (h:Fits S z) (t y r:ℕ):
    leadingPrice S t y r=leading z t y r:=by
  simp only [leadingPrice,leading,h.1,h.2.1,h.2.2.1,h.2.2.2.2]

theorem stageCost_le (SZ SP SQ:Source F) (z:Degrees) (hZ:Fits SZ z)
    (delta:ℕ) (p q:FlagDegree) (t y r:ℕ)
    (hp:CumulativeLe (ordinaryFlag SP.P) p) (hq:CumulativeLe (ordinaryFlag SQ.P) q):
    DTH SZ SP SQ delta t y r (parent t y r)≤pairCost z delta p q t y r:=by
  unfold DTH stageScale pairCost
  rw [fits_degree SZ z hZ,fits_flag SZ z hZ]
  apply Nat.div_le_div_right
  have hu:=CAB _ _ _ _ unitYZFlag hp hq
  have hv:=CAB _ _ _ _ unitAllFlag hp hq
  simp only [CZ,price,parent]
  gcongr

variable {x:I→K} {t y r:ℕ}

theorem AHM
    (P:Packet x t y r) (SZ SP SQ:Source P.F)
    (z:Degrees) (hZ:Fits SZ z) (hFT:z.T<wt AT P.F)
    (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hcop:IsRelPrime SP.P SQ.P) (delta:ℕ) (hd:0<delta) (hchar:delta≤2130706433)
    (hSP:delta≤SP.d) (hSQ:delta≤SQ.d)
    (p q:FlagDegree) (hp:CumulativeLe (ordinaryFlag SP.P) p)
    (hq:CumulativeLe (ordinaryFlag SQ.P) q)
    (hz:flagMixed p q unitZFlag<2130706433)
    (hu:flagMixed p q unitYZFlag<2130706433):
    P.seeds.card≤max (MG t y r) (pairCost z delta p q t y r+leading z t y r):=by
  have hg' :Gates t y r (SZ.B-2*SZ.n0) (SZ.U-SZ.n0) (SZ.T-SZ.n0):=by
    simpa only [hZ.1,hZ.2.1,hZ.2.2.1,hZ.2.2.2.2] using hg
  have hc:=FRX P SZ SP SQ (by simpa only [hZ.2.2.1] using hFT)
    (by simpa only [hZ.2.2.2.1] using hk) hg' hcop delta hd hchar hSP hSQ
    ((CAB _ _ _ _ unitZFlag hp hq).trans_lt hz)
    ((CAB _ _ _ _ unitYZFlag hp hq).trans_lt hu)
  have hp' :=stageCost_le SZ SP SQ z hZ delta p q t y r hp hq
  exact hc.trans (max_le_max le_rfl (Nat.add_le_add hp' (fits_leading SZ z hZ t y r).le))

def nativeScalar (z:Degrees) (t y r:ℕ):ℕ:=
  z.d*SW.DIU t y r (parent t y r)+
    ∑ j:Fin 3,SW.coefficient t y r j*
      flagMixed (parent t y r) (direction j) z.flag

theorem GEE (S:Source F) (z:Degrees) (h:Fits S z) (t y r:ℕ):
    BDD S t y r (parent t y r)=nativeScalar z t y r:=by
  have hd:0<z.d:=by dsimp [Degrees.d];omega
  unfold BDD HFreeDir6813.numeratorDir nativeScalar
  simp only [fits_degree S z h,fits_flag S z h,Nat.mul_div_cancel_left z.d (by decide:0<3),
    Nat.div_self (by omega:0<3*z.d),Nat.mul_div_cancel 3 hd,mul_one,Finset.sum_add_distrib]
  refine congrArg₂ (fun a b:ℕ=>a+b) ?_ ?_
  · unfold SW.DIU
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    unfold SW.coefficient
    simp only [RCN326.w,RCN327.w]
    ring

theorem BVF
    (P:Packet x t y r) (S:Source P.F) (z:Degrees) (h:Fits S z)
    (hFT:z.T<wt AT P.F) (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)):
    P.seeds.card≤max (MG t y r) (nativeScalar z t y r/(3*z.d)+leading z t y r):=by
  have hg' :Gates t y r (S.B-2*S.n0) (S.U-S.n0) (S.T-S.n0):=by
    simpa only [h.1,h.2.1,h.2.2.1,h.2.2.2.2] using hg
  have hc:=FJO P S (by simpa only [h.2.2.2.1] using hk)
    (by simpa only [h.2.2.1] using hFT) hg'
  change P.seeds.card≤max (MG t y r)
    (BDD S t y r (parent t y r)/(3*S.d)+leadingPrice S t y r) at hc
  simpa only [GEE S z h t y r,fits_degree S z h,fits_leading S z h t y r] using hc

end
end HI
end MergedPart10
section MergedPart11
namespace BPZ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC BX DP
open DU ER EF
open HI



variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}





end
end BPZ
end MergedPart11
section MergedPart12
namespace BHP
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC BX DP
open DU ER EF
open HI
variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}





end
end BHP
end MergedPart12
section MergedPart13
namespace KY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN260 RCN294 RCN234 RCN156
open ER DU FF

theorem count_mono (t y r b u l capT capY capR capB capU capL:ℕ)
    (ht:t≤capT) (hy:y≤capY) (hr:r≤capR) (hb:b≤capB) (hu:u≤capU) (hl:l≤capL):
    GB.FU (pair t y r b u l)≤
      GB.FU (pair capT capY capR capB capU capL):=by
  unfold GB.FU
  apply Nat.div_le_div_right
  simp only [GB.KP,pair,DG.errors,
    DG.gap,DG.KO,DG.mixedCost,dot]
  gcongr

theorem gates_mono (t y r b u l capT capY capR capB capU capL:ℕ)
    (ht:t≤capT) (hy:y≤capY) (hr:r≤capR) (hb:b≤capB) (hu:u≤capU) (hl:l≤capL)
    (h:Gates capT capY capR capB capU capL):Gates t y r b u l:=by
  rcases h with ⟨hY,hR,hZ⟩
  unfold Gates pair DG.mixedCost at*
  constructor
  · apply lt_of_le_of_lt _ hY
    dsimp only
    gcongr
  constructor
  · apply lt_of_le_of_lt _ hR
    dsimp only
    gcongr
  · apply lt_of_le_of_lt _ hZ
    dsimp only
    gcongr

theorem DZN:Gates 4100 117 13 1024 7936 266432∧
    GB.FU (pair 4100 117 13 1024 7936 266432)<2000000000000000:=by
  unfold Gates
  decide+kernel

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x:I→K} {t y r:ℕ}

theorem ESM (p:Parameters) (P:Packet x t y r)
    (hb:p.B≤256) (hu:p.U≤512) (hl:p.L≤4096) (hs:p.s≤64):
    p.B+p.s*(r-1)≤1024∧p.U+p.s*(y-1)≤7936∧p.L+p.s*(t-1)≤266432:=by
  have hr:=P.rhigh
  have hy:=P.yhigh
  have ht:=P.thigh
  have hrr:p.s*(r-1)≤64*12:=Nat.mul_le_mul hs (by omega)
  have hyy:p.s*(y-1)≤64*116:=Nat.mul_le_mul hs (by omega)
  have htt:p.s*(t-1)≤64*4099:=Nat.mul_le_mul hs (by omega)
  omega

theorem helper_count (p:Parameters) (nodes:I ↪ K) (P:Packet (nodes:I→K) t y r)
    (hb:p.B≤256) (hu:p.U≤512) (hl:p.L≤4096) (hs:p.s≤64)
    (Q:MvPolynomial (Fin 4) K) (hQ:ProperHelper p P.F Q r y t nodes P.u0 P.u1):
    P.seeds.card<2000000000000000:=by
  obtain ⟨hr,hy,ht⟩:=ESM p P hb hu hl hs
  have hg:=gates_mono t y r _ _ _ 4100 117 13 1024 7936 266432
    P.thigh P.yhigh P.rhigh hr hy ht DZN.1
  exact (AJR.helper_count p nodes P Q hQ hg).trans_lt
    ((count_mono t y r _ _ _ 4100 117 13 1024 7936 266432
      P.thigh P.yhigh P.rhigh hr hy ht).trans_lt DZN.2)

end
end KY
end MergedPart13
section MergedPart14
namespace CN
set_option maxHeartbeats 2500000
set_option maxRecDepth 30000

theorem small (i:Fin 321):(profile i).B≤256∧(profile i).U≤512∧
    (profile i).L≤4096∧(profile i).s≤64∧(profile i).L+(profile i).s≤8192:=by
  fin_cases i<;>decide+kernel

end CN
end MergedPart14

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace ADE
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN095 RCN260
open HI BAL ER
open RL SW






















end ADE
end MergedPart0
section MergedPart1
namespace AXJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 30000
open RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ
open CB GF
open DU ER EF
open BD HI ADE
variable {K:Type} [Field K]







variable {I:Type} [CharP K 2130706433] {xmap:I→K} {t y r:ℕ}



end
end AXJ
end MergedPart1
section MergedPart2
namespace BGT
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
open RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ
open FF ZGL HI ADE
open AXJ CB BD
open DU ER EF
open DC FN BX DP


def active (p:Parameters) (m s b u e:ℕ):Prop:=
  e*b≤p.B∧e*u≤p.U∧e*s≤p.s∧p.k+1-e*m≤p.s-e*s
def box (p:Parameters) (m s b u lo:ℕ):DA.OwnerBox:=
  ⟨(p.k+1+m-1)/m,b,b,s,u,lo⟩





variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x:I→K} {t y r:ℕ}



end
end BGT
end MergedPart2
section MergedPart3
namespace CQG
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 50000
open FF HI ADE BGT

instance (p:Parameters) (m s b u e:ℕ):Decidable (active p m s b u e):=by
  unfold active
  infer_instance

def GoodPower (i:Fin 321) (m s b u lo:ℕ):Prop:=
  let p:=CN.profile i
  (DA.Impossible (ZGL.caps p) (box p m s b u lo)∧
    0<CN.kernel i)∨
  ZGL.strongCount p (box p m s b u lo)<
    CN.kernel i

instance (i:Fin 321) (m s b u lo:ℕ):Decidable (GoodPower i m s b u lo):=by
  unfold GoodPower DA.Impossible
  infer_instance











end CQG
end MergedPart3

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace QN
set_option autoImplicit false
set_option maxHeartbeats 1200000
open RCN095
















end QN
end MergedPart0
section MergedPart1
namespace BPW
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open scoped BigOperators
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF LK
open SW HI





variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}













end
end BPW
end MergedPart1

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
section MergedPart0
namespace AZY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 30000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF
open HI ADE AXJ
variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}







end
end AZY
end MergedPart0
section MergedPart1
namespace LV
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF
open HI FF ZGL DR

def flag (B U T S:ℕ):FlagDegree:=
  let M:=max B (U+S)
  ⟨max M (T+S)-M,M-B,B⟩
def ownerFlag (a:Box):=flag a.bhi a.uhi a.thi a.shi
def AFD (a:Box):FlagDegree:=
  let p:=ownerFlag a
  ⟨p.zOnly,p.yz,p.all-2⟩
def ownerZ (a:Box) (m:ℕ):Degrees:=
  ⟨a.bhi,max a.bhi a.uhi,max (max a.bhi a.uhi) a.thi,m-1,a.slo⟩
def point {K:Type} [Field K] (J:Poly (K:=K)):Point:=
  ⟨order J,slope J,middle J,total J⟩
def powerBox (p:Parameters) (a:Box) (m:ℕ):DA.OwnerBox:=
  ⟨(p.k+1+m-1)/m,a.blo,a.bhi,a.slo,a.ulo,a.tlo⟩
def cofactorFlag (p:Parameters) (a:Box) (e:ℕ):=
  flag (p.B-e*a.blo) (p.U-e*a.ulo) (p.L-e*a.tlo) (p.s-e*a.slo)
def active (p:Parameters) (a:Box) (m e:ℕ):Prop:=
  e*a.blo≤p.B∧e*a.ulo≤p.U∧e*a.tlo≤p.L∧e*a.slo≤p.s∧p.k+1-e*m≤p.s-e*a.slo
def GoodPower (i:Fin 321) (a:Box) (m:ℕ):Prop:=
  let p:=CN.profile i
  (DA.Impossible (caps p) (powerBox p a m)∧
    0<CN.kernel i)∨
  strongCount p (powerBox p a m)<CN.kernel i

variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}

theorem FBA (J:Poly (K:=K)) (B U T S:ℕ)
    (hb:slope J≤B) (hu:middle J≤U) (ht:total J≤T) (hs:order J≤S):
    CumulativeLe (ordinaryFlag J) (flag B U T S):=by
  have h:=RJ J
  dsimp only [flag]
  change _≤B∧_≤max B (U+S)-B+B∧
    _≤max (max B (U+S)) (T+S)-max B (U+S)+(max B (U+S)-B)+B
  omega

theorem _Q23 (J:Poly (K:=K)) (a:Box) (h:Contains a (point J)):
    CumulativeLe (ordinaryFlag J) (ownerFlag a):=by
  exact FBA J a.bhi a.uhi a.thi a.shi h.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2 h.2.1

theorem DEA (J:Poly (K:=K)) (a:Box) (h:Contains a (point J))
    (hs:2≤order J):CumulativeLe (ordinaryFlag (pderiv 1 J)) (AFD a):=by
  have hdB:=LL.AWV J slopeWeights
  have hdU:=LL.AWV J HA
  have hdT:=LL.AWV J totalWeights
  have hdS:=LL.pderiv_order J
  change slope (pderiv 1 J)≤slope J-2 at hdB
  change middle (pderiv 1 J)≤middle J-1 at hdU
  change total (pderiv 1 J)≤total J-1 at hdT
  change order (pderiv 1 J)≤order J-1 at hdS
  have hn:=_Q15 J
  have hd:=RJ (pderiv 1 J)
  dsimp only [Contains,point] at h
  dsimp only [CumulativeLe,AFD,ownerFlag,flag]
  omega

theorem owner_source (P:Packet x t y r) [Fact (Irreducible P.F)]
    (J:Poly (K:=K)) (a:Box) (m:ℕ) (hm:0<m)
    (h:Contains a (point J)) (hms:m≤a.slo) (h2:2*a.slo≤a.bhi)
    (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m):
    ∃S:Source P.F,Fits S (ownerZ a m):=by
  have hshape: ∀e∈J.support,2*e 1+e 3≤a.bhi∧
      e 1+e 2+e 3≤max a.bhi a.uhi∧e 1+e 2+e 3+e 4≤max (max a.bhi a.uhi) a.thi:=by
    intro e he
    have h1:=(le_weightedTotalDegree slopeWeights he).trans h.2.2.2.1
    have h2:=(le_weightedTotalDegree HA he).trans h.2.2.2.2.2.1
    have h3:=(le_weightedTotalDegree totalWeights he).trans h.2.2.2.2.2.2.2
    simp [JW,slopeWeights,HA,totalWeights] at h1 h2 h3
    exact ⟨by simpa only [Nat.mul_comm] using h1,h2.trans (le_max_right _ _),h3.trans (le_max_right _ _)⟩
  have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
  obtain ⟨S,_,hp⟩:=ON.DDZ P.F P.rdegree hchar J m a.shi
    a.bhi (max a.bhi a.uhi) (max (max a.bhi a.uhi) a.thi) (m-1) a.slo
    (by omega) (by omega) h.1 h.2.1 h2 (le_max_left _ _) (le_max_left _ _) hshape hroot
  exact ⟨S,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2⟩

theorem GBB (P:Packet x t y r) [Fact (Irreducible P.F)]
    (SZ:Source P.F) (z:Degrees) (hZ:Fits SZ z)
    (hZFT:z.T<wt AT P.F) (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (hFT:1700<wt AT P.F)
    (J:Poly (K:=K)) (hJ:Irreducible J) (a:Box) (m cap:ℕ)
    (h:Contains a (point J)) (hm:2≤m) (hms:m≤order J)
    (hsmall:a.thi≤1700) (hsChar:a.shi<2130706433)
    (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hcg:flagMixed (ownerFlag a) (AFD a) unitZFlag<2130706433∧
      flagMixed (ownerFlag a) (AFD a) unitYZFlag<2130706433)
    (hfit:pairCost z (m-1) (ownerFlag a) (AFD a) t y r+leading z t y r≤cap):
    P.seeds.card≤max (MG t y r) cap:=by
  have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
  obtain ⟨SJ,SQ,hSJ,hSQ,hcop,hJd,hQd,_⟩:=LL.AWG
    P.F hFT P.rdegree hchar J hJ (h.2.2.2.2.2.2.2.trans hsmall)
    (by rw [ABW];change 0<order J;omega)
    (by rw [ABW];exact h.2.1.trans_lt hsChar) m hm hroot
  have hp:=_Q23 J a h
  have hq:=DEA J a h (by omega)
  rw [←hSJ] at hp
  rw [←hSQ] at hq
  have hms' :m<2130706433:=hms.trans_lt (h.2.1.trans_lt hsChar)
  exact (AHM P SZ SJ SQ z hZ hZFT hk hg hcop (m-1) (by omega)
    (by omega) (by omega) hQd _ _ hp hq hcg.1 hcg.2).trans (max_le_max le_rfl hfit)

theorem GHJ [Fintype I] (nodes:I ↪ K) (hI:Fintype.card I=262144)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (SZ:Source P.F) (z:Degrees) (hZ:Fits SZ z)
    (hZFT:z.T<wt AT P.F) (hk:z.k<2130706433)
    (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
    (i:Fin 321) (hFT:(CN.profile i).L<wt AT P.F)
    (J:Poly (K:=K)) (hJ:Irreducible J) (a:Box) (m cap:ℕ)
    (h:Contains a (point J)) (hm:0<m)
    (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne:(asS J).map (carrierMap P.F)≠0)
    (hJF:a.thi<wt AT P.F) (hcap:2000000000000000≤cap)
    (hgood:GoodPower i a m)
    (hchecks: ∀e,e<(powerBox (CN.profile i) a m).q→
      active (CN.profile i) a m e→
      flagMixed (ownerFlag a) (cofactorFlag (CN.profile i) a e) unitZFlag<2130706433∧
      flagMixed (ownerFlag a) (cofactorFlag (CN.profile i) a e) unitYZFlag<2130706433∧
      pairCost z (min m ((CN.profile i).k+1-e*m))
        (ownerFlag a) (cofactorFlag (CN.profile i) a e) t y r+leading z t y r≤cap):
    P.seeds.card≤max (MG t y r) cap:=by
  let p:=CN.profile i
  have hp:Shape p:=CN.shape i
  have small:p.B≤256∧p.U≤512∧p.L≤4096∧p.s≤64∧p.L+p.s≤8192:=CN.small i
  have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
  have hcovers:DA.Covers (powerBox p a m) J:=
    ⟨h.2.2.1,h.2.2.2.1,h.1,h.2.2.2.2.1,h.2.2.2.2.2.2.1⟩
  rcases BHD p hp (CN.kernel i)
    (CN.dimension i) nodes P.u0 P.u1 hI P.F hFT P.rdegree hchar
    r y t (by have:=P.rlow;omega) (by have:=P.ylow;have:=P.rlow;omega)
    (by have:=P.yt;have:=P.ylow;have:=P.rlow;omega)
    ⟨P.r_weight,P.y_weight,P.total_weight⟩ J hJ a.thi h.2.2.2.2.2.2.2 hJF m hm hroot hJne
    (powerBox p a m) rfl hcovers hgood
      with ⟨Q,hQ⟩ | ⟨e,he,SJ,SQ,hSJ,hcop,hdelta,hSP,hRet,hT,hU,hB,hS⟩
  · exact ((KY.helper_count p nodes P small.1 small.2.1
      small.2.2.1 small.2.2.2.1 Q hQ).le.trans hcap).trans (le_max_right _ _)
  have hb:=Nat.mul_le_mul_left e h.2.2.1
  have hu:=Nat.mul_le_mul_left e h.2.2.2.2.1
  have ht:=Nat.mul_le_mul_left e h.2.2.2.2.2.2.1
  have hs:=Nat.mul_le_mul_left e h.1
  have horder:SQ.d≤order SQ.P:=by
    have hh:=SQ.hdn.trans SQ.hn
    simpa only [Source.d,ABW,order] using hh
  have ha:active p a m e:=by unfold active;dsimp only [point] at hb hu ht hs;omega
  obtain ⟨hcgZ,hcgU,hfit⟩:=hchecks e he ha
  have hq:CumulativeLe (ordinaryFlag SQ.P) (cofactorFlag p a e):=
    FBA SQ.P _ _ _ _ (by dsimp only [point] at hb;omega)
      (by dsimp only [point] at hu;omega) (by dsimp only [point] at ht;omega)
      (by dsimp only [point] at hs;omega)
  have hj:=_Q23 J a h
  rw [←hSJ] at hj
  have hdchar:min m (p.k+1-e*m)≤2130706433:=by
    have h1:=hp.retention
    have h2:=hp.degree
    have h3:=hp.characteristic
    have h4:=min_le_right m (p.k+1-e*m)
    omega
  exact (AHM P SZ SJ SQ z hZ hZFT hk hg hcop _ hdelta hdchar hSP
    ((min_le_right _ _).trans hRet) _ _ hj hq hcgZ hcgU).trans (max_le_max le_rfl hfit)

end
end LV
end MergedPart1
section MergedPart2
namespace SN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC BX DP BD
open DU ER EF
open FF HI BPZ
open ADE CQG

inductive Choice where
  | native
  | derivative (ownerZ:Bool)
  | auxiliary (ownerZ:Bool) (source:Fin 321)
  deriving DecidableEq



def Common (z:Degrees) (low t y r:ℕ):Prop:=
  z.T<low∧z.k<2130706433∧Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0)
instance (z:Degrees) (low t y r:ℕ):Decidable (Common z low t y r):=by
  unfold Common Gates
  infer_instance



variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {x:I→K} {t y r:ℕ}





end
end SN
end MergedPart2
section MergedPart3
namespace BH
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 50000
open DR LV HI FF
open SN (Choice Common)
open RCN095 RCN135 RCN136 RCN156 RCN234 CB
open DC BD
open DU EF
open CW DJ BX DP

def chosenZ (useOwner:Bool) (fixed:Degrees) (a:Box) (m:ℕ):=
  if useOwner then ownerZ a m else fixed

instance (p:Parameters) (a:Box) (m e:ℕ):Decidable (active p a m e):=by
  unfold active;infer_instance
instance (i:Fin 321) (a:Box) (m:ℕ):Decidable (GoodPower i a m):=by
  unfold GoodPower DA.Impossible;infer_instance

def PairChecks (z:Degrees) (delta:ℕ) (p q:FlagDegree) (t y r cap:ℕ):Prop:=
  flagMixed p q unitZFlag<2130706433∧flagMixed p q unitYZFlag<2130706433∧
    pairCost z delta p q t y r+leading z t y r≤cap
instance (z:Degrees) (delta:ℕ) (p q:FlagDegree) (t y r cap:ℕ):
    Decidable (PairChecks z delta p q t y r cap):=by unfold PairChecks;infer_instance

def checkExit (p:Parameters) (a:Box) (z:Degrees) (m t y r cap e:ℕ):Bool:=
  if active p a m e then decide (PairChecks z (min m (p.k+1-e*m))
    (ownerFlag a) (cofactorFlag p a e) t y r cap) else true
def checkExits (p:Parameters) (a:Box) (z:Degrees) (m t y r cap:ℕ):Bool:=
  (List.range (powerBox p a m).q).all (checkExit p a z m t y r cap)

def checkChoice (c:Choice) (fixed:Degrees) (a:Box) (m low t y r cap:ℕ):Bool:=
  match c with
  | .native=>decide (Common (ownerZ a m) low t y r∧
      nativeScalar (ownerZ a m) t y r/(3*(ownerZ a m).d)+leading (ownerZ a m) t y r≤cap)
  | .derivative useOwner=>
      let z:=chosenZ useOwner fixed a m
      decide (2≤m∧Common z low t y r∧PairChecks z (m-1) (ownerFlag a) (AFD a) t y r cap)
  | .auxiliary useOwner i=>
      let z:=chosenZ useOwner fixed a m
      decide (Common z low t y r∧(CN.profile i).L<low) &&
        decide (GoodPower i a m) && checkExits (CN.profile i) a z m t y r cap

def check (c:Choice) (fixed:Degrees) (a:Box) (m low t y r cap:ℕ):Bool:=
  decide (0<m∧m≤a.slo∧2*a.slo≤a.bhi∧a.thi≤1700∧a.thi<low∧a.shi<2130706433) &&
    checkChoice c fixed a m low t y r cap

theorem exits_spec (p:Parameters) (a:Box) (z:Degrees) (m t y r cap:ℕ)
    (hc:checkExits p a z m t y r cap=true):
    ∀e,e<(powerBox p a m).q→active p a m e→
      PairChecks z (min m (p.k+1-e*m)) (ownerFlag a) (cofactorFlag p a e) t y r cap:=by
  intro e he ha
  have hh:=List.all_eq_true.mp hc e (List.mem_range.mpr he)
  simpa only [checkExit,if_pos ha,decide_eq_true_eq] using hh

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r:ℕ}

theorem BLQ (nodes:I ↪ K) (hI:Fintype.card I=262144)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (fixedS:Source P.F) (fixed:Degrees) (hFixed:Fits fixedS fixed)
    (c:Choice) (a:Box) (m low cap:ℕ)
    (hloF:low≤wt AT P.F) (hlo:1700<low) (hcap:2000000000000000≤cap)
    (J:Poly (K:=K)) (hJ:Irreducible J) (h:Contains a (point J))
    (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hJne:(asS J).map (carrierMap P.F)≠0)
    (hc:check c fixed a m low t y r cap=true):
    P.seeds.card≤max (MG t y r) cap:=by
  simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc
  obtain ⟨hm,hms,h2,hsmall,hJF,hsChar⟩:=hc.1
  have hsrc (useOwner:Bool): ∃S:Source P.F,Fits S (chosenZ useOwner fixed a m):=by
    cases useOwner
    · exact ⟨fixedS,hFixed⟩
    · exact owner_source P J a m hm h hms h2 hroot
  cases c with
  | native=>
    have hh:=of_decide_eq_true hc.2
    obtain ⟨S,hS⟩:=owner_source P J a m hm h hms h2 hroot
    exact (BVF P S _ hS (hh.1.1.trans_le hloF) hh.1.2.1 hh.1.2.2).trans
      (max_le_max le_rfl hh.2)
  | derivative useOwner=>
    have hh:=of_decide_eq_true hc.2
    obtain ⟨S,hS⟩:=hsrc useOwner
    exact GBB P S _ hS (hh.2.1.1.trans_le hloF) hh.2.1.2.1 hh.2.1.2.2
      (hlo.trans_le hloF) J hJ a m cap h hh.1 (hms.trans h.1) hsmall hsChar hroot
      ⟨hh.2.2.1,hh.2.2.2.1⟩ hh.2.2.2.2
  | auxiliary useOwner i=>
    have hh:=hc.2
    simp only [checkChoice,Bool.and_eq_true,decide_eq_true_eq] at hh
    obtain ⟨S,hS⟩:=hsrc useOwner
    exact GHJ nodes hI P S _ hS (hh.1.1.1.1.trans_le hloF)
      hh.1.1.1.2.1 hh.1.1.1.2.2 i (hh.1.1.2.trans_le hloF) J hJ a m cap h hm hroot hJne
      (hJF.trans_le hloF) hcap hh.1.2 (exits_spec _ _ _ _ _ _ _ _ hh.2)

end
end BH
end MergedPart3
section MergedPart4
namespace CNI
noncomputable section
set_option autoImplicit false
open DR LV HI
open RCN095 RCN135 RCN136 RCN156 RCN234 CB
open DC BD
open DU EF
open CW DJ BX DP



variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r:ℕ}


end
end CNI
end MergedPart4
section MergedPart5
namespace FOJ
open DR CNI SN HI
set_option autoImplicit false











end FOJ
end MergedPart5
section MergedPart6
namespace CQJ
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF LK
open HI
open SN (Common)

structure Point where
  b:ℕ
  u:ℕ
  t:ℕ
  deriving DecidableEq
structure Box where
  blo:ℕ
  bhi:ℕ
  ulo:ℕ
  uhi:ℕ
  tlo:ℕ
  thi:ℕ
  deriving DecidableEq


def Empty (a:Box):=a.bhi<a.blo∨a.uhi<a.ulo∨a.thi<a.tlo
instance (a:Box):Decidable (Empty a):=by unfold Empty;infer_instance




















structure Choice where
  which:Fin 3
  derivative:Bool
  deriving DecidableEq




variable {K I:Type} [Field K] [CharP K 2130706433] {x:I→K} {t y r:ℕ}

















end
end CQJ
end MergedPart6
section MergedPart7
namespace FHO
open CQJ HI
set_option autoImplicit false











end FHO
end MergedPart7
section MergedPart8
namespace AYU
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 40000
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GZ LK
open ME ON
open DR LV CNI HI
open AIA BMA



def LinearChecks (B U L t y r cap:ℕ):Prop:=
  Gates t y r (B-2) (U-1) (L-1)∧
  flagMixed ⟨t-y,y-r,r⟩ (firstFlag (2*B-3) (2*U-2) (2*L-2)) unitZFlag<2130706433∧
  linearPrice (firstFlag (2*B-3) (2*U-2) (2*L-2))
    (delayFlag (2*B-3) (2*U-2) (2*L-2)) t y r (B-2) (U-1) (L-1)≤cap
instance (B U L t y r cap:ℕ):Decidable (LinearChecks B U L t y r cap):=by
  unfold LinearChecks Gates;infer_instance

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I] {t y r:ℕ}



end
end AYU
end MergedPart8

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ALQ
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K:Type*} [Field K]

/-- Disjoint roots at zero and at nonzero nodes determine a short polynomial. -/
theorem EBA (f:Polynomial K) (points:Finset K)
    (orders:K→ℕ) (b D M:ℕ)
    (hzero:(0:K)∉points)
    (hcoeff: ∀j<b,f.coeff j=0)
    (hroots: ∀x∈points,(Polynomial.X-Polynomial.C x)^orders x∣f)
    (hmass:M≤∑ x∈points,orders x)
    (hdegree:f.natDegree<D) (hfit:D≤b+M):f=0:=by
  classical
  by_contra hf
  have hb:b≤f.rootMultiplicity 0:=by
    apply (Polynomial.le_rootMultiplicity_iff hf).mpr
    simpa using (Polynomial.X_pow_dvd_iff.mpr hcoeff:Polynomial.X^b∣f)
  have hn:(∑ x∈points,orders x)≤∑ x∈points,f.rootMultiplicity x:=
    Finset.sum_le_sum (fun x hx=>(Polynomial.le_rootMultiplicity_iff hf).mpr (hroots x hx))
  have hall:=RCN355._Q14 f (insert 0 points)
  rw [Finset.sum_insert hzero] at hall
  omega

variable {σ:Type*} [DecidableEq σ]

def coeffPoly (e:σ→₀ ℕ) (P:Polynomial (MvPolynomial σ K)):Polynomial K:=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.mapRange
    (fun c:MvPolynomial σ K=>c.coeff e) (by simp) P.toFinsupp.coeff))

@[simp] theorem FEH (e:σ→₀ ℕ) (P:Polynomial (MvPolynomial σ K)) (j:ℕ):
    (coeffPoly e P).coeff j=(P.coeff j).coeff e:=rfl

theorem FGW (e:σ→₀ ℕ) (f:Polynomial K)
    (P:Polynomial (MvPolynomial σ K)):
    coeffPoly e (f.map MvPolynomial.C*P)=f*coeffPoly e P:=by
  ext j
  simp only [FEH,Polynomial.coeff_mul,Polynomial.coeff_map,
    MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul]

theorem GHW (e:σ→₀ ℕ) (P:Polynomial (MvPolynomial σ K))
    (x:K) (n:ℕ)
    (h:(Polynomial.X-Polynomial.C (MvPolynomial.C x))^n ∣ P):
    (Polynomial.X-Polynomial.C x)^n ∣ coeffPoly e P:=by
  obtain ⟨Q,hQ⟩:=h
  refine ⟨coeffPoly e Q,?_⟩
  have he:=FGW e ((Polynomial.X-Polynomial.C x)^n) Q
  simpa only [Polynomial.map_pow,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_C,←hQ]
    using he

/-- Once enough common jets are fixed, the remaining low coefficients determine
    a polynomial with a weighted bound on its other variables. -/
theorem CSN
    (P:Polynomial (MvPolynomial σ K)) (weight:(σ→₀ ℕ)→ℕ)
    (points:Finset K) (orders:K→ℕ) (D d M:ℕ)
    (hzero:(0:K)∉points)
    (hcode: ∀e j,(P.coeff j).coeff e≠0→j+weight e<D)
    (hlow: ∀e j,j+weight e<d→(P.coeff j).coeff e=0)
    (hroots: ∀x∈points,
      (Polynomial.X-Polynomial.C (MvPolynomial.C x))^orders x∣P)
    (hmass:M≤∑ x∈points,orders x) (hfit:D≤d+M):P=0:=by
  have he (e:σ→₀ ℕ):coeffPoly e P=0:=by
    by_contra hf
    have hc:(coeffPoly e P).coeff (coeffPoly e P).natDegree≠0:=
      Polynomial.leadingCoeff_ne_zero.mpr hf
    have hd:=hcode e _ hc
    have hdeg:(coeffPoly e P).natDegree<D-weight e:=by omega
    have hpref: ∀j<d-weight e,(coeffPoly e P).coeff j=0:=by
      intro j hj
      exact hlow e j (by omega)
    have hroots' :=fun x hx=>GHW e P x (orders x) (hroots x hx)
    exact hf (EBA (coeffPoly e P) points orders
      (d-weight e) (D-weight e) M hzero hpref hroots' hmass hdeg (by omega))
  ext j e
  simpa only [FEH,Polynomial.coeff_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using
    congrArg (fun f:Polynomial K=>f.coeff j) (he e)

/-- Convert the derivative's zero mass into contact orders left for a quotient. -/
theorem DZT {ι:Type*} (s:Finset ι) (mu:ι→ℕ)
    (q m n A W G nu:ℕ) (hA:A=W+G) (hcard:s.card=A)
    (hnu:m*W≤nu) (hloss:(∑ i∈s,(mu i-m))≤nu-m*W):
    n*A≤(∑ i∈s,(n-q*mu i))+q*nu+q*m*G:=by
  have hmu:(∑ i∈s,mu i)≤A*m+∑ i∈s,(mu i-m):=by
    calc
      _≤∑ i∈s,(m+(mu i-m)):=Finset.sum_le_sum (fun i _=>by omega)
      _=_:=by simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,hcard]
  have hsub:=Nat.sub_add_cancel hnu
  have hmul:A*m=W*m+G*m:=by rw [hA];ring
  have hmu' :(∑ i∈s,mu i)≤nu+m*G:=by nlinarith
  have hp:n*A≤(∑ i∈s,(n-q*mu i))+q*(∑ i∈s,mu i):=by
    calc
      _=∑ i∈s,n:=by simp [hcard,Nat.mul_comm]
      _≤∑ i∈s,((n-q*mu i)+q*mu i):=Finset.sum_le_sum (fun i _=>by omega)
      _=_:=by simp only [Finset.sum_add_distrib,Finset.mul_sum]
  have hh:=Nat.mul_le_mul_left q hmu'
  nlinarith

section ProductJets
variable {R:Type*} [CommRing R] [IsDomain R]

theorem EXH (J:Polynomial R) (hJ:J≠0) (q:ℕ):
    (J^q).rootMultiplicity 0=q*J.rootMultiplicity 0:=by
  induction q with
  | zero=>simp
  | succ q ih=>
    rw [pow_succ,Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hJ) hJ),ih]
    simp only [Nat.succ_mul]

theorem quotient_jet (J Q:Polynomial R) (hJ:J≠0) (q n:ℕ)
    (h:Polynomial.X^n ∣ J^q*Q):
    Polynomial.X^(n-q*J.rootMultiplicity 0)∣Q:=by
  by_cases hQ:Q=0
  · simp [hQ]
  have hn:n≤(J^q*Q).rootMultiplicity 0:=by
    apply (Polynomial.le_rootMultiplicity_iff (mul_ne_zero (pow_ne_zero _ hJ) hQ)).mpr
    simpa using h
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ hJ) hQ),
    EXH J hJ q] at hn
  have hd:n-q*J.rootMultiplicity 0≤Q.rootMultiplicity 0:=by omega
  have hh:=(Polynomial.le_rootMultiplicity_iff hQ).mp hd
  simpa using hh
end ProductJets

end
end ALQ

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ASN
open scoped BigOperators
open DX HZ IM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {K I:Type*} [Field K]

theorem DIJ (nodes:I ↪ K) (u0 u1:I→K)
    (J:Poly (K:=K)) (f:Polynomial K) (z:K) (A:Finset I)
    (mu:I→ℕ) (m D:ℕ)
    (hag: ∀i∈A,f.eval (nodes i)=u0 i+u1 i*z)
    (hmu: ∀i∈A,MvPolynomial.X 0^mu i ∣
      substitute (K:=K) (localize (nodes i) (u0 i) (u1 i) J))
    (hne:HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0)
    (hdegree:(HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤D):
    (∑ i∈A,(mu i-m))≤D:=by
  classical
  let R:=HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)
  have hroot (i:I) (hi:i∈A):(mu i-m)≤R.rootMultiplicity (nodes i):=by
    apply (Polynomial.le_rootMultiplicity_iff hne).mpr
    by_cases hm:m≤mu i
    · apply HH.root_contact ((MvPolynomial.pderiv 1)^[m] J) f (nodes i) (u0 i) (u1 i) z (mu i-m) (hag i hi)
      apply KL.ADR (nodes i) (u0 i) (u1 i) J (mu i-m) m
      simpa only [Nat.sub_add_cancel hm] using hmu i hi
    · simp only [Nat.sub_eq_zero_of_le (Nat.le_of_lt (Nat.lt_of_not_ge hm)),pow_zero]
      exact one_dvd _
  have hsum:(∑ i∈A,(mu i-m))≤∑ i∈A,R.rootMultiplicity (nodes i):=
    Finset.sum_le_sum (fun i hi=>hroot i hi)
  have hmass:(∑ x∈A.map nodes,R.rootMultiplicity x)≤R.natDegree:=
    RCN355._Q14 R (A.map nodes)
  rw [Finset.sum_map] at hmass
  exact hsum.trans (hmass.trans hdegree)

end
end ASN

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AMR
open MvPolynomial DX HZ IM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
variable {K:Type*} [Field K]

theorem BZR (P:Poly (K:=K)) (n:ℕ):
    MvPolynomial.X 0^n∣P ↔ Polynomial.X^n∣(MvPolynomial.finSuccEquiv K 4) P:=by
  constructor
  · intro h
    have hd:=map_dvd (MvPolynomial.finSuccEquiv K 4).toRingHom h
    change (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0^n)∣(MvPolynomial.finSuccEquiv K 4) P at hd
    simpa only [map_pow,MvPolynomial.finSuccEquiv_X_zero] using hd
  · rintro ⟨R,hR⟩
    refine ⟨(MvPolynomial.finSuccEquiv K 4).symm R,?_⟩
    apply (MvPolynomial.finSuccEquiv K 4).injective
    rw [map_mul,map_pow,MvPolynomial.finSuccEquiv_X_zero,AlgEquiv.apply_symm_apply]
    exact hR

def shift (x:K):Poly (K:=K)→ₐ[K] Poly (K:=K):=
  MvPolynomial.aeval ![MvPolynomial.C x+MvPolynomial.X 0,MvPolynomial.X 1,
    MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4]

theorem GEN (Q:Poly (K:=K)) (hA:Q.degreeOf 2=0) (x u0 u1:K):
    substitute (K:=K) (localize x u0 u1 Q)=shift x Q:=by
  classical
  have hnot:(2:Fin 5)∉Q.vars:=by
    simpa only [MvPolynomial.mem_vars_iff_degreeOf_ne_zero,not_not] using hA
  apply MvPolynomial.hom_congr_vars (f₁:=((substitute (K:=K)).comp (localize x u0 u1)).toRingHom)
    (f₂:=(shift x).toRingHom) ?_ ?_ rfl
  · ext c
    simp
  · intro j hj _
    have hj2:j≠2:=by intro he;subst j;exact hnot hj
    fin_cases j<;>simp_all [shift,substitute,localize]

theorem shift_outer (x:K) (Q:Poly (K:=K)):
    (MvPolynomial.finSuccEquiv K 4) (shift x Q)=
      Polynomial.taylor (MvPolynomial.C x) ((MvPolynomial.finSuccEquiv K 4) Q):=by
  let left:Poly (K:=K)→ₐ[K] Polynomial (MvPolynomial (Fin 4) K):=
    (MvPolynomial.finSuccEquiv K 4).toAlgHom.comp (shift x)
  let right:Poly (K:=K)→ₐ[K] Polynomial (MvPolynomial (Fin 4) K):=
    ((Polynomial.taylorAlgHom (MvPolynomial.C x)).restrictScalars K).comp
      (MvPolynomial.finSuccEquiv K 4).toAlgHom
  have hC:(MvPolynomial.finSuccEquiv K 4) (MvPolynomial.C x)=
      Polynomial.C (MvPolynomial.C x):=by simp [MvPolynomial.finSuccEquiv_apply]
  have hs (j:Fin 4):shift x (MvPolynomial.X j.succ)=MvPolynomial.X j.succ:=by
    fin_cases j<;>simp [shift]
  have he:left=right:=by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.cases ?_ (fun j=> ?_) j
    · simp [left,right,shift,hC,MvPolynomial.finSuccEquiv_X_zero,add_comm]
    · simp [left,right,hs,MvPolynomial.finSuccEquiv_X_succ]
  exact DFunLike.congr_fun he Q

theorem GFN (Q:Poly (K:=K)) (hA:Q.degreeOf 2=0)
    (x u0 u1:K) (n:ℕ)
    (h:MvPolynomial.X 0^n∣substitute (K:=K) (localize x u0 u1 Q)):
    (Polynomial.X-Polynomial.C (MvPolynomial.C x))^n∣(MvPolynomial.finSuccEquiv K 4) Q:=by
  rw [GEN Q hA] at h
  have hh:=map_dvd (MvPolynomial.finSuccEquiv K 4).toRingHom h
  change (MvPolynomial.finSuccEquiv K 4) (MvPolynomial.X 0^n)∣
    (MvPolynomial.finSuccEquiv K 4) (shift x Q) at hh
  rw [map_pow,MvPolynomial.finSuccEquiv_X_zero,shift_outer] at hh
  obtain ⟨R,hR⟩:=hh
  refine ⟨(Polynomial.taylorEquiv (MvPolynomial.C x)).symm R,?_⟩
  apply Polynomial.taylor_injective (MvPolynomial.C x)
  rw [Polynomial.taylor_mul,Polynomial.taylor_pow]
  have hx:Polynomial.taylor (MvPolynomial.C x:MvPolynomial (Fin 4) K)
      (Polynomial.X-Polynomial.C (MvPolynomial.C x))=Polynomial.X:=by simp
  rw [hx]
  change Polynomial.taylor (MvPolynomial.C x) ((MvPolynomial.finSuccEquiv K 4) Q)=
    Polynomial.X^n*((Polynomial.taylorEquiv (MvPolynomial.C x))
      ((Polynomial.taylorEquiv (MvPolynomial.C x)).symm R))
  rw [AlgEquiv.apply_symm_apply]
  exact hR
end
end AMR

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace NS
open scoped BigOperators
open MvPolynomial DX HZ IM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type*} [Field K]

def outer (x u0 u1:K) (J:Poly (K:=K)):=
  (MvPolynomial.finSuccEquiv K 4) (substitute (K:=K) (localize x u0 u1 J))

theorem BXW (J:Poly (K:=K)) (f:Polynomial K)
    (x u0 u1 z:K) (m:ℕ) (hag:f.eval x=u0+u1*z)
    (hne:HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0):
    substitute (K:=K) (localize x u0 u1 J)≠0:=by
  intro hz
  let R:=HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)
  have hd:MvPolynomial.X 0^(R.natDegree+1+m) ∣
      substitute (K:=K) (localize x u0 u1 J):=by simp [hz]
  have hh:=KL.ADR x u0 u1 J
    (R.natDegree+1) m hd
  have hr:=HH.root_contact ((MvPolynomial.pderiv 1)^[m] J)
    f x u0 u1 z (R.natDegree+1) hag hh
  have hle:=Polynomial.natDegree_le_of_dvd hr hne
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,mul_one] at hle
  change R.natDegree+1≤R.natDegree at hle
  omega

/-- Projection injectivity for a quotient that has no value variable left. -/
theorem DNO
    (nodes:I ↪ K) (u0 u1:I→K) (s:Finset I)
    (J P Q:Poly (K:=K)) (q m n A W G nu D:ℕ)
    (heq:P=J^q*Q) (hfree:Q.degreeOf 2=0)
    (hjet: ∀i∈s,MvPolynomial.X 0^n∣substitute (K:=K) (localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (z:K)
    (hag: ∀i∈s,f.eval (nodes i)=u0 i+u1 i*z)
    (hne:HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0)
    (hdegree:(HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤nu-m*W)
    (hnu:m*W≤nu) (hA:A=W+G) (hcard:s.card=A) (hD:D+q*nu=n*A)
    (hnodes: ∀i∈s,nodes i≠0)
    (weight:(Fin 4→₀ ℕ)→ℕ)
    (hcode: ∀e j,(((MvPolynomial.finSuccEquiv K 4) Q).coeff j).coeff e≠0→j+weight e<D)
    (hlow: ∀e j,j+weight e<q*m*G→(((MvPolynomial.finSuccEquiv K 4) Q).coeff j).coeff e=0):Q=0:=by
  classical
  let mu (i:I):=(outer (nodes i) (u0 i) (u1 i) J).rootMultiplicity 0
  let ord (i:I):=n-q*mu i
  have hmu (i:I):MvPolynomial.X 0^mu i∣
      substitute (K:=K) (localize (nodes i) (u0 i) (u1 i) J):=by
    apply (AMR.BZR _ _).mpr
    simpa only [mu,outer,map_zero,sub_zero] using
      (outer (nodes i) (u0 i) (u1 i) J).pow_rootMultiplicity_dvd 0
  have hloss:=ASN.DIJ nodes u0 u1 J f z s
    mu m (nu-m*W) hag (fun i _=>hmu i) hne hdegree
  have hmass:=ALQ.DZT s mu q m n A W G nu hA hcard hnu hloss
  have hroot (i:I) (hi:i∈s):
      (Polynomial.X-Polynomial.C (MvPolynomial.C (nodes i)))^ord i∣(MvPolynomial.finSuccEquiv K 4) Q:=by
    have hJ:outer (nodes i) (u0 i) (u1 i) J≠0:=by
      intro hz
      apply BXW J f (nodes i) (u0 i) (u1 i) z m (hag i hi) hne
      exact (MvPolynomial.finSuccEquiv K 4).injective (by simpa only [outer,map_zero] using hz)
    have hp:=(AMR.BZR _ _).mp (hjet i hi)
    have he:outer (nodes i) (u0 i) (u1 i) P=
        (outer (nodes i) (u0 i) (u1 i) J)^q*outer (nodes i) (u0 i) (u1 i) Q:=by
      simp only [outer,heq,map_mul,map_pow]
    change Polynomial.X^n∣outer (nodes i) (u0 i) (u1 i) P at hp
    rw [he] at hp
    have hq:=ALQ.quotient_jet _ _ hJ q n hp
    apply AMR.GFN Q hfree (nodes i) (u0 i) (u1 i) (ord i)
    exact (AMR.BZR _ _).mpr hq
  have hzero:(0:K)∉s.map nodes:=by
    intro h
    obtain ⟨i,hi,he⟩:=Finset.mem_map.mp h
    exact hnodes i hi he
  let orders:K→ℕ:=fun x=>if h:x∈s.map nodes then ord ((Finset.mem_map.mp h).choose) else 0
  have horders (i:I) (hi:i∈s):orders (nodes i)=ord i:=by
    have hh:nodes i∈s.map nodes:=Finset.mem_map.mpr ⟨i,hi,rfl⟩
    dsimp only [orders]
    rw [dif_pos hh]
    have he:=(Finset.mem_map.mp hh).choose_spec.2
    have he' :=nodes.injective he
    rw [he']
  have hsum:(∑ x∈s.map nodes,orders x)=(∑ i∈s,ord i):=by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i hi
    exact horders i hi
  have hm:D≤q*m*G+∑ x∈s.map nodes,orders x:=by
    rw [hsum]
    change D≤q*m*G+∑ i∈s,(n-q*mu i)
    omega
  have hz:(MvPolynomial.finSuccEquiv K 4) Q=0:=by
    apply ALQ.CSN _ weight
      (s.map nodes) orders D (q*m*G) (∑ x∈s.map nodes,orders x) hzero hcode hlow ?_ le_rfl hm
    intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_map.mp hx
    rw [horders i hi]
    exact hroot i hi
  exact (MvPolynomial.finSuccEquiv K 4).injective (by simpa only [map_zero] using hz)
end
end NS

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace SI
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

abbrev Index (C T B S U d:ℕ):=
  RB.Index (C-131071) (T-1) B S (U-1) ⊕
  RB.Index d T B S U

def exponent (C T B S U d:ℕ):Index C T B S U d→Fin 5→₀ ℕ
  | .inl i=>RB.exponent (C-131071) (T-1) B S (U-1) i+Finsupp.single 2 1
  | .inr i=>RB.exponent d T B S U i

def count (C T B S U d:ℕ):ℕ:=
  AM.AW (fun _=>C-131071) 131071 (T-1) B S (U-1)+
  AM.AW (fun _=>d) 131071 T B S U

theorem card_eq (C T B S U d:ℕ) (hUT:U≤T):
    Fintype.card (Index C T B S U d)=count C T B S U d:=by
  rw [Fintype.card_sum,RB.card_eq _ _ _ _ _ (Nat.sub_le_sub_right hUT 1),
    RB.card_eq _ _ _ _ _ hUT]
  rfl

def lowerA (e:Fin 5→₀ ℕ):=Finsupp.equivFunOnFinite.symm
  (fun i=>if i=2 then e 2-1 else e i)

@[simp] theorem lowerA_apply (e:Fin 5→₀ ℕ) (i:Fin 5):
    lowerA e i=if i=2 then e 2-1 else e i:=by simp [lowerA]

theorem positive_mem (C T B S U d:ℕ) (e:Fin 5→₀ ℕ)
    (hpos:0<e 2) (hc:e 0+131069*e 1+131071*e 2+131070*e 3<C)
    (ht:e 1+e 2+e 3+e 4≤T) (hb:2*e 1+e 3≤B) (hs:e 1≤S)
    (hu:e 1+e 2+e 3≤U):e∈Set.range (exponent C T B S U d):=by
  have hm:lowerA e∈Set.range (RB.exponent (C-131071) (T-1) B S (U-1)):=by
    apply RB.AKF
    all_goals simp only [lowerA_apply,Fin.isValue,ite_true,ite_false,show (0:Fin 5)≠2 by decide,
      show (1:Fin 5)≠2 by decide,show (3:Fin 5)≠2 by decide,show (4:Fin 5)≠2 by decide]
    all_goals omega
  obtain ⟨i,hi⟩:=hm
  refine ⟨Sum.inl i,?_⟩
  simp only [exponent,hi]
  ext j
  fin_cases j<;>simp [lowerA,Finsupp.single_apply]<;>omega

theorem low_mem (C T B S U d:ℕ) (e:Fin 5→₀ ℕ)
    (hc:e 0+131069*e 1+131071*e 2+131070*e 3<d)
    (ht:e 1+e 2+e 3+e 4≤T) (hb:2*e 1+e 3≤B) (hs:e 1≤S)
    (hu:e 1+e 2+e 3≤U):e∈Set.range (exponent C T B S U d):=by
  obtain ⟨i,hi⟩:=RB.AKF d T B S U e hc ht hb hs hu
  exact ⟨Sum.inr i,hi⟩

variable {K:Type*} [Field K]

theorem FCF {W:Type*} [AddCommGroup W] [Module K W]
    {I:Type*} [Fintype I] (e:I→Fin 5→₀ ℕ)
    (f:W→ₗ[K] DX.Poly (K:=K))
    (hzero: ∀v:W,(∀i,(f v).coeff (e i)=0)→v=0):
    Module.finrank K W≤Fintype.card I:=by
  let A:W→ₗ[K] (I→K):=LinearMap.pi (fun i=>(MvPolynomial.lcoeff K (e i)).comp f)
  have hi:Function.Injective A:=by
    intro v u h
    have hh:A (v-u)=0:=by rw [map_sub,h,sub_self]
    have hz:v-u=0:=hzero (v-u) (fun i=>congrFun hh i)
    exact sub_eq_zero.mp hz
  simpa using LinearMap.finrank_le_finrank_of_injective hi
end
end SI

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace LM
open MvPolynomial DX HZ IM
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K I:Type*} [Field K]

def code (e:Fin 5→₀ ℕ):=e 0+131069*e 1+131071*e 2+131070*e 3
def innerCode (e:Fin 4→₀ ℕ):=131069*e 0+131071*e 1+131070*e 2

theorem code_cons (e:Fin 4→₀ ℕ) (j:ℕ):code (e.cons j)=j+innerCode e:=by
  have h0:(e.cons j) 0=j:=Finsupp.cons_zero j e
  have h1:(e.cons j) 1=e 0:=Finsupp.cons_succ 0 j e
  have h2:(e.cons j) 2=e 1:=Finsupp.cons_succ 1 j e
  have h3:(e.cons j) 3=e 2:=Finsupp.cons_succ 2 j e
  simp only [code,innerCode,h0,h1,h2,h3]
  omega

def Bounds (C T B S U:ℕ) (Q:Poly (K:=K)):Prop:= ∀e∈Q.support,
  code e<C∧e 1+e 2+e 3+e 4≤T∧2*e 1+e 3≤B∧e 1≤S∧e 1+e 2+e 3≤U

theorem FCU (C T B S U d:ℕ) (Q:Poly (K:=K))
    (hb:Bounds C T B S U Q)
    (hp: ∀i,Q.coeff (SI.exponent C T B S U d i)=0):
    Q.degreeOf 2=0∧ ∀e j,j+innerCode e<d→
      (((MvPolynomial.finSuccEquiv K 4) Q).coeff j).coeff e=0:=by
  classical
  have hpos (e:Fin 5→₀ ℕ) (he:e∈Q.support):e 2=0:=by
    by_contra hn
    obtain ⟨hc,ht,hB,hs,hu⟩:=hb e he
    obtain ⟨i,hi⟩:=SI.positive_mem C T B S U d e
      (Nat.pos_of_ne_zero hn) hc ht hB hs hu
    have hz:=hp i
    rw [hi] at hz
    exact (MvPolynomial.mem_support_iff.mp he) hz
  constructor
  · apply Nat.eq_zero_of_le_zero
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro e he
    rw [hpos e he]
  · intro e j hd
    rw [MvPolynomial.finSuccEquiv_coeff_coeff]
    by_cases hz:Q.coeff (e.cons j)=0
    · exact hz
    have he:e.cons j∈Q.support:=MvPolynomial.mem_support_iff.mpr hz
    obtain ⟨_,ht,hB,hs,hu⟩:=hb (e.cons j) he
    have hc:code (e.cons j)<d:=by
      simpa only [code_cons] using hd
    obtain ⟨i,hi⟩:=SI.low_mem C T B S U d (e.cons j) hc ht hB hs hu
    simpa only [hi] using hp i

theorem FPZ (Q:Poly (K:=K)) (D:ℕ)
    (hc: ∀e∈Q.support,code e<D):
    ∀e j,(((MvPolynomial.finSuccEquiv K 4) Q).coeff j).coeff e≠0→j+innerCode e<D:=by
  intro e j hh
  rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hh
  have hb:=hc (e.cons j) (MvPolynomial.mem_support_iff.mpr hh)
  simpa only [code_cons] using hb

/-- Dimension bound using the auxiliary kernel's retained contact conditions. -/
theorem EHI
    (nodes:I ↪ K) (u0 u1:I→K) (s:Finset I)
    (J:Poly (K:=K)) (q m n A W G nu D C T B S U:ℕ)
    (V:Submodule K (Poly (K:=K)))
    (Q:V→ₗ[K] Poly (K:=K))
    (heq: ∀v:V,v.val=J^q*Q v)
    (hbound: ∀v:V,Bounds C T B S U (Q v))
    (hcode: ∀v:V,∀e∈(Q v).support,code e<D)
    (hjet: ∀v:V,∀i∈s,MvPolynomial.X 0^n∣substitute (K:=K)
      (localize (nodes i) (u0 i) (u1 i) v.val))
    (f:Polynomial K) (z:K) (hag: ∀i∈s,f.eval (nodes i)=u0 i+u1 i*z)
    (hne:HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0)
    (hdegree:(HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤nu-m*W)
    (hnu:m*W≤nu) (hA:A=W+G) (hcard:s.card=A) (hD:D+q*nu=n*A)
    (hnodes: ∀i∈s,nodes i≠0) (hUT:U≤T):
    Module.finrank K V≤SI.count C T B S U (q*m*G):=by
  have hh:Module.finrank K V≤Fintype.card (SI.Index C T B S U (q*m*G)):=by
    apply SI.FCF
      (SI.exponent C T B S U (q*m*G)) Q
    intro v hp
    obtain ⟨hfree,hlow⟩:=FCU C T B S U (q*m*G) (Q v) (hbound v) hp
    have hz:=NS.DNO
      nodes u0 u1 s J v.val (Q v) q m n A W G nu D (heq v) hfree (hjet v)
      f z hag hne hdegree hnu hA hcard hD hnodes innerCode
      (FPZ (Q v) D (hcode v)) hlow
    apply Subtype.ext
    simp only [heq v,hz,mul_zero,ZeroMemClass.coe_zero]
  rw [SI.card_eq C T B S U (q*m*G) hUT] at hh
  exact hh
end
end LM

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BJM
open MvPolynomial DX BX FR DP
open OR JQ
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K E:Type*} [Field K] [Field E]

theorem DEB
    (J:Poly (K:=K)) (F:MvPolynomial (Fin 4) K)
    (phi:MvPolynomial (Fin 4) K→+*E) (s m:ℕ)
    (hS: ∀e∈J.support,e 1≤s) (hF:phi F=0)
    (hH:phi (2*RCN313.polyH K F)≠0) (hne:(asS J).map phi≠0)
    (hfact:(m.factorial:E)≠0)
    (hm:((asS J).map phi).rootMultiplicity (ratio phi F)=m):
    ¬F∣helper J F (s-m) m:=by
  have hder:(((Polynomial.derivative)^[m] ((asS J).map phi)).eval (ratio phi F))≠0:=by
    rcases BMM.BOS
      ((asS J).map phi) hne (ratio phi F) m hfact with h | h
    · obtain ⟨d,hd,hn⟩:=h
      have he:d=m:=by
        by_contra hdm
        have hlt:d<((asS J).map phi).rootMultiplicity (ratio phi F):=by omega
        exact hn (Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity hlt)
      simpa only [he] using hn
    · have hh:=(Polynomial.le_rootMultiplicity_iff hne).mpr h
      omega
  intro hd
  have hz:=map_dvd phi hd
  rw [hF,zero_dvd_iff,CNM J F phi s m hS hH] at hz
  exact (mul_ne_zero (pow_ne_zero _ hH) hder) hz

section PacketSeed
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
open RCN095 RCN234 RCN156
open DU ER
open CB EF
open FF HI

theorem CZX {t y r:ℕ} (nodes:I ↪ K)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (p:Parameters) (hp:Shape p) (J:Poly (K:=K)) (m:ℕ)
    (hm:m≤p.s)
    (hflags: ∀e∈J.support,2*e 1+e 3≤p.B∧e 1+e 2+e 3≤p.U∧
      e 1+e 2+e 3+e 4≤p.L)
    (hslope: ∀e∈J.support,e 1≤p.s)
    (hproper: ¬P.F∣helper J P.F (p.s-m) m)
    (hb:p.B≤256) (hu:p.U≤512) (hl:p.L≤4096) (hs:p.s≤64):
    P.seeds.card<2000000000000000∨
      ∃gamma∈P.seeds,HH.specialize (P.selected gamma) gamma
        ((MvPolynomial.pderiv 1)^[m] J)≠0:=by
  classical
  by_cases hex: ∃gamma∈P.seeds,HH.specialize (P.selected gamma) gamma
      ((MvPolynomial.pderiv 1)^[m] J)≠0
  · exact Or.inr hex
  left
  have hzero: ∀gamma∈P.seeds,HH.specialize (P.selected gamma) gamma
      ((MvPolynomial.pderiv 1)^[m] J)=0:=by
    simpa only [not_exists,not_and,not_not] using hex
  have hF:=And.intro P.r_weight (And.intro P.y_weight P.total_weight)
  have hweights:=EUI J P.F p.B p.U p.L p.s m t y r hp.slope
    (by have:=hp.slope;have:=hp.middle;omega)
    (by have:=hp.slope;have:=hp.middle;have:=hp.total;omega) hm
    (by have:=P.rlow;omega) (by have:=P.rlow;have:=P.ylow;omega)
    (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega) hflags hF
  have hrr:=Nat.mul_le_mul_right (r-1) (Nat.sub_le p.s m)
  have hyy:=Nat.mul_le_mul_right (y-1) (Nat.sub_le p.s m)
  have htt:=Nat.mul_le_mul_right (t-1) (Nat.sub_le p.s m)
  have hweights' :wt BE (helper J P.F (p.s-m) m)≤p.B+p.s*(r-1)∧
      wt BC (helper J P.F (p.s-m) m)≤p.U+p.s*(y-1)∧
      wt AT (helper J P.F (p.s-m) m)≤p.L+p.s*(t-1):=by omega
  obtain ⟨hr,hy,ht⟩:=KY.ESM p P hb hu hl hs
  have hg:=KY.gates_mono t y r _ _ _ 4100 117 13 1024 7936 266432
    P.thigh P.yhigh P.rhigh hr hy ht KY.DZN.1
  have hc:=ER.DHG P (helper J P.F (p.s-m) m)
    _ _ _ (P.irreducible.isRelPrime_iff_not_dvd.mpr hproper) hweights' hg
    (fun gamma hgamma=>FAI J P.F (p.s-m) m
      (AFG J p.s m hslope) (P.selected gamma) gamma
      (P.solution gamma hgamma) (hzero gamma hgamma))
  exact hc.trans_lt ((KY.count_mono t y r _ _ _ 4100 117 13 1024 7936 266432
    P.thigh P.yhigh P.rhigh hr hy ht).trans_lt KY.DZN.2)
def maximumOwner:Parameters:=⟨65,4096,256,64,512,0,1⟩
theorem ENC:Shape maximumOwner:=by constructor<;>decide+kernel

theorem CMA {t y r:ℕ} (nodes:I ↪ K)
    (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (J:Poly (K:=K)) (m:ℕ) (hms:m≤J.degreeOf 1) (horder:J.degreeOf 1≤64)
    (hflags: ∀e∈J.support,2*e 1+e 3≤256∧e 1+e 2+e 3≤512∧
      e 1+e 2+e 3+e 4≤4096)
    (hne:(asS J).map (DC.carrierMap P.F)≠0)
    (hm:((asS J).map (DC.carrierMap P.F)).rootMultiplicity
      (ratio (DC.carrierMap P.F) P.F)=m):
    P.seeds.card<2000000000000000∨
      ∃gamma∈P.seeds,HH.specialize (P.selected gamma) gamma
        ((MvPolynomial.pderiv 1)^[m] J)≠0:=by
  have hS: ∀e∈J.support,e 1≤64:=fun e he=>(MvPolynomial.monomial_le_degreeOf 1 he).trans horder
  have hchar:=P.IZ.2.1.trans_lt
    (by have:=P.rhigh;omega:r<2130706433)
  have hnot:=DEB J P.F (DC.carrierMap P.F)
    64 m hS (DC.DQY P.F)
    (DC.ALO P.F P.rdegree hchar) hne
    (TI.factorial_ne m (by omega)) hm
  exact CZX nodes P maximumOwner ENC J m
    (hms.trans horder) hflags hS hnot (by decide) (by decide) (by decide) (by decide)

end PacketSeed

end
end BJM

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AIP
open MvPolynomial DX
open LM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
variable {K:Type*} [Field K]

theorem code_add_S (e:Fin 5→₀ ℕ) (m:ℕ):
    code (e+Finsupp.single 1 m)=code e+131069*m:=by
  simp only [code,Finsupp.add_apply,Finsupp.single_apply]
  norm_num
  ring

theorem ARL
    (J:Poly (K:=K)) (f:Polynomial K) (z:K) (m nu:ℕ)
    (hf:f.natDegree≤131071) (hc: ∀e∈J.support,code e≤nu):
    (HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤nu-m*131069:=by
  have hh:=HH.DRK ((MvPolynomial.pderiv 1)^[m] J)
    f z 131071 (nu-m*131069+1) hf (by omega) (by
      intro e he
      have h:=hc _ (KL.CAJ J m e he)
      rw [code_add_S] at h
      change e 0+131071*e 2+131070*e 3+131069*e 1<nu-m*131069+1
      dsimp only [code] at h
      omega)
  omega
end
end AIP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace TA
open MvPolynomial CW DJ XB
open DX HZ IM
open DA
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
variable {K I:Type*} [Field K]



theorem BLT (e:Fin 5→₀ ℕ):
    LM.code e=Finsupp.weight codeWeights e:=by
  simp [LM.code,JW,codeWeights,Nat.mul_comm,Nat.add_comm,
    Nat.add_left_comm,Nat.add_assoc]


end
end TA

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BYG
open MvPolynomial CW DJ
open DX HZ IM
open FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

variable {K:Type*} [Field K]
theorem EHN (J:DX.Poly (K:=K)) (hJ:J≠0) (m:ℕ)
    (hms:m≤J.degreeOf 1):m*131069≤weightedTotalDegree codeWeights J:=by
  classical
  obtain ⟨e,he,hh⟩:=Finset.exists_mem_eq_sup J.support (MvPolynomial.support_nonempty.mpr hJ)
    (fun e=>e (1:Fin 5))
  have hd:J.degreeOf 1=e 1:=by rw [MvPolynomial.degreeOf_eq_sup];exact hh
  have hc:LM.code e≤weightedTotalDegree codeWeights J:=by
    rw [TA.BLT]
    exact le_weightedTotalDegree codeWeights he
  dsimp only [LM.code] at hc
  rw [hd] at hms
  nlinarith

variable {K N:Type} [Field K] [Fintype N]

end
end BYG

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BSV
open scoped BigOperators
open MvPolynomial DX HZ IM
open LM
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K I:Type*} [Field K]

theorem DYW
    (nodes:I ↪ K) (u0 u1:I→K) (s:Finset I)
    (J P Q:Poly (K:=K)) (q m n nu D:ℕ)
    (heq:P=J^q*Q)
    (hjet: ∀i∈s,MvPolynomial.X 0^n∣substitute (K:=K) (localize (nodes i) (u0 i) (u1 i) P))
    (f:Polynomial K) (z:K) (hf:f.natDegree≤131071)
    (hag: ∀i∈s,f.eval (nodes i)=u0 i+u1 i*z)
    (hne:HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)≠0)
    (hdegree:(HH.specialize f z ((MvPolynomial.pderiv 1)^[m] J)).natDegree≤nu-m*131069)
    (hnu:m*131069≤nu) (hcard:s.card=181235) (hD:D+q*nu=n*181235)
    (hQ:weightedTotalDegree CW.codeWeights Q<D-q*m*50166):
    HH.specialize f z Q=0:=by
  classical
  let mu (i:I):=(NS.outer (nodes i) (u0 i) (u1 i) J).rootMultiplicity 0
  let ord (i:I):=n-q*mu i
  have hmu (i:I):MvPolynomial.X 0^mu i∣substitute (K:=K) (localize (nodes i) (u0 i) (u1 i) J):=by
    apply (AMR.BZR _ _).mpr
    simpa only [mu,NS.outer,map_zero,sub_zero] using
      (NS.outer (nodes i) (u0 i) (u1 i) J).pow_rootMultiplicity_dvd 0
  have hloss:=ASN.DIJ nodes u0 u1 J f z s
    mu m (nu-m*131069) hag (fun i _=>hmu i) hne hdegree
  have hmass:=ALQ.DZT s mu q m n 181235 131069 50166 nu
    (by decide) hcard hnu hloss
  let R:=HH.specialize f z Q
  by_contra hR
  have hroot (i:I) (hi:i∈s):ord i≤R.rootMultiplicity (nodes i):=by
    have hJ:NS.outer (nodes i) (u0 i) (u1 i) J≠0:=by
      intro hz
      apply NS.BXW J f (nodes i) (u0 i) (u1 i) z m (hag i hi) hne
      exact (MvPolynomial.finSuccEquiv K 4).injective (by simpa only [NS.outer,map_zero] using hz)
    have hp:=(AMR.BZR _ _).mp (hjet i hi)
    have he:NS.outer (nodes i) (u0 i) (u1 i) P=
      (NS.outer (nodes i) (u0 i) (u1 i) J)^q*
        NS.outer (nodes i) (u0 i) (u1 i) Q:=by
      simp only [NS.outer,heq,map_mul,map_pow]
    change Polynomial.X^n∣NS.outer (nodes i) (u0 i) (u1 i) P at hp
    rw [he] at hp
    have hq:=ALQ.quotient_jet _ _ hJ q n hp
    have hcontact:=(AMR.BZR _ _).mpr hq
    have hh:=HH.root_contact Q f (nodes i) (u0 i) (u1 i) z (ord i) (hag i hi) hcontact
    exact (Polynomial.le_rootMultiplicity_iff hR).mpr hh
  have hsum:(∑ i∈s,ord i)≤R.natDegree:=by
    have h1:=Finset.sum_le_sum hroot
    have h2:=RCN355._Q14 R (s.map nodes)
    rw [Finset.sum_map] at h2
    exact h1.trans h2
  have hdeg:R.natDegree≤weightedTotalDegree CW.codeWeights Q:=by
    have hh:=AIP.ARL Q f z 0
      (weightedTotalDegree CW.codeWeights Q) hf (fun e he=>by
        rw [TA.BLT]
        exact le_weightedTotalDegree CW.codeWeights he)
    simpa only [Function.iterate_zero,id_eq,Nat.zero_mul,Nat.sub_zero] using hh
  change n*181235≤(∑ i∈s,ord i)+q*nu+q*m*50166 at hmass
  omega
end
end BSV

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AMK
open scoped BigOperators
open MvPolynomial DX HZ IM
open BX FR DP
open BJM
open RCN095 RCN234 DU DC
open FF
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]

abbrev Small (Q:Poly (K:=K)):Prop:=Q.degreeOf 1≤64∧
  ∀e∈Q.support,2*e 1+e 3≤256∧e 1+e 2+e 3≤512∧e 1+e 2+e 3+e 4≤4096

theorem FIN {t y r:ℕ}
    (nodes:I ↪ K) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
    (J T Q:Poly (K:=K)) (hJ:J≠0) (q m n nu D:ℕ)
    (heq:T=J^q*Q)
    (hjet: ∀i,MvPolynomial.X 0^n∣substitute (K:=K) (localize (nodes i) (P.u0 i) (P.u1 i) T))
    (hms:m≤J.degreeOf 1) (hJs:Small J) (hQs:Small Q)
    (hJne:(asS J).map (carrierMap P.F)≠0)
    (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
    (hnu:weightedTotalDegree CW.codeWeights J=nu)
    (hD:D+q*nu=n*181235)
    (hQcode:weightedTotalDegree CW.codeWeights Q<D-q*m*50166):
    P.F∣helper Q P.F 64 0∨P.seeds.card<4000000000000000:=by
  classical
  by_cases hproper:P.F∣helper Q P.F 64 0
  · exact Or.inl hproper
  right
  let zeroSeeds:=P.seeds.filter (fun g=>HH.specialize (P.selected g) g Q=0)
  let nonzeroSeeds:=P.seeds.filter (fun g=>HH.specialize (P.selected g) g Q≠0)
  have hZsub:zeroSeeds⊆P.seeds:=Finset.filter_subset _ _
  have hUsub:nonzeroSeeds⊆P.seeds:=Finset.filter_subset _ _
  let zeroPacket:=P.restrict zeroSeeds hZsub
  let nonzeroPacket:=P.restrict nonzeroSeeds hUsub
  letI:Fact (Irreducible zeroPacket.F):=⟨zeroPacket.irreducible⟩
  letI:Fact (Irreducible nonzeroPacket.F):=⟨nonzeroPacket.irreducible⟩
  have hZsmall:zeroSeeds.card<2000000000000000:=by
    rcases CZX nodes zeroPacket maximumOwner ENC Q 0
        (by decide) hQs.2 (fun e he=>(MvPolynomial.monomial_le_degreeOf 1 he).trans hQs.1)
        hproper (by decide) (by decide) (by decide) (by decide)
        with hs | ⟨g,hg,hn⟩
    · exact hs
    · have hz:=(Finset.mem_filter.mp hg).2
      exact False.elim (hn (by simpa only [zeroPacket,Packet.restrict,Function.iterate_zero,id_eq] using hz))
  have hUsmall:nonzeroSeeds.card<2000000000000000:=by
    rcases CMA nodes nonzeroPacket J m hms hJs.1 hJs.2 hJne hroot
        with hs | ⟨g,hg,hn⟩
    · exact hs
    · have hgP:g∈P.seeds:=hUsub hg
      obtain ⟨Aagree,hAsub,hAcard⟩:=Finset.exists_subset_card_eq (P.agreement g hgP)
      have hag: ∀i∈Aagree,(P.selected g).eval (nodes i)=P.u0 i+P.u1 i*g:=by
        intro i hi
        simpa only [mul_comm] using (Finset.mem_filter.mp (hAsub hi)).2
      have hnuLow:m*131069≤nu:=by
        rw [←hnu]
        exact BYG.EHN J hJ m hms
      have hdeg:=AIP.ARL J (P.selected g) g m nu
        (P.degree g hgP) (fun e he=>by
          rw [TA.BLT]
          exact (le_weightedTotalDegree CW.codeWeights he).trans_eq hnu)
      have hz:=BSV.DYW nodes P.u0 P.u1 Aagree
        J T Q q m n nu D heq (fun i _=>hjet i) (P.selected g) g (P.degree g hgP)
        hag hn hdeg hnuLow hAcard hD hQcode
      exact False.elim ((Finset.mem_filter.mp hg).2 hz)
  have hcover:P.seeds⊆zeroSeeds∪nonzeroSeeds:=by
    intro g hg
    by_cases hz:HH.specialize (P.selected g) g Q=0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hg,hz⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hg,hz⟩)
  have hc:=(Finset.card_le_card hcover).trans (Finset.card_union_le zeroSeeds nonzeroSeeds)
  omega
end
end AMK

end SubmissionLower
end ProximityPrize
end
namespace ProximityPrize.SubmissionLower.BandPrefixKernel6816
open scoped BigOperators
 theorem weighted_prefix (q C M : Nat) :
 (∑ a : Fin M, (q-131071*a.val)*(C-a.val)) =
 CPV.weightedCell q 131071 C (min ((q-1)/131071+1) (min M C)) := by
  let n := min ((q-1)/131071+1) (min M C)
  have hnM : n≤M := by dsimp [n]; omega
  have hs : (∑a ∈ Finset.range M, (q-131071*a)*(C-a)) =
   ∑a ∈ Finset.range n, (q-131071*a)*(C-a) := by
   symm
   apply Finset.sum_subset (Finset.range_mono hnM)
   intro a ha hnot
   simp only [Finset.mem_range] at ha hnot
   have hz : q-131071*a=0 ∨ C-a=0 := by dsimp [n] at hnot; omega
   rcases hz with hz|hz <;> simp only [hz, Nat.zero_mul, Nat.mul_zero]
  calc
   _ = ∑a : Fin n, (q-131071*a.val)*(C-a.val) := by
    rw [Fin.sum_univ_eq_sum_range (fun a : Nat => (q-131071*a)*(C-a)),
        Fin.sum_univ_eq_sum_range (fun a : Nat => (q-131071*a)*(C-a))]
    exact hs
   _ = _ := by
    apply CPV.ESA
    · intro a
      have ha := a.isLt
      dsimp [n] at ha
      omega
    · intro a
      have ha := a.isLt
      dsimp [n] at ha
      omega

 theorem sum_fin_cut (f : Nat → Nat) (M n : Nat) (hn : n≤M)
  (hz : ∀ (i : Nat), n ≤ i → i < M → f i = 0) : (∑i : Fin M, f i.val) = ∑i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range f, Fin.sum_univ_eq_sum_range f]
  symm
  apply Finset.sum_subset (Finset.range_mono hn)
  intro i hi hnot
  simp only [Finset.mem_range] at hi hnot
  exact hz i (by omega) hi
 def row (D T B U h : Nat) : Nat :=
  ∑r : Fin (B+1-2*h), ∑a : Fin (U+1-h-r.val),
   (D-131069*h-131070*r.val-131071*a.val)*(T+1-h-r.val-a.val)
 def prefixCount (D T B S U : Nat) : Nat := ∑h : Fin (S+1), row D T B U h.val
 theorem prefix_eq (D T B S U : Nat) :
 prefixCount D T B S U = AM.AW (fun _ => D) 131071 T B (min S (B/2)) (min U T) := by
  have hcut : prefixCount D T B S U = ∑h : Fin (min S (B/2)+1), row D T B U h.val := by
   apply sum_fin_cut
   · omega
   · intro h hlo hhi
     have hz : B+1-2*h=0 := by omega
     simp [row, hz]
  rw [hcut]
  unfold AM.AW
  apply Finset.sum_congr rfl
  intro h hh
  have hm := h.isLt
  have hb : B+1-2*h.val=B-2*h.val+1 := by omega
  unfold row
  rw [hb]
  apply Finset.sum_congr rfl
  intro r hr
  rw [weighted_prefix]
  dsimp only [DD.yCount, DD.budget]
  norm_num only [Nat.reduceSub]
  congr 1 <;> omega

 def inner (h r a : Nat) := 131069*h+131070*r+131071*a
 def rawCount (D width T B S U : Nat) : Nat :=
 ∑h : Fin (S+1), ∑r : Fin (B+1-2*h.val), ∑a : Fin (U+1-h.val-r.val),
  min width (D-inner h.val r.val a.val)*(T+1-h.val-r.val-a.val)
 theorem band_add_prefix (D width T B S U : Nat) :
 rawCount D width T B S U + prefixCount (D-width) T B S U = prefixCount D T B S U := by
  unfold rawCount prefixCount row
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have e1 : D-131069*h.val-131070*r.val-131071*a.val = D-inner h.val r.val a.val := by unfold inner; omega
  have e2 : D-width-131069*h.val-131070*r.val-131071*a.val = D-width-inner h.val r.val a.val := by unfold inner; omega
  rw [e1, e2, ←Nat.add_mul]
  have he : min width (D-inner h.val r.val a.val)+(D-width-inner h.val r.val a.val)=D-inner h.val r.val a.val := by omega
  rw [he]
 def closedCount (D width T B S U : Nat) : Nat :=
 AM.AW (fun _ => D) 131071 T B (min S (B/2)) (min U T) -
 AM.AW (fun _ => D-width) 131071 T B (min S (B/2)) (min U T)
 theorem count_eq (D width T B S U : Nat) : rawCount D width T B S U = closedCount D width T B S U := by
  have h := band_add_prefix D width T B S U
  rw [prefix_eq, prefix_eq] at h
  unfold closedCount
  omega
end ProximityPrize.SubmissionLower.BandPrefixKernel6816

section
namespace ProximityPrize.SubmissionLower
namespace BLM
open MvPolynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def inner (h r a:ℕ):=131069*h+131070*r+131071*a
def start (D width h r a:ℕ):=D-width-inner h r a
def length (D width h r a:ℕ):=min width (D-inner h r a)
def Index (D width T B S U:ℕ):=
 (h:Fin (S+1)) × (r:Fin (B+1-2*h.val)) × (a:Fin (U+1-h.val-r.val)) ×
 (Fin (length D width h.val r.val a.val) × Fin (T+1-h.val-r.val-a.val))
instance (D width T B S U:ℕ):Fintype (Index D width T B S U):=by unfold Index;infer_instance

def exponent (D width T B S U:ℕ) (i:Index D width T B S U):Fin 5→₀ ℕ:=
 Finsupp.equivFunOnFinite.symm ![start D width i.1.val i.2.1.val i.2.2.1.val+i.2.2.2.1.val,
   i.1.val,i.2.2.1.val,i.2.1.val,i.2.2.2.2.val]

def count (D width T B S U:ℕ):=BandPrefixKernel6816.closedCount D width T B S U

theorem count_eq_sum (D width T B S U:ℕ):count D width T B S U=
 ∑ h:Fin (S+1),∑ r:Fin (B+1-2*h.val),∑ a:Fin (U+1-h.val-r.val),
 length D width h.val r.val a.val*(T+1-h.val-r.val-a.val):=by
 exact (BandPrefixKernel6816.count_eq D width T B S U).symm

theorem card_eq (D width T B S U:ℕ):Fintype.card (Index D width T B S U)=count D width T B S U:=by
 simp only [Index,Fintype.card_sigma,Fintype.card_prod,Fintype.card_fin,count_eq_sum]

theorem count_mono_D (D E width T B S U:ℕ) (hDE:D≤E):
 count D width T B S U≤count E width T B S U:=by
 rw [count_eq_sum,count_eq_sum]
 apply Finset.sum_le_sum
 intro h _
 apply Finset.sum_le_sum
 intro r _
 apply Finset.sum_le_sum
 intro a _
 apply Nat.mul_le_mul_right
 exact min_le_min_left _ (Nat.sub_le_sub_right hDE _)

theorem AKF (D width T B S U:ℕ) (e:Fin 5→₀ ℕ)
 (hc:LM.code e<D) (hl:D-width≤LM.code e)
 (ht:e 1+e 2+e 3+e 4≤T) (hb:2*e 1+e 3≤B) (hs:e 1≤S)
 (hu:e 1+e 2+e 3≤U):e∈Set.range (exponent D width T B S U):=by
 have hh:e 1<S+1:=by omega
 have hr:e 3<B+1-2*e 1:=by omega
 have ha:e 2<U+1-e 1-e 3:=by omega
 have hstart:start D width (e 1) (e 3) (e 2)≤e 0:=by
   dsimp only [start,inner,LM.code] at*
   omega
 have hx:e 0-start D width (e 1) (e 3) (e 2)<length D width (e 1) (e 3) (e 2):=by
   dsimp only [start,length,inner,LM.code] at*
   omega
 have hg:e 4<T+1-e 1-e 3-e 2:=by omega
 refine ⟨⟨⟨e 1,hh⟩,⟨e 3,hr⟩,⟨e 2,ha⟩,⟨e 0-start D width (e 1) (e 3) (e 2),hx⟩,⟨e 4,hg⟩⟩,?_⟩
 ext j
 fin_cases j<;>simp [exponent,Nat.add_sub_of_le hstart]

theorem ECV {K:Type*} [Field K]
 (D width T B S U:ℕ) (Q:DX.Poly (K:=K)) (hQ:Q≠0)
 (hb:LM.Bounds D T B S U Q)
 (hp: ∀i,Q.coeff (exponent D width T B S U i)=0):
 weightedTotalDegree CW.codeWeights Q<D-width:=by
 classical
 have hevery: ∀e∈Q.support,Finsupp.weight CW.codeWeights e<D-width:=by
   intro e he
   obtain ⟨hc,ht,hB,hS,hU⟩:=hb e he
   rw [←TA.BLT]
   by_contra hn
   obtain ⟨i,hi⟩:=AKF D width T B S U e hc (by omega) ht hB hS hU
   exact (MvPolynomial.mem_support_iff.mp he) (by rw [←hi];exact hp i)
 have hpos:0<D-width:=by
   obtain ⟨e,he⟩:=MvPolynomial.support_nonempty.mpr hQ
   exact (Nat.zero_le _).trans_lt (hevery e he)
 have hh:weightedTotalDegree CW.codeWeights Q≤D-width-1:=by
   apply Finset.sup_le
   intro e he
   exact Nat.le_sub_one_of_lt (hevery e he)
 omega
end
end BLM

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace EKS
open MvPolynomial DX HZ
open BX FR DP
open DC CB BD
open AMK RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {K:Type} [Field K] [CharP K 2130706433]

theorem FGS
    (F:MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (cap:ℕ) (hFT:cap<wt AT F)
    (hpos:0<F.degreeOf 2) (hchar:F.degreeOf 2<2130706433)
    (Q:Poly (K:=K)) (hQ:Q≠0) (hS:Q.degreeOf 1≤64)
    (hT:total Q≤cap) (hdiv:F∣helper Q F 64 0):
    ∃SQ:Source F,SQ.P=Q∧1≤SQ.d:=by
  let phi:=carrierMap F
  have hH:phi (2*RCN313.polyH K F)≠0:=ALO F hpos hchar
  have hz:=map_dvd phi hdiv
  rw [DQY,zero_dvd_iff] at hz
  have hs: ∀e∈Q.support,e 1≤64:=fun e he=>(MvPolynomial.monomial_le_degreeOf 1 he).trans hS
  have hm:=CNM Q F phi 64 0 hs hH
  simp only [Nat.sub_zero,Function.iterate_zero,id_eq] at hm
  have hroot:((asS Q).map phi).eval (ratio phi F)=0:=by
    rw [hm] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hH)
  have hp:(Polynomial.X-Polynomial.C (ratio (carrierMap F) F))^1∣(asS Q).map (carrierMap F):=by
    simpa only [pow_one] using (Polynomial.dvd_iff_isRoot.mpr hroot)
  exact ZD.UN F cap hFT hpos hchar Q hQ hT 1 (by decide) hp
end
end EKS

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ZZ
open MvPolynomial CW DJ XB
open DA
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K:Type*} [Field K]

def powSpace (V:Submodule K (Poly (K:=K))) (J:Poly (K:=K)) (e:ℕ):Submodule K (Poly (K:=K)) where
 carrier:={P | P∈V∧J^e∣P}
 zero_mem' :=⟨V.zero_mem,dvd_zero _⟩
 add_mem' hP hQ:=⟨V.add_mem hP.1 hQ.1,dvd_add hP.2 hQ.2⟩
 smul_mem' c P hP:=by
   refine ⟨V.smul_mem c hP.1,?_⟩
   obtain ⟨Q,hQ⟩:=hP.2
   refine ⟨c • Q,?_⟩
   rw [hQ]
   simp only [MvPolynomial.smul_eq_C_mul]
   ring

theorem powSpace_le (V:Submodule K (Poly (K:=K))) (J:Poly (K:=K)) (e:ℕ):
 powSpace V J e≤V:=fun _ h=>h.1

@[simp] theorem GVA (V:Submodule K (Poly (K:=K))) (J:Poly (K:=K)):
 powSpace V J 0=V:=by ext P;simp [powSpace]

def bandCount (p:SourceCaps) (a:OwnerBox) (m e:ℕ):ℕ:=
 BLM.count (p.C-e*(131071*a.loU-a.hiB)) (e*m*50166)
   (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU)

theorem EAJ (p:SourceCaps) (a:OwnerBox) (e:ℕ)
 (P J Q:Poly (K:=K)) (hJ:J≠0) (hQ:Q≠0) (heq:P=J^e*Q)
 (hP:Bounds p P) (ha:Covers a J):
 LM.Bounds (p.C-e*weightedTotalDegree codeWeights J)
   (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU) Q:=by
 let aa:OwnerBox:={a with q:=e}
 have haa:Covers aa J:=ha
 obtain ⟨_,_,ht,hB,hS,hU⟩:=AUL p aa P J Q hJ hQ heq hP haa
 have hc:=hP.1
 rw [heq,weight_mul codeWeights _ _ (pow_ne_zero _ hJ) hQ,weight_pow codeWeights J hJ] at hc
 intro d hd
 have cc:=le_weightedTotalDegree codeWeights hd
 have tt:=(le_weightedTotalDegree totalWeights hd).trans ht
 have bb:=(le_weightedTotalDegree slopeWeights hd).trans hB
 have ss:=(MvPolynomial.monomial_le_degreeOf 1 hd).trans hS
 have uu:=(le_weightedTotalDegree HA hd).trans hU
 rw [←TA.BLT] at cc
 simp only [JW,totalWeights,slopeWeights,HA] at tt bb uu
 norm_num at tt bb uu
 dsimp only [aa,remT,remB] at tt bb ss uu
 refine ⟨by omega,?_,?_,ss,?_⟩<;>omega

theorem step
 (p:SourceCaps) (a:OwnerBox) (m e:ℕ)
 (V:Submodule K (Poly (K:=K))) [Module.Finite K V]
 (hb: ∀P∈V,Bounds p P) (J:Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
 (hlow: ∀(P Q:Poly (K:=K)),P∈V→P=J^e*Q→Q≠0→
   weightedTotalDegree codeWeights Q<p.C-e*weightedTotalDegree codeWeights J-e*m*50166→J∣Q):
 Module.finrank K (powSpace V J e)≤bandCount p a m e+Module.finrank K (powSpace V J (e+1)):=by
 classical
 let W:=powSpace V J e
 letI:Module.Finite K W:=Submodule.finiteDimensional_of_le (powSpace_le V J e)
 let hd: ∀v:W,J^e∣v.val:=fun v=>v.property.2
 let Q:=BKC W J e hJ hd
 have heq (v:W):v.val=J^e*Q v:=RV W J e hd v
 let D:=p.C-e*weightedTotalDegree codeWeights J
 let width:=e*m*50166
 let idx:=BLM.Index D width (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU)
 let ex:=BLM.exponent D width (p.T-e*a.loT) (p.B-e*a.loB) (p.S-e*a.loS) (p.U-e*a.loU)
 let proj:W→ₗ[K] (idx→K):=LinearMap.pi (fun i=>(MvPolynomial.lcoeff K (ex i)).comp Q)
 have hnext (v:proj.ker):(v.val:W).val∈powSpace V J (e+1):=by
   let w:W:=v.val
   have hp: ∀i,(Q w).coeff (ex i)=0:=by
     intro i
     have hh:=congrFun v.property i
     exact hh
   have hdiv:J∣Q w:=by
     by_cases hz:Q w=0
     · rw [hz];exact dvd_zero _
     apply hlow w.val (Q w) w.property.1 (heq w) hz
     exact BLM.ECV D width _ _ _ _ (Q w) hz
       (EAJ p a e w.val J (Q w) hJ hz (heq w) (hb w.val w.property.1) ha) hp
   refine ⟨w.property.1,?_⟩
   obtain ⟨R,hR⟩:=hdiv
   refine ⟨R,?_⟩
   rw [heq w,hR,pow_succ,mul_assoc]
 let inc:proj.ker→ₗ[K] powSpace V J (e+1):=
   (((powSpace V J e).subtype).comp proj.ker.subtype).codRestrict _ hnext
 have hi:Function.Injective inc:=by
   intro v u h
   apply Subtype.ext
   apply Subtype.ext
   have hh:=congrArg (fun z:powSpace V J (e+1)=>z.val) h
   change v.val.val=u.val.val at hh
   exact hh
 letI:Module.Finite K (powSpace V J (e+1)):=Submodule.finiteDimensional_of_le (powSpace_le V J (e+1))
 have hk:=LinearMap.finrank_le_finrank_of_injective hi
 have hr:Module.finrank K proj.range≤Fintype.card idx:=by
   have hh:=proj.range.finrank_le
   simpa using hh
 have hsum:=proj.finrank_range_add_finrank_ker
 change Module.finrank K proj.range+Module.finrank K proj.ker=Module.finrank K (powSpace V J e) at hsum
 have hactual:Fintype.card idx≤bandCount p a m e:=by
   rw [BLM.card_eq]
   apply BLM.count_mono_D
   apply Nat.sub_le_sub_left
   exact Nat.mul_le_mul_left e (BKI J hJ a.loU a.hiB ha.2.2.2.1 ha.2.1)
 omega

theorem telescope
 (p:SourceCaps) (a:OwnerBox) (m N:ℕ)
 (V:Submodule K (Poly (K:=K))) [Module.Finite K V]
 (hb: ∀P∈V,Bounds p P) (J:Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
 (hlow: ∀e<N,∀(P Q:Poly (K:=K)),P∈V→P=J^e*Q→Q≠0→
   weightedTotalDegree codeWeights Q<p.C-e*weightedTotalDegree codeWeights J-e*m*50166→J∣Q):
 Module.finrank K V≤(∑ e∈Finset.range N,bandCount p a m e)+Module.finrank K (powSpace V J N):=by
 induction N with
 | zero=>
   rw [GVA V J]
   simp
 | succ N ih=>
   have hprev:=ih (fun e he=>hlow e (by omega))
   have hstep:=step p a m N V hb J hJ ha (hlow N (by omega))
   rw [Finset.sum_range_succ]
   omega




theorem EVH
 (p:SourceCaps) (a:OwnerBox) (N:ℕ)
 (V:Submodule K (Poly (K:=K)))
 (hb: ∀P∈V,Bounds p P) (J:Poly (K:=K)) (hJ:J≠0) (ha:Covers a J)
 (hstop:Impossible p {a with q:=N}):powSpace V J N=⊥ :=by
 apply le_antisymm _ bot_le
 intro P hP
 change P=0
 by_contra hPne
 obtain ⟨Q,hQ⟩:=hP.2
 have heq:P=J^N*Q:=hQ
 have hQne:Q≠0:=by intro hz;simp [hz] at heq;exact hPne heq
 exact (AUL p {a with q:=N} P J Q hJ hQne heq (hb P hP.1) ha).1 hstop

end
end ZZ

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace DDV
open MvPolynomial CW DJ XB
open DX HZ IM
open CB DC BD
open DU EF GF
open BX DP
open HI LV DR BH
open RCN095 RCN234 RCN156 ER
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]

theorem GHY {t y r:ℕ}
 (nodes:I ↪ K) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (p:DA.SourceCaps) (n:ℕ) (hpC:p.C=n*181235)
 (hpSmall:p.B≤256∧p.U≤512∧p.T≤4096∧p.S≤64)
 (hFT:p.T<wt AT P.F)
 (J:CW.Poly (K:=K)) (hJ:Irreducible J) (a:DR.Box) (ha:Contains a (point J))
 (m:ℕ) (hms:m≤J.degreeOf 1) (hJs:AMK.Small J)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (SJ SZ:Source P.F) (hSJ:SJ.P=J) (hSJd:1≤SJ.d)
 (z:Degrees) (hZ:Fits SZ z) (hZFT:z.T<wt AT P.F)
 (hk:z.k<2130706433) (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
 (cap:ℕ) (hcap:4000000000000000≤cap) (hlarge:cap<P.seeds.card)
 (hidentity:MG t y r≤cap)
 (hgeo:flagMixed (ownerFlag a) (flag p.B p.U p.T p.S) unitZFlag<2130706433∧
   flagMixed (ownerFlag a) (flag p.B p.U p.T p.S) unitYZFlag<2130706433∧
   pairCost z 1 (ownerFlag a) (flag p.B p.U p.T p.S) t y r+leading z t y r≤cap)
 (e:ℕ) (T Q:CW.Poly (K:=K))
 (heq:T=J^e*Q) (hQ:Q≠0) (hb:DA.Bounds p T)
 (hjet: ∀i,MvPolynomial.X 0^n∣substitute (K:=K) (localize (nodes i) (P.u0 i) (P.u1 i) T))
 (hcode:weightedTotalDegree codeWeights Q<p.C-e*weightedTotalDegree codeWeights J-e*m*50166):
 J∣Q:=by
 classical
 by_contra hnot
 have hn:=ZZ.EAJ p (⟨e,0,weightedTotalDegree slopeWeights J,0,0,0⟩) e
   T J Q hJ.ne_zero hQ heq hb (by exact ⟨Nat.zero_le _,le_rfl,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩)
 have hTQ:total Q≤p.T:=by
   apply Finset.sup_le
   intro d hd
   have hh:=(hn d hd).2.1
   simpa [total,JW,totalWeights] using hh
 have hBQ:slope Q≤p.B:=by
   apply Finset.sup_le
   intro d hd
   have hh:=(hn d hd).2.2.1
   simpa [CB.slope,JW,slopeWeights,Nat.mul_comm] using hh
 have hSQ:Q.degreeOf 1≤p.S:=by
   apply MvPolynomial.degreeOf_le_iff.mpr
   exact fun d hd=>(hn d hd).2.2.2.1
 have hUQ:middle Q≤p.U:=by
   apply Finset.sup_le
   intro d hd
   have hh:=(hn d hd).2.2.2.2
   simpa [middle,JW,HA] using hh
 have hQs:AMK.Small Q:=by
   refine ⟨hSQ.trans hpSmall.2.2.2,?_⟩
   intro d hd
   have hh:=hn d hd
   exact ⟨hh.2.2.1.trans hpSmall.1,hh.2.2.2.2.trans hpSmall.2.1,hh.2.1.trans hpSmall.2.2.1⟩
 have hc:=hb.1
 rw [heq,weight_mul codeWeights _ _ (pow_ne_zero _ hJ.ne_zero) hQ,weight_pow codeWeights J hJ.ne_zero] at hc
 have henu:e*weightedTotalDegree codeWeights J≤p.C:=by omega
 have hD:p.C-e*weightedTotalDegree codeWeights J+e*weightedTotalDegree codeWeights J=n*181235:=by
   rw [Nat.sub_add_cancel henu,hpC]
 rcases AMK.FIN nodes P J T Q hJ.ne_zero e m n
     (weightedTotalDegree codeWeights J) (p.C-e*weightedTotalDegree codeWeights J) heq hjet
     hms hJs hQs hJne hroot rfl hD hcode with hdiv | hsmall
 · have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
   obtain ⟨SQ,hSQP,hSQd⟩:=EKS.FGS P.F p.T hFT P.rdegree hchar Q hQ
     hQs.1 hTQ hdiv
   have hcop:IsRelPrime SJ.P SQ.P:=by
     rw [hSJ,hSQP]
     exact hJ.isRelPrime_iff_not_dvd.mpr hnot
   have hJF:=_Q23 J a ha
   rw [←hSJ] at hJF
   have hQF:=FBA Q p.B p.U p.T p.S hBQ hUQ hTQ hSQ
   rw [←hSQP] at hQF
   have hbnd:=AHM P SZ SJ SQ z hZ hZFT hk hg hcop 1
     (by decide) (by decide) hSJd hSQd _ _ hJF hQF hgeo.1 hgeo.2.1
   have hh:=hbnd.trans (max_le hidentity hgeo.2.2)
   omega
 · omega
end
end DDV

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace XU
open MvPolynomial CW DJ XB
open DX HZ IM
open CB DC BD
open DU EF GF
open BX DP
open HI LV DR BH
open RCN095 RCN234 RCN156 ER
open FF ZGL
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]

theorem packet_count {t y r:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (p:Parameters) (hp:Shape p) (Kdim:ℕ) (hd:Dimension p Kdim)
 (hpSmall:p.B≤256∧p.U≤512∧p.L≤4096∧p.s≤64)
 (hFT:p.L<wt AT P.F)
 (J:CW.Poly (K:=K)) (hJ:Irreducible J) (a:DR.Box) (ha:Contains a (point J))
 (m:ℕ) (hms:m≤J.degreeOf 1) (hJs:AMK.Small J)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (SJ SZ:Source P.F) (hSJ:SJ.P=J) (hSJd:1≤SJ.d)
 (z:Degrees) (hZ:Fits SZ z) (hZFT:z.T<wt AT P.F)
 (hk:z.k<2130706433) (hg:Gates t y r (z.B-2*z.n0) (z.U-z.n0) (z.T-z.n0))
 (cap:ℕ) (hcap:4000000000000000≤cap)
 (hidentity:MG t y r≤cap)
 (hgeo:flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
   flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
   pairCost z 1 (ownerFlag a) (flag p.B p.U p.L p.s) t y r+leading z t y r≤cap)

 (N:ℕ) (hstop:DA.Impossible (caps p) {powerBox p a m with q:=N})
 (hband:(∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<Kdim):
 P.seeds.card≤cap:=by
 classical
 by_contra hnot
 have hlarge:cap<P.seeds.card:=Nat.lt_of_not_ge hnot
 obtain ⟨V,hV,hv,hb,hjet⟩:=DVF p hp Kdim hd nodes P.u0 P.u1 hN
 letI:Module.Finite K V:=hV
 have hbounds:=fun Q hQ=>CTV p hp Q (hb Q hQ)
 have hcover:DA.Covers (powerBox p a m) J:=by
   exact ⟨ha.2.2.1,ha.2.2.2.1,ha.1,ha.2.2.2.2.1,ha.2.2.2.2.2.2.1⟩
 have hlow: ∀e<N,∀(T Q:CW.Poly (K:=K)),T∈V→T=J^e*Q→Q≠0→
   weightedTotalDegree codeWeights Q<(caps p).C-e*weightedTotalDegree codeWeights J-e*m*50166→J∣Q:=by
   intro e he T Q hT heq hQ hcode
   exact DDV.GHY nodes P (caps p) p.m rfl hpSmall hFT J hJ a ha m hms hJs
     hJne hroot SJ SZ hSJ hSJd z hZ hZFT hk hg cap hcap hlarge hidentity hgeo
     e T Q heq hQ (hbounds T hT) (hjet T hT) hcode
 have hdim:=ZZ.telescope (caps p) (powerBox p a m) m N V hbounds J hJ.ne_zero hcover hlow
 have hz:=ZZ.EVH (caps p) (powerBox p a m) N V hbounds J hJ.ne_zero hcover hstop
 rw [hz] at hdim
 simp only [finrank_bot,add_zero] at hdim
 omega

end
end XU

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AUA
open FF ZGL
open LV BH HI ZZ
open scoped BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def p:Parameters:=⟨51,400,23,11,70,0,1⟩

theorem shape:Shape p:=by constructor<;>decide+kernel
theorem middle_p (h:ℕ) (hh:h≤11):70≤(p.cutoff h+23-1)/131071:=by
 interval_cases h<;>decide+kernel
theorem coefficients:AM.AW p.cutoff 131071 400 23 11 70=13525111441855:=by decide+kernel
theorem rank:AR.rankBound 51 400 23 11 70=51397405:=by decide+kernel
theorem dimension:Dimension p 51590105535:=by
 exact AZ p 51590105535 13525111441855 51397405 (by decide) (by decide) (by decide) (by decide) (by decide) middle_p coefficients rank (by decide)


end AUA

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BWK
open FF ZGL
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def p314:Parameters:=⟨51,314,23,11,70,0,1⟩
theorem shape314:Shape p314:=by constructor<;>decide+kernel
theorem middle314 (h:ℕ) (hh:h≤11):70≤(p314.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem GGH:AM.AW p314.cutoff 131071 314 23 11 70=10387660139831:=by decide+kernel
theorem rank314:AR.rankBound 51 314 23 11 70=39625725:=by decide+kernel
theorem dimension314:Dimension p314 14085431:=by
 exact AZ p314 14085431 10387660139831 39625725 (by decide) (by decide) (by decide) (by decide) (by decide) middle314 GGH rank314 (by decide)

def p600:Parameters:=⟨51,600,23,11,70,0,1⟩
theorem shape600:Shape p600:=by constructor<;>decide+kernel
theorem middle600 (h:ℕ) (hh:h≤11):70≤(p600.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem GIT:AM.AW p600.cutoff 131071 600 23 11 70=20821509818655:=by decide+kernel
theorem rank600:AR.rankBound 51 600 23 11 70=78773405:=by decide+kernel
theorem dimension600:Dimension p600 171534338335:=by
 exact AZ p600 171534338335 20821509818655 78773405 (by decide) (by decide) (by decide) (by decide) (by decide) middle600 GIT rank600 (by decide)

def p1000:Parameters:=⟨51,1000,23,11,70,0,1⟩
theorem shape1000:Shape p1000:=by constructor<;>decide+kernel
theorem middle1000 (h:ℕ) (hh:h≤11):70≤(p1000.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem GDB:AM.AW p1000.cutoff 131071 1000 23 11 70=35414306572255:=by decide+kernel
theorem rank1000:AR.rankBound 51 1000 23 11 70=133525405:=by decide+kernel
theorem GXD:Dimension p1000 411422803935:=by
 exact AZ p1000 411422803935 35414306572255 133525405 (by decide) (by decide) (by decide) (by decide) (by decide) middle1000 GDB rank1000 (by decide)

def profile (i:Fin 3):Parameters:=match i.val with
 | 0=>AUA.p
 | 1=>p600
 | _=>p1000
def kernel (i:Fin 3):ℕ:=match i.val with
 | 0=>51590105535
 | 1=>171534338335
 | _=>411422803935
theorem shape (i:Fin 3):Shape (profile i):=by fin_cases i;exact AUA.shape;exact shape600;exact shape1000
theorem dimension (i:Fin 3):Dimension (profile i) (kernel i):=by fin_cases i;exact AUA.dimension;exact dimension600;exact GXD
end BWK

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ACX
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF
open HI LV BH DR
open FF ZGL BWK
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
instance (p:DA.SourceCaps) (a:DA.OwnerBox):
 Decidable (DA.Impossible p a):=by unfold DA.Impossible;infer_instance

def pricing (fixed:Degrees) (a:DR.Box) (m:ℕ) (useOwner:Bool):=if useOwner then ownerZ a m else fixed

def BandValid (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (N:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 0<m∧m≤a.slo∧2*a.slo≤a.bhi∧
 a.shi≤64∧a.bhi≤256∧a.uhi≤512∧a.thi≤4096∧a.thi<low∧p.L<low∧
 SN.Common z low t y r∧MG t y r≤cap∧
 DA.Impossible (caps p) {powerBox p a m with q:=N}∧
 (∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<kernel i∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 pairCost z 1 (ownerFlag a) (flag p.B p.U p.L p.s) t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool) (N:ℕ):Decidable (BandValid fixed a m low t y r cap i useOwner N):=by
 unfold BandValid SN.Common Gates;infer_instance

def Valid (fixed:Degrees) (m low t y r cap:ℕ) (a:DR.Box):Prop:=
 BH.check .native fixed a m low t y r cap=true∨
 ∃i useOwner N,BandValid fixed a m low t y r cap i useOwner N

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem CPT {t y r low cap m:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (SZ:Source P.F) (fixed:Degrees) (hFixed:Fits SZ fixed)
 (hFT:low≤wt AT P.F) (hcap:4000000000000000≤cap)
 (J:DX.Poly (K:=K)) (hJ:Irreducible J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (i:Fin 3) (useOwner:Bool) (N:ℕ) (hc:BandValid fixed a m low t y r cap i useOwner N):
 P.seeds.card≤cap:=by
 classical
 obtain ⟨hm,hms,h2,hs,hb,hu,ht,haf,hpf,hcommon,hid,hstop,hband,hz,huy,hgeo⟩:=hc
 have hsmall:AMK.Small J:=by
   refine ⟨ha.2.1.trans hs,?_⟩
   intro d hd
   have hB:=(le_weightedTotalDegree slopeWeights hd).trans (ha.2.2.2.1.trans hb)
   have hU:=(le_weightedTotalDegree HA hd).trans (ha.2.2.2.2.2.1.trans hu)
   have hT:=(le_weightedTotalDegree totalWeights hd).trans (ha.2.2.2.2.2.2.2.trans ht)
   simp only [JW,slopeWeights,HA,totalWeights] at hB hU hT
   norm_num at hB hU hT
   exact ⟨by omega,by omega,by omega⟩
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hpower:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS J).map (carrierMap P.F):=
   (Polynomial.le_rootMultiplicity_iff hJne).mp (by rw [hroot];omega)
 obtain ⟨SJ,hSJ,hSJd⟩:=ZD.UN P.F a.thi
   (haf.trans_le hFT) P.rdegree hchar J hJ.ne_zero ha.2.2.2.2.2.2.2 1 (by decide) hpower
 have hpricing: ∃S:Source P.F,Fits S (pricing fixed a m useOwner):=by
   cases useOwner with
   | false=>exact ⟨SZ,hFixed⟩
   | true=>exact owner_source P J a m hm ha hms h2 hroot
 obtain ⟨S,hS⟩:=hpricing
 have hpSmall:(profile i).B≤256∧(profile i).U≤512∧(profile i).L≤4096∧(profile i).s≤64:=by
   fin_cases i<;>decide
 exact XU.packet_count nodes hN P (profile i) (shape i) (kernel i) (dimension i)
   hpSmall (hpf.trans_le hFT) J hJ a ha m (hms.trans ha.1) hsmall hJne hroot SJ S hSJ hSJd
   (pricing fixed a m useOwner) hS (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
   cap hcap hid ⟨hz,huy,hgeo⟩ N hstop hband

end
end ACX

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace PA
open DR (Box Point Contains Empty lower upper EQB)
set_option autoImplicit false

def Admissible (m:ℕ) (p:Point):Prop:=
 m≤p.s∧1≤p.s∧2*p.s≤p.b∧p.s≤p.u∧p.b≤p.u+p.s∧p.u≤p.t

def step (m:ℕ) (a:Box):Box:=
 let sl:=max (max (max a.slo m) 1) (a.blo-a.uhi)
 let sh:=min a.shi (a.bhi/2)
 let bl:=max a.blo (2*sl)
 let bh:=min a.bhi (a.uhi+sh)
 let ul:=max (max a.ulo sl) (bl-sh)
 let uh:=min a.uhi a.thi
 let tl:=max a.tlo ul
 ⟨sl,sh,bl,bh,ul,uh,tl,a.thi⟩

def normalize (m:ℕ):ℕ→Box→Box
 | 0,a=>a
 | n+1,a=>normalize m n (step m a)

theorem DVI (m:ℕ) (a:Box) (p:Point)
 (ha:Admissible m p) (hp:Contains a p):Contains (step m a) p:=by
 unfold Admissible Contains at*
 dsimp only [step]
 omega

theorem ATG (m n:ℕ) (a:Box) (p:Point)
 (ha:Admissible m p) (hp:Contains a p):Contains (normalize m n a) p:=by
 induction n generalizing a with
 | zero=>exact hp
 | succ n ih=>exact ih (step m a) (DVI m a p ha hp)

def Covered (m:ℕ) (valid:Box→Prop) (a:Box):Prop:=
 ∀p,Admissible m p→Contains a p→ ∃b,valid b∧Contains b p

theorem covered_leaf (m:ℕ) (valid:Box→Prop) (a:Box) (h:valid a):Covered m valid a:=by
 intro p _ hp
 exact ⟨a,h,hp⟩

theorem AO (m:ℕ) (valid:Box→Prop) (a b:Box)
 (he:normalize m 8 a=b) (h:Covered m valid b):Covered m valid a:=by
 intro p ha hp
 apply h p ha
 rw [←he]
 exact ATG m 8 a p ha hp

theorem BJ (m:ℕ) (valid:Box→Prop) (a:Box) (axis:Fin 4) (v:ℕ)
 (hl:Covered m valid (lower a axis v)) (hh:Covered m valid (upper a axis v)):Covered m valid a:=by
 intro p ha hp
 rcases EQB a p axis v hp with hp | hp
 · exact hl p ha hp
 · exact hh p ha hp
end PA

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BN
open DR (Box Contains lower upper)
open HI ACX PA
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def fixed:Degrees:=⟨53,177,3666,6,8⟩
abbrev valid (m:ℕ):=ACX.Valid fixed m 3681 3800 58 13 273900000000000000

theorem bc1_12:BH.check .native fixed ⟨1,3,2,8,1,5,1,5⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_13:BandValid fixed ⟨4,5,8,10,4,5,4,5⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 3:=by decide+kernel







theorem bc1_15:BH.check .native fixed ⟨1,3,2,8,1,5,6,10⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_16:BandValid fixed ⟨4,5,8,10,4,5,6,10⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 3:=by decide+kernel









theorem bc1_18:BH.check .native fixed ⟨1,4,2,8,6,10,6,10⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_19:BandValid fixed ⟨1,5,9,15,6,10,6,10⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel









theorem bc1_20:BandValid fixed ⟨6,10,12,20,6,10,6,10⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_24:BH.check .native fixed ⟨1,3,2,8,1,5,11,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_25:BandValid fixed ⟨4,5,8,10,4,5,11,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 3:=by decide+kernel







theorem bc1_27:BH.check .native fixed ⟨1,4,2,8,6,10,11,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_28:BandValid fixed ⟨1,5,9,15,6,10,11,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel









theorem bc1_29:BandValid fixed ⟨6,10,12,20,6,10,11,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel









theorem bc1_34:BH.check .native fixed ⟨1,2,2,4,11,20,11,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_38:BH.check .native fixed ⟨1,1,5,7,11,15,11,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_41:BH.check .native fixed ⟨1,1,5,6,16,18,16,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_42:BandValid fixed ⟨1,1,5,6,19,20,19,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_43:BandValid fixed ⟨1,1,7,7,16,20,16,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel









theorem bc1_44:BH.check .native fixed ⟨2,2,5,7,11,20,11,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel







theorem bc1_45:BH.check .native fixed ⟨3,3,6,7,11,20,11,20⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel









theorem bc1_46:BandValid fixed ⟨1,3,8,12,11,20,11,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_47:BandValid fixed ⟨4,6,8,12,11,20,11,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_48:BandValid fixed ⟨1,11,13,23,11,20,11,20⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_53:BH.check .native fixed ⟨1,3,2,8,1,5,21,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_54:BandValid fixed ⟨4,5,8,10,4,5,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 3:=by decide+kernel







theorem bc1_56:BH.check .native fixed ⟨1,4,2,8,6,10,21,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_57:BandValid fixed ⟨1,5,9,15,6,10,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel









theorem bc1_58:BandValid fixed ⟨6,10,12,20,6,10,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_63:BH.check .native fixed ⟨1,2,2,4,11,20,21,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_68:BH.check .native fixed ⟨1,1,5,7,11,15,21,30⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_72:BH.check .native fixed ⟨1,1,5,6,16,18,21,25⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_73:BandValid fixed ⟨1,1,5,6,19,20,21,25⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_74:BandValid fixed ⟨1,1,7,7,16,20,21,25⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_77:BH.check .native fixed ⟨1,1,5,6,16,18,26,30⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_78:BandValid fixed ⟨1,1,5,6,19,20,26,30⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_79:BandValid fixed ⟨1,1,7,7,16,20,26,30⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel











theorem bc1_81:BH.check .native fixed ⟨1,1,5,7,11,15,31,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_85:BH.check .native fixed ⟨1,1,5,6,16,18,31,35⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_86:BandValid fixed ⟨1,1,5,6,19,20,31,35⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_88:BH.check .native fixed ⟨1,1,5,6,16,18,36,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_89:BandValid fixed ⟨1,1,5,6,19,20,36,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel









theorem bc1_90:BandValid fixed ⟨1,1,7,7,16,20,31,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel











theorem bc1_91:BH.check .native fixed ⟨2,2,5,7,11,20,21,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel







theorem bc1_92:BH.check .native fixed ⟨3,3,6,7,11,20,21,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel









theorem bc1_93:BandValid fixed ⟨1,3,8,12,11,20,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_94:BandValid fixed ⟨4,6,8,12,11,20,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_95:BandValid fixed ⟨1,11,13,23,11,20,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel











theorem bc1_105:BH.check .native fixed ⟨1,1,2,2,21,30,21,30⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_107:BH.check .native fixed ⟨1,1,3,3,21,25,21,30⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_108:BandValid fixed ⟨1,1,3,3,26,30,26,30⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel









theorem bc1_110:BH.check .native fixed ⟨1,1,2,2,21,30,31,40⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_111:BandValid fixed ⟨1,1,3,3,21,30,31,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel









theorem bc1_112:BandValid fixed ⟨1,1,2,3,31,40,31,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_113:BandValid fixed ⟨1,1,4,4,21,40,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ false 4:=by decide+kernel







theorem bc1_114:BandValid fixed ⟨2,2,4,4,21,40,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_115:BandValid fixed ⟨1,3,5,7,21,40,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ false 4:=by decide+kernel







theorem bc1_116:BandValid fixed ⟨1,3,8,12,21,40,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_117:BandValid fixed ⟨4,6,8,12,21,40,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_118:BandValid fixed ⟨1,11,13,23,21,40,21,40⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_125:BH.check .native fixed ⟨1,3,2,8,1,5,41,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_126:BandValid fixed ⟨4,5,8,10,4,5,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_128:BH.check .native fixed ⟨1,4,2,8,6,9,41,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_129:BandValid fixed ⟨1,5,9,14,6,9,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel









theorem bc1_130:BandValid fixed ⟨6,9,12,18,6,9,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_135:BH.check .native fixed ⟨1,2,2,4,10,18,41,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_140:BH.check .native fixed ⟨1,1,5,7,10,14,41,60⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_143:BH.check .native fixed ⟨1,1,5,6,15,18,41,50⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_144:BandValid fixed ⟨1,1,7,7,15,18,41,50⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_146:BH.check .native fixed ⟨1,1,5,6,15,18,51,60⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_147:BandValid fixed ⟨1,1,7,7,15,18,51,60⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel











theorem bc1_149:BH.check .native fixed ⟨1,1,5,7,10,14,61,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_151:BH.check .native fixed ⟨1,1,5,6,15,18,61,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_152:BandValid fixed ⟨1,1,7,7,15,18,61,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel











theorem bc1_153:BH.check .native fixed ⟨2,2,5,7,10,18,41,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel







theorem bc1_154:BH.check .native fixed ⟨3,3,6,7,10,18,41,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel









theorem bc1_155:BandValid fixed ⟨1,3,8,12,10,18,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_156:BandValid fixed ⟨4,6,8,12,10,18,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_157:BandValid fixed ⟨1,11,13,23,10,18,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_166:BH.check .native fixed ⟨1,1,2,3,19,27,41,60⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_167:BandValid fixed ⟨1,1,2,3,28,35,41,60⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_169:BH.check .native fixed ⟨1,1,2,3,19,27,61,79⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_170:BandValid fixed ⟨1,1,2,3,28,35,61,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel









theorem bc1_175:BH.check .native fixed ⟨1,1,4,4,19,23,41,50⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_176:BandValid fixed ⟨1,1,4,4,24,27,41,50⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_178:BH.check .native fixed ⟨1,1,4,4,19,23,51,60⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_179:BandValid fixed ⟨1,1,4,4,24,27,51,60⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel









theorem bc1_180:BandValid fixed ⟨1,1,4,4,28,35,41,60⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_181:BandValid fixed ⟨1,1,4,4,19,35,61,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel









theorem bc1_184:BH.check .native fixed ⟨2,2,4,4,19,27,41,60⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_185:BandValid fixed ⟨2,2,4,4,28,35,41,60⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_186:BandValid fixed ⟨2,2,4,4,19,35,61,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel









theorem bc1_187:BandValid fixed ⟨1,3,5,7,19,35,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ false 4:=by decide+kernel







theorem bc1_188:BandValid fixed ⟨1,3,8,12,19,35,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_189:BandValid fixed ⟨4,6,8,12,19,35,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_190:BandValid fixed ⟨1,11,13,23,19,35,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_191:BandValid fixed ⟨1,11,2,23,36,70,41,79⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 2:=by decide+kernel









theorem bc1_198:BH.check .native fixed ⟨1,3,2,8,1,5,80,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_199:BandValid fixed ⟨4,5,8,10,4,5,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_201:BH.check .native fixed ⟨1,4,2,8,6,9,80,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_202:BandValid fixed ⟨1,5,9,14,6,9,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel









theorem bc1_203:BandValid fixed ⟨6,9,12,18,6,9,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_208:BH.check .native fixed ⟨1,2,2,4,10,18,80,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_213:BH.check .native fixed ⟨1,1,5,7,10,14,80,118⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_217:BH.check .native fixed ⟨1,1,5,6,15,18,80,89⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_219:BH.check .native fixed ⟨1,1,5,5,15,18,90,99⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_220:BandValid fixed ⟨1,1,6,6,15,18,90,99⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel









theorem bc1_221:BandValid fixed ⟨1,1,7,7,15,18,80,99⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_224:BH.check .native fixed ⟨1,1,5,5,15,18,100,118⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_225:BandValid fixed ⟨1,1,6,6,15,18,100,118⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_226:BandValid fixed ⟨1,1,7,7,15,18,100,118⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel











theorem bc1_229:BH.check .native fixed ⟨1,1,5,6,10,14,119,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_230:BandValid fixed ⟨1,1,7,7,10,14,119,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_231:BandValid fixed ⟨1,1,5,7,15,18,119,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 5:=by decide+kernel









theorem bc1_232:BH.check .native fixed ⟨2,2,5,7,10,18,80,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel







theorem bc1_233:BH.check .native fixed ⟨3,3,6,7,10,18,80,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel









theorem bc1_234:BandValid fixed ⟨1,3,8,12,10,18,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_235:BandValid fixed ⟨4,6,8,12,10,18,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_236:BandValid fixed ⟨1,11,13,23,10,18,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_245:BH.check .native fixed ⟨1,1,2,3,19,27,80,118⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_246:BandValid fixed ⟨1,1,2,3,28,35,80,118⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc1_248:BH.check .native fixed ⟨1,1,2,3,19,27,119,157⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_249:BandValid fixed ⟨1,1,2,3,28,35,119,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel









theorem bc1_250:BandValid fixed ⟨1,1,4,4,19,35,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_251:BandValid fixed ⟨2,2,4,4,19,35,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 4:=by decide+kernel







theorem bc1_252:BandValid fixed ⟨1,3,5,7,19,35,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ false 4:=by decide+kernel







theorem bc1_253:BandValid fixed ⟨1,3,8,12,19,35,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_254:BandValid fixed ⟨4,6,8,12,19,35,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 3:=by decide+kernel







theorem bc1_255:BandValid fixed ⟨1,11,13,23,19,35,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_256:BandValid fixed ⟨1,11,2,23,36,70,80,157⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_264:BH.check .native fixed ⟨1,3,2,6,1,3,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_266:BH.check .native fixed ⟨1,2,2,5,4,5,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_268:BH.check .native fixed ⟨1,2,6,7,4,5,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_269:BH.check .native fixed ⟨3,3,6,8,4,5,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel











theorem bc1_270:BandValid fixed ⟨4,5,8,10,4,5,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 3:=by decide+kernel







theorem bc1_274:BH.check .native fixed ⟨1,2,2,5,6,9,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_275:BandValid fixed ⟨1,2,6,8,6,9,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_276:BandValid fixed ⟨3,4,6,8,6,9,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_277:BandValid fixed ⟨1,5,9,14,6,9,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 3:=by decide+kernel









theorem bc1_278:BandValid fixed ⟨6,9,12,18,6,9,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_283:BH.check .native fixed ⟨1,2,2,4,10,18,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_290:BH.check .native fixed ⟨1,1,5,6,10,14,158,197⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_291:BandValid fixed ⟨1,1,7,7,10,14,158,197⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_292:BandValid fixed ⟨1,1,5,7,10,14,198,236⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 3:=by decide+kernel







theorem bc1_293:BandValid fixed ⟨1,1,5,7,15,18,158,236⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_294:BandValid fixed ⟨1,1,5,7,10,18,237,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_295:BH.check .native fixed ⟨2,2,5,7,10,18,158,314⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel







theorem bc1_296:BandValid fixed ⟨3,3,6,7,10,18,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel









theorem bc1_297:BandValid fixed ⟨1,3,8,12,10,18,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 3:=by decide+kernel







theorem bc1_298:BandValid fixed ⟨4,6,8,12,10,18,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 3:=by decide+kernel







theorem bc1_299:BandValid fixed ⟨1,11,13,23,10,18,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_309:BH.check .native fixed ⟨1,1,2,2,19,27,158,236⟩ 1 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc1_310:BandValid fixed ⟨1,1,3,3,19,27,158,236⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_311:BandValid fixed ⟨1,1,2,3,28,35,158,236⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 3:=by decide+kernel







theorem bc1_312:BandValid fixed ⟨1,1,2,3,19,35,237,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc1_313:BandValid fixed ⟨1,1,4,4,19,35,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_314:BandValid fixed ⟨2,2,4,4,19,35,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 4:=by decide+kernel







theorem bc1_315:BandValid fixed ⟨1,3,5,7,19,35,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 4:=by decide+kernel







theorem bc1_316:BandValid fixed ⟨1,3,8,12,19,35,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 3:=by decide+kernel







theorem bc1_317:BandValid fixed ⟨4,6,8,12,19,35,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 3:=by decide+kernel







theorem bc1_318:BandValid fixed ⟨1,11,13,23,19,35,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc1_319:BandValid fixed ⟨1,11,2,23,36,70,158,314⟩ 1 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_328:BH.check .native fixed ⟨2,6,4,17,2,11,2,11⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_329:BandValid fixed ⟨7,11,14,22,7,11,7,11⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel







theorem bc2_331:BH.check .native fixed ⟨2,6,4,17,2,11,12,21⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_332:BandValid fixed ⟨7,11,14,22,7,11,12,21⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel









theorem bc2_334:BH.check .native fixed ⟨2,6,4,13,12,21,12,21⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_335:BandValid fixed ⟨2,11,14,23,12,21,12,21⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 2:=by decide+kernel









theorem bc2_338:BH.check .native fixed ⟨2,6,4,17,2,11,22,41⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_339:BandValid fixed ⟨7,11,14,22,7,11,22,41⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel







theorem bc2_341:BH.check .native fixed ⟨2,6,4,13,12,21,22,41⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_342:BandValid fixed ⟨2,11,14,23,12,21,22,41⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 2:=by decide+kernel











theorem bc2_345:BH.check .native fixed ⟨2,4,4,8,22,41,22,41⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_346:BandValid fixed ⟨2,6,9,13,22,41,22,41⟩ 2 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 3:=by decide+kernel







theorem bc2_347:BandValid fixed ⟨2,11,14,23,22,41,22,41⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_352:BH.check .native fixed ⟨2,6,4,16,2,10,42,80⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_353:BandValid fixed ⟨7,10,14,20,7,10,42,80⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel







theorem bc2_355:BH.check .native fixed ⟨2,6,4,13,11,19,42,80⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_356:BandValid fixed ⟨2,11,14,23,11,19,42,80⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 2:=by decide+kernel









theorem bc2_359:BH.check .native fixed ⟨2,4,4,8,20,36,42,80⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_360:BandValid fixed ⟨2,6,9,13,20,36,42,80⟩ 2 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 3:=by decide+kernel







theorem bc2_361:BandValid fixed ⟨2,11,14,23,20,36,42,80⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_362:BandValid fixed ⟨2,11,4,23,37,70,42,80⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 2:=by decide+kernel









theorem bc2_367:BH.check .native fixed ⟨2,6,4,16,2,10,81,158⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_368:BandValid fixed ⟨7,10,14,20,7,10,81,158⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc2_370:BH.check .native fixed ⟨2,6,4,13,11,19,81,158⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_371:BandValid fixed ⟨2,11,14,23,11,19,81,158⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_374:BH.check .native fixed ⟨2,4,4,8,20,36,81,158⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_375:BandValid fixed ⟨2,6,9,13,20,36,81,158⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc2_376:BandValid fixed ⟨2,11,14,23,20,36,81,158⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_378:BandValid fixed ⟨2,6,4,13,37,70,81,158⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ false 2:=by decide+kernel





theorem bc2_379:BandValid fixed ⟨2,11,14,23,37,70,81,158⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel











theorem bc2_384:BH.check .native fixed ⟨2,6,4,16,2,10,159,314⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_385:BandValid fixed ⟨7,10,14,20,7,10,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel







theorem bc2_387:BH.check .native fixed ⟨2,6,4,13,11,19,159,314⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_388:BandValid fixed ⟨2,11,14,23,11,19,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_391:BH.check .native fixed ⟨2,4,4,8,20,36,159,314⟩ 2 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc2_392:BandValid fixed ⟨2,6,9,13,20,36,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 3:=by decide+kernel







theorem bc2_393:BandValid fixed ⟨2,11,14,23,20,36,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel









theorem bc2_396:BandValid fixed ⟨2,4,4,8,37,70,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel





theorem bc2_397:BandValid fixed ⟨2,6,9,13,37,70,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel







theorem bc2_398:BandValid fixed ⟨2,11,14,23,37,70,159,314⟩ 2 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ false 2:=by decide+kernel











theorem bc3_403:BH.check .native fixed ⟨3,11,6,23,3,22,3,41⟩ 3 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc3_405:BH.check .native fixed ⟨3,7,6,14,23,41,23,41⟩ 3 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc3_406:BandValid fixed ⟨3,11,15,23,23,41,23,41⟩ 3 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel









theorem bc3_408:BH.check .native fixed ⟨3,11,6,23,3,36,42,80⟩ 3 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc3_410:BandValid fixed ⟨3,7,6,14,37,70,42,80⟩ 3 3681 3800 58 13 273900000000000000 ⟨2,by decide⟩ true 2:=by decide+kernel





theorem bc3_411:BandValid fixed ⟨3,11,15,23,37,70,42,80⟩ 3 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel











theorem bc3_413:BH.check .native fixed ⟨3,11,6,23,3,36,81,158⟩ 3 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc3_415:BandValid fixed ⟨3,7,6,14,37,70,81,158⟩ 3 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel





theorem bc3_416:BandValid fixed ⟨3,11,15,23,37,70,81,158⟩ 3 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel











theorem bc3_419:BH.check .native fixed ⟨3,11,6,23,3,19,159,314⟩ 3 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc3_421:BH.check .native fixed ⟨3,7,6,14,20,36,159,314⟩ 3 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc3_422:BandValid fixed ⟨3,11,15,23,20,36,159,314⟩ 3 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel









theorem bc3_424:BandValid fixed ⟨3,7,6,14,37,70,159,314⟩ 3 3681 3800 58 13 273900000000000000 ⟨1,by decide⟩ true 2:=by decide+kernel





theorem bc3_425:BandValid fixed ⟨3,11,15,23,37,70,159,314⟩ 3 3681 3800 58 13 273900000000000000 ⟨0,by decide⟩ true 2:=by decide+kernel











theorem bc4_426:BH.check .native fixed ⟨4,11,8,23,4,70,4,314⟩ 4 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc5_427:BH.check .native fixed ⟨5,11,10,23,5,70,5,314⟩ 5 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc6_428:BH.check .native fixed ⟨6,11,12,23,6,70,6,314⟩ 6 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc7_429:BH.check .native fixed ⟨7,11,14,23,7,70,7,314⟩ 7 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc8_430:BH.check .native fixed ⟨8,11,16,23,8,70,8,314⟩ 8 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc9_431:BH.check .native fixed ⟨9,11,18,23,9,70,9,314⟩ 9 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc10_432:BH.check .native fixed ⟨10,11,20,23,10,70,10,314⟩ 10 3681 3800 58 13 273900000000000000=true:=by decide+kernel





theorem bc11_433:BH.check .native fixed ⟨11,11,22,23,11,70,11,314⟩ 11 3681 3800 58 13 273900000000000000=true:=by decide+kernel





def root (m:ℕ):Box:=⟨max 1 m,11,2*max 1 m,23,0,70,0,314⟩

end BN

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ATV
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF NX
open GZ ME LK
open HI LV BH DR
open FF ZGL ON YY
open BWK BN
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {t y r cap low:ℕ}

theorem from_sources (fixed' :Degrees) (hLow:1700<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 [Fact (Irreducible P.F)] (hFT:low≤wt AT P.F)
 (S SZ:Source P.F) (hS:Profile S 23 70 314 11 0 1) (hZ:Fits SZ fixed')
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤11→PA.Covered m
   (ACX.Valid fixed' m low t y r cap) (root m)):
 P.seeds.card≤cap:=by
 classical
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hST:S.T=314:=hS.2.2.1
 have hs:=ADG P.F S (by rw [hST];omega) P.rdegree hchar
   (by rw [hS.2.2.2.2.1];decide)
 have hpow:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣QC (carrierMap P.F) S.P:=by
   change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS S.P).map (carrierMap P.F)
   simpa only [Source.d,hS.2.2.2.2.1,Nat.zero_add] using hs.2
 have hroot:NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0:=by
   exact Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
 obtain ⟨J,hJ,hJS,hJroot,_⟩:=ADQ
   (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
 obtain ⟨hJne,hm,hms,hJb,hJu,hJt,hJs⟩:=AVL P.F S (by rw [hST];omega) J hJ hJS hJroot
 rw [hS.1] at hJb
 rw [hS.2.1] at hJu
 rw [hS.2.2.1] at hJt
 rw [hS.2.2.2.1] at hJs
 let m:=multiplicity P.F J
 have hn:=_Q15 J
 have horder:1≤order J:=Nat.succ_le_of_lt (hm.trans_le hms)
 have hadm:PA.Admissible m (point J):=
   ⟨hms,horder,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
 have hx:Contains (root m) (point J):=by
   dsimp only [Contains,root,point]
   refine ⟨max_le horder hms,hJs,?_,hJb,Nat.zero_le _,hJu,Nat.zero_le _,hJt⟩
   have hh:=hn.2.2.1
   omega
 obtain ⟨a,hvalid,ha⟩:=hcov m hm (hms.trans hJs) (point J) hadm hx
 rcases hvalid with hc | ⟨i,useOwner,N,hc⟩
 · have hh:=BH.BLQ nodes hI P SZ fixed' hZ .native a m
     low cap hFT hLow (by omega) J hJ ha rfl hJne hc
   exact hh.trans (max_le hid le_rfl)
 · exact ACX.CPT nodes hI P SZ fixed' hZ hFT hcap
     J hJ a ha rfl hJne i useOwner N hc


theorem AKJ (fixed' :Degrees) (hLow:1700<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 (hFT:low≤wt AT P.F) (SZ:Source P.F) (hZ:Fits SZ fixed')
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤11→PA.Covered m
   (ACX.Valid fixed' m low t y r cap) (root m)):P.seeds.card≤cap:=by
 classical
 letI:Fact (Irreducible P.F):=⟨P.irreducible⟩
 rcases VT p314 shape314 14085431 (by decide) dimension314 nodes P.u0 P.u1 hI
     P.F P.irreducible (by change 314<_;omega) r y t (by have:=P.rlow;omega) (by have:=P.rlow;have:=P.ylow;omega) (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega)
     ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · exact (KY.helper_count p314 nodes P (by decide) (by decide) (by decide) (by decide) Q hQ).le.trans (by omega)
 exact from_sources fixed' hLow nodes hI P hFT S SZ hS hZ hcap hid hcov


end
end ATV

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ECZ
open ACX HI LV BH
open BWK EF GF RCN095 RCN234 RCN156
set_option autoImplicit false

def BandGeometry (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 SN.Common z low t y r∧MG t y r≤cap∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 pairCost z 1 (ownerFlag a) (flag p.B p.U p.L p.s) t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool):Decidable (BandGeometry fixed a m low t y r cap i useOwner):=by
 unfold BandGeometry SN.Common ER.Gates;infer_instance



def CQM (a:DR.Box) (m low t y r cap:ℕ):Prop:=
 SN.Common (ownerZ a m) low t y r∧
 nativeScalar (ownerZ a m) t y r/(3*(ownerZ a m).d)+leading (ownerZ a m) t y r≤cap
instance (a:DR.Box) (m low t y r cap:ℕ):
 Decidable (CQM a m low t y r cap):=by
 unfold CQM SN.Common ER.Gates;infer_instance




def DHJ (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool):Prop:=
 a.thi<low∧(profile i).L<low∧BandGeometry fixed a m low t y r cap i useOwner
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 3) (useOwner:Bool):Decidable (DHJ fixed a m low t y r cap i useOwner):=by
 unfold DHJ;infer_instance

theorem GVP (fixed fixed' :Degrees) (a:DR.Box) (m low t y r cap low' t' y' r' cap' :ℕ)
 (i:Fin 3) (useOwner:Bool) (N:ℕ)
 (hc:BandValid fixed a m low t y r cap i useOwner N)
 (hg:DHJ fixed' a m low' t' y' r' cap' i useOwner):
 BandValid fixed' a m low' t' y' r' cap' i useOwner N:=by
 obtain ⟨hm,hms,h2,hs,hb,hu,ht,_,_,_,_,hstop,hband,_,_,_⟩:=hc
 exact ⟨hm,hms,h2,hs,hb,hu,ht,hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,hstop,hband,
   hg.2.2.2.2.1,hg.2.2.2.2.2.1,hg.2.2.2.2.2.2⟩

def CME (a:DR.Box) (m low t y r cap:ℕ):Prop:=
 a.thi<low∧CQM a m low t y r cap
instance (a:DR.Box) (m low t y r cap:ℕ):
 Decidable (CME a m low t y r cap):=by unfold CME;infer_instance

theorem GIP (fixed fixed' :Degrees) (a:DR.Box) (m low t y r cap low' t' y' r' cap' :ℕ)
 (hc:check .native fixed a m low t y r cap=true)
 (hg:CME a m low' t' y' r' cap'):
 check .native fixed' a m low' t' y' r' cap'=true:=by
 simp only [check,Bool.and_eq_true,decide_eq_true_eq] at hc ⊢
 refine ⟨⟨hc.1.1,hc.1.2.1,hc.1.2.2.1,hc.1.2.2.2.1,hg.1,hc.1.2.2.2.2.2⟩,?_⟩
 simpa only [checkChoice,CQM,decide_eq_true_eq] using hg.2
end ECZ

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace JG
open DR (Box Contains lower upper)
open HI LV BH
open ACX ECZ PA
open BN (fixed root)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
structure Leaf where
 m:ℕ
 a:Box
 kind:Option (Fin 3 × Bool × ℕ)
def leaf:Fin 222→Leaf:= ![⟨1,⟨1,3,2,8,1,5,1,5⟩,none⟩,⟨1,⟨4,5,8,10,4,5,4,5⟩,some (⟨2,by decide⟩,true,3)⟩,⟨1,⟨1,3,2,8,1,5,6,10⟩,none⟩,⟨1,⟨4,5,8,10,4,5,6,10⟩,some (⟨2,by decide⟩,true,3)⟩,⟨1,⟨1,4,2,8,6,10,6,10⟩,none⟩,⟨1,⟨1,5,9,15,6,10,6,10⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨6,10,12,20,6,10,6,10⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,3,2,8,1,5,11,20⟩,none⟩,⟨1,⟨4,5,8,10,4,5,11,20⟩,some (⟨2,by decide⟩,true,3)⟩,⟨1,⟨1,4,2,8,6,10,11,20⟩,none⟩,⟨1,⟨1,5,9,15,6,10,11,20⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨6,10,12,20,6,10,11,20⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,2,2,4,11,20,11,20⟩,none⟩,⟨1,⟨1,1,5,7,11,15,11,20⟩,none⟩,⟨1,⟨1,1,5,6,16,18,16,20⟩,none⟩,⟨1,⟨1,1,5,6,19,20,19,20⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,7,7,16,20,16,20⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨2,2,5,7,11,20,11,20⟩,none⟩,⟨1,⟨3,3,6,7,11,20,11,20⟩,none⟩,⟨1,⟨1,3,8,12,11,20,11,20⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,11,20,11,20⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,11,13,23,11,20,11,20⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,3,2,8,1,5,21,40⟩,none⟩,⟨1,⟨4,5,8,10,4,5,21,40⟩,some (⟨2,by decide⟩,true,3)⟩,⟨1,⟨1,4,2,8,6,10,21,40⟩,none⟩,⟨1,⟨1,5,9,15,6,10,21,40⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨6,10,12,20,6,10,21,40⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,2,2,4,11,20,21,40⟩,none⟩,⟨1,⟨1,1,5,7,11,15,21,30⟩,none⟩,⟨1,⟨1,1,5,6,16,18,21,25⟩,none⟩,⟨1,⟨1,1,5,6,19,20,21,25⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,7,7,16,20,21,25⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,6,16,18,26,30⟩,none⟩,⟨1,⟨1,1,5,6,19,20,26,30⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,7,7,16,20,26,30⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,7,11,15,31,40⟩,none⟩,⟨1,⟨1,1,5,6,16,18,31,35⟩,none⟩,⟨1,⟨1,1,5,6,19,20,31,35⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,6,16,18,36,40⟩,none⟩,⟨1,⟨1,1,5,6,19,20,36,40⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,7,7,16,20,31,40⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨2,2,5,7,11,20,21,40⟩,none⟩,⟨1,⟨3,3,6,7,11,20,21,40⟩,none⟩,⟨1,⟨1,3,8,12,11,20,21,40⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,11,20,21,40⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,11,13,23,11,20,21,40⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,1,2,2,21,30,21,30⟩,none⟩,⟨1,⟨1,1,3,3,21,25,21,30⟩,none⟩,⟨1,⟨1,1,3,3,26,30,26,30⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,2,2,21,30,31,40⟩,none⟩,⟨1,⟨1,1,3,3,21,30,31,40⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,2,3,31,40,31,40⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨1,1,4,4,21,40,21,40⟩,some (⟨2,by decide⟩,false,4)⟩,⟨1,⟨2,2,4,4,21,40,21,40⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,3,5,7,21,40,21,40⟩,some (⟨2,by decide⟩,false,4)⟩,⟨1,⟨1,3,8,12,21,40,21,40⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,21,40,21,40⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨1,11,13,23,21,40,21,40⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,3,2,8,1,5,41,79⟩,none⟩,⟨1,⟨4,5,8,10,4,5,41,79⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,4,2,8,6,9,41,79⟩,none⟩,⟨1,⟨1,5,9,14,6,9,41,79⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨6,9,12,18,6,9,41,79⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,2,2,4,10,18,41,79⟩,none⟩,⟨1,⟨1,1,5,7,10,14,41,60⟩,none⟩,⟨1,⟨1,1,5,6,15,18,41,50⟩,none⟩,⟨1,⟨1,1,7,7,15,18,41,50⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,6,15,18,51,60⟩,none⟩,⟨1,⟨1,1,7,7,15,18,51,60⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,7,10,14,61,79⟩,none⟩,⟨1,⟨1,1,5,6,15,18,61,79⟩,none⟩,⟨1,⟨1,1,7,7,15,18,61,79⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨2,2,5,7,10,18,41,79⟩,none⟩,⟨1,⟨3,3,6,7,10,18,41,79⟩,none⟩,⟨1,⟨1,3,8,12,10,18,41,79⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,10,18,41,79⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,11,13,23,10,18,41,79⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,1,2,3,19,27,41,60⟩,none⟩,⟨1,⟨1,1,2,3,28,35,41,60⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,2,3,19,27,61,79⟩,none⟩,⟨1,⟨1,1,2,3,28,35,61,79⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,4,4,19,23,41,50⟩,none⟩,⟨1,⟨1,1,4,4,24,27,41,50⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,4,4,19,23,51,60⟩,none⟩,⟨1,⟨1,1,4,4,24,27,51,60⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,4,4,28,35,41,60⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,4,4,19,35,61,79⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨2,2,4,4,19,27,41,60⟩,none⟩,⟨1,⟨2,2,4,4,28,35,41,60⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨2,2,4,4,19,35,61,79⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,3,5,7,19,35,41,79⟩,some (⟨2,by decide⟩,false,4)⟩,⟨1,⟨1,3,8,12,19,35,41,79⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,19,35,41,79⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨1,11,13,23,19,35,41,79⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,11,2,23,36,70,41,79⟩,some (⟨1,by decide⟩,false,2)⟩,⟨1,⟨1,3,2,8,1,5,80,157⟩,none⟩,⟨1,⟨4,5,8,10,4,5,80,157⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,4,2,8,6,9,80,157⟩,none⟩,⟨1,⟨1,5,9,14,6,9,80,157⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨6,9,12,18,6,9,80,157⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,2,2,4,10,18,80,157⟩,none⟩,⟨1,⟨1,1,5,7,10,14,80,118⟩,none⟩,⟨1,⟨1,1,5,6,15,18,80,89⟩,none⟩,⟨1,⟨1,1,5,5,15,18,90,99⟩,none⟩,⟨1,⟨1,1,6,6,15,18,90,99⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,1,7,7,15,18,80,99⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,5,15,18,100,118⟩,none⟩,⟨1,⟨1,1,6,6,15,18,100,118⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,7,7,15,18,100,118⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,6,10,14,119,157⟩,none⟩,⟨1,⟨1,1,7,7,10,14,119,157⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,7,15,18,119,157⟩,some (⟨2,by decide⟩,true,5)⟩,⟨1,⟨2,2,5,7,10,18,80,157⟩,none⟩,⟨1,⟨3,3,6,7,10,18,80,157⟩,none⟩,⟨1,⟨1,3,8,12,10,18,80,157⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,10,18,80,157⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,11,13,23,10,18,80,157⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,1,2,3,19,27,80,118⟩,none⟩,⟨1,⟨1,1,2,3,28,35,80,118⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,2,3,19,27,119,157⟩,none⟩,⟨1,⟨1,1,2,3,28,35,119,157⟩,some (⟨1,by decide⟩,true,3)⟩,⟨1,⟨1,1,4,4,19,35,80,157⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨2,2,4,4,19,35,80,157⟩,some (⟨2,by decide⟩,true,4)⟩,⟨1,⟨1,3,5,7,19,35,80,157⟩,some (⟨2,by decide⟩,false,4)⟩,⟨1,⟨1,3,8,12,19,35,80,157⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,19,35,80,157⟩,some (⟨1,by decide⟩,false,3)⟩,⟨1,⟨1,11,13,23,19,35,80,157⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,11,2,23,36,70,80,157⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,3,2,6,1,3,158,314⟩,none⟩,⟨1,⟨1,2,2,5,4,5,158,314⟩,none⟩,⟨1,⟨1,2,6,7,4,5,158,314⟩,none⟩,⟨1,⟨3,3,6,8,4,5,158,314⟩,none⟩,⟨1,⟨4,5,8,10,4,5,158,314⟩,some (⟨0,by decide⟩,true,3)⟩,⟨1,⟨1,2,2,5,6,9,158,314⟩,none⟩,⟨1,⟨1,2,6,8,6,9,158,314⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨3,4,6,8,6,9,158,314⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,5,9,14,6,9,158,314⟩,some (⟨0,by decide⟩,false,3)⟩,⟨1,⟨6,9,12,18,6,9,158,314⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,2,2,4,10,18,158,314⟩,none⟩,⟨1,⟨1,1,5,6,10,14,158,197⟩,none⟩,⟨1,⟨1,1,7,7,10,14,158,197⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,7,10,14,198,236⟩,some (⟨0,by decide⟩,true,3)⟩,⟨1,⟨1,1,5,7,15,18,158,236⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,5,7,10,18,237,314⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨2,2,5,7,10,18,158,314⟩,none⟩,⟨1,⟨3,3,6,7,10,18,158,314⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,3,8,12,10,18,158,314⟩,some (⟨0,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,10,18,158,314⟩,some (⟨0,by decide⟩,true,3)⟩,⟨1,⟨1,11,13,23,10,18,158,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,1,2,2,19,27,158,236⟩,none⟩,⟨1,⟨1,1,3,3,19,27,158,236⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,1,2,3,28,35,158,236⟩,some (⟨0,by decide⟩,true,3)⟩,⟨1,⟨1,1,2,3,19,35,237,314⟩,some (⟨0,by decide⟩,true,2)⟩,⟨1,⟨1,1,4,4,19,35,158,314⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨2,2,4,4,19,35,158,314⟩,some (⟨1,by decide⟩,true,4)⟩,⟨1,⟨1,3,5,7,19,35,158,314⟩,some (⟨1,by decide⟩,false,4)⟩,⟨1,⟨1,3,8,12,19,35,158,314⟩,some (⟨0,by decide⟩,false,3)⟩,⟨1,⟨4,6,8,12,19,35,158,314⟩,some (⟨0,by decide⟩,false,3)⟩,⟨1,⟨1,11,13,23,19,35,158,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨1,⟨1,11,2,23,36,70,158,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,6,4,17,2,11,2,11⟩,none⟩,⟨2,⟨7,11,14,22,7,11,7,11⟩,some (⟨1,by decide⟩,true,2)⟩,⟨2,⟨2,6,4,17,2,11,12,21⟩,none⟩,⟨2,⟨7,11,14,22,7,11,12,21⟩,some (⟨1,by decide⟩,true,2)⟩,⟨2,⟨2,6,4,13,12,21,12,21⟩,none⟩,⟨2,⟨2,11,14,23,12,21,12,21⟩,some (⟨1,by decide⟩,false,2)⟩,⟨2,⟨2,6,4,17,2,11,22,41⟩,none⟩,⟨2,⟨7,11,14,22,7,11,22,41⟩,some (⟨1,by decide⟩,true,2)⟩,⟨2,⟨2,6,4,13,12,21,22,41⟩,none⟩,⟨2,⟨2,11,14,23,12,21,22,41⟩,some (⟨1,by decide⟩,false,2)⟩,⟨2,⟨2,4,4,8,22,41,22,41⟩,none⟩,⟨2,⟨2,6,9,13,22,41,22,41⟩,some (⟨2,by decide⟩,true,3)⟩,⟨2,⟨2,11,14,23,22,41,22,41⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,6,4,16,2,10,42,80⟩,none⟩,⟨2,⟨7,10,14,20,7,10,42,80⟩,some (⟨1,by decide⟩,true,2)⟩,⟨2,⟨2,6,4,13,11,19,42,80⟩,none⟩,⟨2,⟨2,11,14,23,11,19,42,80⟩,some (⟨1,by decide⟩,false,2)⟩,⟨2,⟨2,4,4,8,20,36,42,80⟩,none⟩,⟨2,⟨2,6,9,13,20,36,42,80⟩,some (⟨2,by decide⟩,true,3)⟩,⟨2,⟨2,11,14,23,20,36,42,80⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,11,4,23,37,70,42,80⟩,some (⟨1,by decide⟩,false,2)⟩,⟨2,⟨2,6,4,16,2,10,81,158⟩,none⟩,⟨2,⟨7,10,14,20,7,10,81,158⟩,some (⟨0,by decide⟩,true,2)⟩,⟨2,⟨2,6,4,13,11,19,81,158⟩,none⟩,⟨2,⟨2,11,14,23,11,19,81,158⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,4,4,8,20,36,81,158⟩,none⟩,⟨2,⟨2,6,9,13,20,36,81,158⟩,some (⟨1,by decide⟩,true,3)⟩,⟨2,⟨2,11,14,23,20,36,81,158⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,6,4,13,37,70,81,158⟩,some (⟨1,by decide⟩,false,2)⟩,⟨2,⟨2,11,14,23,37,70,81,158⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,6,4,16,2,10,159,314⟩,none⟩,⟨2,⟨7,10,14,20,7,10,159,314⟩,some (⟨0,by decide⟩,true,2)⟩,⟨2,⟨2,6,4,13,11,19,159,314⟩,none⟩,⟨2,⟨2,11,14,23,11,19,159,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,4,4,8,20,36,159,314⟩,none⟩,⟨2,⟨2,6,9,13,20,36,159,314⟩,some (⟨1,by decide⟩,true,3)⟩,⟨2,⟨2,11,14,23,20,36,159,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,4,4,8,37,70,159,314⟩,some (⟨1,by decide⟩,true,2)⟩,⟨2,⟨2,6,9,13,37,70,159,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨2,⟨2,11,14,23,37,70,159,314⟩,some (⟨0,by decide⟩,false,2)⟩,⟨3,⟨3,11,6,23,3,22,3,41⟩,none⟩,⟨3,⟨3,7,6,14,23,41,23,41⟩,none⟩,⟨3,⟨3,11,15,23,23,41,23,41⟩,some (⟨1,by decide⟩,true,2)⟩,⟨3,⟨3,11,6,23,3,36,42,80⟩,none⟩,⟨3,⟨3,7,6,14,37,70,42,80⟩,some (⟨2,by decide⟩,true,2)⟩,⟨3,⟨3,11,15,23,37,70,42,80⟩,some (⟨0,by decide⟩,true,2)⟩,⟨3,⟨3,11,6,23,3,36,81,158⟩,none⟩,⟨3,⟨3,7,6,14,37,70,81,158⟩,some (⟨1,by decide⟩,true,2)⟩,⟨3,⟨3,11,15,23,37,70,81,158⟩,some (⟨0,by decide⟩,true,2)⟩,⟨3,⟨3,11,6,23,3,19,159,314⟩,none⟩,⟨3,⟨3,7,6,14,20,36,159,314⟩,none⟩,⟨3,⟨3,11,15,23,20,36,159,314⟩,some (⟨0,by decide⟩,true,2)⟩,⟨3,⟨3,7,6,14,37,70,159,314⟩,some (⟨1,by decide⟩,true,2)⟩,⟨3,⟨3,11,15,23,37,70,159,314⟩,some (⟨0,by decide⟩,true,2)⟩,⟨4,⟨4,11,8,23,4,70,4,314⟩,none⟩,⟨5,⟨5,11,10,23,5,70,5,314⟩,none⟩,⟨6,⟨6,11,12,23,6,70,6,314⟩,none⟩,⟨7,⟨7,11,14,23,7,70,7,314⟩,none⟩,⟨8,⟨8,11,16,23,8,70,8,314⟩,none⟩,⟨9,⟨9,11,18,23,9,70,9,314⟩,none⟩,⟨10,⟨10,11,20,23,10,70,10,314⟩,none⟩,⟨11,⟨11,11,22,23,11,70,11,314⟩,none⟩]

def OldValid (l:Leaf):Prop:=match l.kind with
 | none=>check .native fixed l.a l.m 3681 3800 58 13 273900000000000000=true
 | some c=>BandValid fixed l.a l.m 3681 3800 58 13 273900000000000000 c.1 c.2.1 c.2.2
theorem old (i:Fin 222):OldValid (leaf i):=by
 fin_cases i
 · exact BN.bc1_12
 · exact BN.bc1_13
 · exact BN.bc1_15
 · exact BN.bc1_16
 · exact BN.bc1_18
 · exact BN.bc1_19
 · exact BN.bc1_20
 · exact BN.bc1_24
 · exact BN.bc1_25
 · exact BN.bc1_27
 · exact BN.bc1_28
 · exact BN.bc1_29
 · exact BN.bc1_34
 · exact BN.bc1_38
 · exact BN.bc1_41
 · exact BN.bc1_42
 · exact BN.bc1_43
 · exact BN.bc1_44
 · exact BN.bc1_45
 · exact BN.bc1_46
 · exact BN.bc1_47
 · exact BN.bc1_48
 · exact BN.bc1_53
 · exact BN.bc1_54
 · exact BN.bc1_56
 · exact BN.bc1_57
 · exact BN.bc1_58
 · exact BN.bc1_63
 · exact BN.bc1_68
 · exact BN.bc1_72
 · exact BN.bc1_73
 · exact BN.bc1_74
 · exact BN.bc1_77
 · exact BN.bc1_78
 · exact BN.bc1_79
 · exact BN.bc1_81
 · exact BN.bc1_85
 · exact BN.bc1_86
 · exact BN.bc1_88
 · exact BN.bc1_89
 · exact BN.bc1_90
 · exact BN.bc1_91
 · exact BN.bc1_92
 · exact BN.bc1_93
 · exact BN.bc1_94
 · exact BN.bc1_95
 · exact BN.bc1_105
 · exact BN.bc1_107
 · exact BN.bc1_108
 · exact BN.bc1_110
 · exact BN.bc1_111
 · exact BN.bc1_112
 · exact BN.bc1_113
 · exact BN.bc1_114
 · exact BN.bc1_115
 · exact BN.bc1_116
 · exact BN.bc1_117
 · exact BN.bc1_118
 · exact BN.bc1_125
 · exact BN.bc1_126
 · exact BN.bc1_128
 · exact BN.bc1_129
 · exact BN.bc1_130
 · exact BN.bc1_135
 · exact BN.bc1_140
 · exact BN.bc1_143
 · exact BN.bc1_144
 · exact BN.bc1_146
 · exact BN.bc1_147
 · exact BN.bc1_149
 · exact BN.bc1_151
 · exact BN.bc1_152
 · exact BN.bc1_153
 · exact BN.bc1_154
 · exact BN.bc1_155
 · exact BN.bc1_156
 · exact BN.bc1_157
 · exact BN.bc1_166
 · exact BN.bc1_167
 · exact BN.bc1_169
 · exact BN.bc1_170
 · exact BN.bc1_175
 · exact BN.bc1_176
 · exact BN.bc1_178
 · exact BN.bc1_179
 · exact BN.bc1_180
 · exact BN.bc1_181
 · exact BN.bc1_184
 · exact BN.bc1_185
 · exact BN.bc1_186
 · exact BN.bc1_187
 · exact BN.bc1_188
 · exact BN.bc1_189
 · exact BN.bc1_190
 · exact BN.bc1_191
 · exact BN.bc1_198
 · exact BN.bc1_199
 · exact BN.bc1_201
 · exact BN.bc1_202
 · exact BN.bc1_203
 · exact BN.bc1_208
 · exact BN.bc1_213
 · exact BN.bc1_217
 · exact BN.bc1_219
 · exact BN.bc1_220
 · exact BN.bc1_221
 · exact BN.bc1_224
 · exact BN.bc1_225
 · exact BN.bc1_226
 · exact BN.bc1_229
 · exact BN.bc1_230
 · exact BN.bc1_231
 · exact BN.bc1_232
 · exact BN.bc1_233
 · exact BN.bc1_234
 · exact BN.bc1_235
 · exact BN.bc1_236
 · exact BN.bc1_245
 · exact BN.bc1_246
 · exact BN.bc1_248
 · exact BN.bc1_249
 · exact BN.bc1_250
 · exact BN.bc1_251
 · exact BN.bc1_252
 · exact BN.bc1_253
 · exact BN.bc1_254
 · exact BN.bc1_255
 · exact BN.bc1_256
 · exact BN.bc1_264
 · exact BN.bc1_266
 · exact BN.bc1_268
 · exact BN.bc1_269
 · exact BN.bc1_270
 · exact BN.bc1_274
 · exact BN.bc1_275
 · exact BN.bc1_276
 · exact BN.bc1_277
 · exact BN.bc1_278
 · exact BN.bc1_283
 · exact BN.bc1_290
 · exact BN.bc1_291
 · exact BN.bc1_292
 · exact BN.bc1_293
 · exact BN.bc1_294
 · exact BN.bc1_295
 · exact BN.bc1_296
 · exact BN.bc1_297
 · exact BN.bc1_298
 · exact BN.bc1_299
 · exact BN.bc1_309
 · exact BN.bc1_310
 · exact BN.bc1_311
 · exact BN.bc1_312
 · exact BN.bc1_313
 · exact BN.bc1_314
 · exact BN.bc1_315
 · exact BN.bc1_316
 · exact BN.bc1_317
 · exact BN.bc1_318
 · exact BN.bc1_319
 · exact BN.bc2_328
 · exact BN.bc2_329
 · exact BN.bc2_331
 · exact BN.bc2_332
 · exact BN.bc2_334
 · exact BN.bc2_335
 · exact BN.bc2_338
 · exact BN.bc2_339
 · exact BN.bc2_341
 · exact BN.bc2_342
 · exact BN.bc2_345
 · exact BN.bc2_346
 · exact BN.bc2_347
 · exact BN.bc2_352
 · exact BN.bc2_353
 · exact BN.bc2_355
 · exact BN.bc2_356
 · exact BN.bc2_359
 · exact BN.bc2_360
 · exact BN.bc2_361
 · exact BN.bc2_362
 · exact BN.bc2_367
 · exact BN.bc2_368
 · exact BN.bc2_370
 · exact BN.bc2_371
 · exact BN.bc2_374
 · exact BN.bc2_375
 · exact BN.bc2_376
 · exact BN.bc2_378
 · exact BN.bc2_379
 · exact BN.bc2_384
 · exact BN.bc2_385
 · exact BN.bc2_387
 · exact BN.bc2_388
 · exact BN.bc2_391
 · exact BN.bc2_392
 · exact BN.bc2_393
 · exact BN.bc2_396
 · exact BN.bc2_397
 · exact BN.bc2_398
 · exact BN.bc3_403
 · exact BN.bc3_405
 · exact BN.bc3_406
 · exact BN.bc3_408
 · exact BN.bc3_410
 · exact BN.bc3_411
 · exact BN.bc3_413
 · exact BN.bc3_415
 · exact BN.bc3_416
 · exact BN.bc3_419
 · exact BN.bc3_421
 · exact BN.bc3_422
 · exact BN.bc3_424
 · exact BN.bc3_425
 · exact BN.bc4_426
 · exact BN.bc5_427
 · exact BN.bc6_428
 · exact BN.bc7_429
 · exact BN.bc8_430
 · exact BN.bc9_431
 · exact BN.bc10_432
 · exact BN.bc11_433

def Geometry (l:Leaf) (fixedNew:Degrees) (low t y r cap:ℕ):Prop:=match l.kind with
 | none=>CME l.a l.m low t y r cap
 | some c=>DHJ fixedNew l.a l.m low t y r cap c.1 c.2.1
instance (l:Leaf) (fixedNew:Degrees) (low t y r cap:ℕ):Decidable (Geometry l fixedNew low t y r cap):=by unfold Geometry;split<;>infer_instance
def AllGeometry (fixedNew:Degrees) (low t y r cap:ℕ):Prop:= ∀i:Fin 222,Geometry (leaf i) fixedNew low t y r cap
instance (fixedNew:Degrees) (low t y r cap:ℕ):Decidable (AllGeometry fixedNew low t y r cap):=by unfold AllGeometry;infer_instance
theorem leaf_valid (i:Fin 222) (fixedNew:Degrees) (low t y r cap:ℕ) (hg:Geometry (leaf i) fixedNew low t y r cap):
 Valid fixedNew (leaf i).m low t y r cap (leaf i).a:=by
 have hc:=old i
 cases hh:(leaf i).kind with
 | none=>
   simp only [OldValid,hh] at hc
   simp only [Geometry,hh] at hg
   exact Or.inl (GIP fixed fixedNew (leaf i).a (leaf i).m 3681 3800 58 13 273900000000000000 low t y r cap hc hg)
 | some c=>
   simp only [OldValid,hh] at hc
   simp only [Geometry,hh] at hg
   exact Or.inr ⟨c.1,c.2.1,c.2.2,GVP fixed fixedNew (leaf i).a (leaf i).m 3681 3800 58 13 273900000000000000 low t y r cap c.1 c.2.1 c.2.2 hc hg⟩
def occurs (m:ℕ) (a:Box):Prop:= ∃i:Fin 222,(leaf i).m=m∧(leaf i).a=a

theorem metac1_12:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,1,5⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,1,5⟩ ⟨1,3,2,8,1,5,1,5⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,8,1,5,1,5⟩ ⟨⟨0,by decide⟩,rfl,rfl⟩

theorem metac1_13:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,1,5⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,1,5⟩ ⟨4,5,8,10,4,5,4,5⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,4,5⟩ ⟨⟨1,by decide⟩,rfl,rfl⟩

theorem metac1_11:Covered 1 (occurs 1) ⟨1,5,2,10,1,5,1,5⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,10,1,5,1,5⟩ ⟨1,5,2,10,1,5,1,5⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,1,5⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_12) (by simpa only [upper] using metac1_13)

theorem metac1_15:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,6,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,6,10⟩ ⟨1,3,2,8,1,5,6,10⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,8,1,5,6,10⟩ ⟨⟨2,by decide⟩,rfl,rfl⟩

theorem metac1_16:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,6,10⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,6,10⟩ ⟨4,5,8,10,4,5,6,10⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,6,10⟩ ⟨⟨3,by decide⟩,rfl,rfl⟩

theorem metac1_14:Covered 1 (occurs 1) ⟨1,5,2,10,1,5,6,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,10,1,5,6,10⟩ ⟨1,5,2,10,1,5,6,10⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,6,10⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_15) (by simpa only [upper] using metac1_16)

theorem metac1_10:Covered 1 (occurs 1) ⟨1,5,2,15,1,5,1,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,15,1,5,1,10⟩ ⟨1,5,2,10,1,5,1,10⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,1,10⟩ ⟨3,by decide⟩ 5 (by simpa only [lower] using metac1_11) (by simpa only [upper] using metac1_14)

theorem metac1_18:Covered 1 (occurs 1) ⟨1,5,2,8,6,10,6,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,8,6,10,6,10⟩ ⟨1,4,2,8,6,10,6,10⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,4,2,8,6,10,6,10⟩ ⟨⟨4,by decide⟩,rfl,rfl⟩

theorem metac1_19:Covered 1 (occurs 1) ⟨1,5,9,15,6,10,6,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,9,15,6,10,6,10⟩ ⟨1,5,9,15,6,10,6,10⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,5,9,15,6,10,6,10⟩ ⟨⟨5,by decide⟩,rfl,rfl⟩

theorem metac1_17:Covered 1 (occurs 1) ⟨1,5,2,15,6,10,1,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,15,6,10,1,10⟩ ⟨1,5,2,15,6,10,6,10⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,15,6,10,6,10⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac1_18) (by simpa only [upper] using metac1_19)

theorem metac1_9:Covered 1 (occurs 1) ⟨1,5,2,20,1,10,1,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,20,1,10,1,10⟩ ⟨1,5,2,15,1,10,1,10⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,15,1,10,1,10⟩ ⟨2,by decide⟩ 5 (by simpa only [lower] using metac1_10) (by simpa only [upper] using metac1_17)

theorem metac1_20:Covered 1 (occurs 1) ⟨6,10,2,20,1,10,1,10⟩:=by
 apply AO 1 (occurs 1) ⟨6,10,2,20,1,10,1,10⟩ ⟨6,10,12,20,6,10,6,10⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨6,10,12,20,6,10,6,10⟩ ⟨⟨6,by decide⟩,rfl,rfl⟩

theorem metac1_8:Covered 1 (occurs 1) ⟨1,10,2,20,1,10,1,10⟩:=by
 apply AO 1 (occurs 1) ⟨1,10,2,20,1,10,1,10⟩ ⟨1,10,2,20,1,10,1,10⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,10,2,20,1,10,1,10⟩ ⟨0,by decide⟩ 5 (by simpa only [lower] using metac1_9) (by simpa only [upper] using metac1_20)

theorem metac1_24:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,11,20⟩ ⟨1,3,2,8,1,5,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,8,1,5,11,20⟩ ⟨⟨7,by decide⟩,rfl,rfl⟩

theorem metac1_25:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,11,20⟩ ⟨4,5,8,10,4,5,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,11,20⟩ ⟨⟨8,by decide⟩,rfl,rfl⟩

theorem metac1_23:Covered 1 (occurs 1) ⟨1,5,2,15,1,5,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,15,1,5,11,20⟩ ⟨1,5,2,10,1,5,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,11,20⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_24) (by simpa only [upper] using metac1_25)

theorem metac1_27:Covered 1 (occurs 1) ⟨1,5,2,8,6,10,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,8,6,10,11,20⟩ ⟨1,4,2,8,6,10,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,4,2,8,6,10,11,20⟩ ⟨⟨9,by decide⟩,rfl,rfl⟩

theorem metac1_28:Covered 1 (occurs 1) ⟨1,5,9,15,6,10,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,9,15,6,10,11,20⟩ ⟨1,5,9,15,6,10,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,5,9,15,6,10,11,20⟩ ⟨⟨10,by decide⟩,rfl,rfl⟩

theorem metac1_26:Covered 1 (occurs 1) ⟨1,5,2,15,6,10,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,15,6,10,11,20⟩ ⟨1,5,2,15,6,10,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,15,6,10,11,20⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac1_27) (by simpa only [upper] using metac1_28)

theorem metac1_22:Covered 1 (occurs 1) ⟨1,5,2,20,1,10,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,20,1,10,11,20⟩ ⟨1,5,2,15,1,10,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,15,1,10,11,20⟩ ⟨2,by decide⟩ 5 (by simpa only [lower] using metac1_23) (by simpa only [upper] using metac1_26)

theorem metac1_29:Covered 1 (occurs 1) ⟨6,10,2,20,1,10,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨6,10,2,20,1,10,11,20⟩ ⟨6,10,12,20,6,10,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨6,10,12,20,6,10,11,20⟩ ⟨⟨11,by decide⟩,rfl,rfl⟩

theorem metac1_21:Covered 1 (occurs 1) ⟨1,10,2,20,1,10,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,10,2,20,1,10,11,20⟩ ⟨1,10,2,20,1,10,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,10,2,20,1,10,11,20⟩ ⟨0,by decide⟩ 5 (by simpa only [lower] using metac1_22) (by simpa only [upper] using metac1_29)

theorem metac1_7:Covered 1 (occurs 1) ⟨1,11,2,23,1,10,1,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,10,1,20⟩ ⟨1,10,2,20,1,10,1,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,10,2,20,1,10,1,20⟩ ⟨3,by decide⟩ 10 (by simpa only [lower] using metac1_8) (by simpa only [upper] using metac1_21)

theorem metac1_34:Covered 1 (occurs 1) ⟨1,3,2,4,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,11,20,11,20⟩ ⟨1,2,2,4,11,20,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,4,11,20,11,20⟩ ⟨⟨12,by decide⟩,rfl,rfl⟩

theorem metac1_38:Covered 1 (occurs 1) ⟨1,1,5,7,11,15,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,15,11,20⟩ ⟨1,1,5,7,11,15,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,11,15,11,20⟩ ⟨⟨13,by decide⟩,rfl,rfl⟩

theorem metac1_41:Covered 1 (occurs 1) ⟨1,1,5,6,16,18,16,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,18,16,20⟩ ⟨1,1,5,6,16,18,16,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,16,18,16,20⟩ ⟨⟨14,by decide⟩,rfl,rfl⟩

theorem metac1_42:Covered 1 (occurs 1) ⟨1,1,5,6,19,20,16,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,19,20,16,20⟩ ⟨1,1,5,6,19,20,19,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,19,20,19,20⟩ ⟨⟨15,by decide⟩,rfl,rfl⟩

theorem metac1_40:Covered 1 (occurs 1) ⟨1,1,5,6,16,20,16,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,20,16,20⟩ ⟨1,1,5,6,16,20,16,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,16,20,16,20⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_41) (by simpa only [upper] using metac1_42)

theorem metac1_43:Covered 1 (occurs 1) ⟨1,1,7,7,16,20,16,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,16,20,16,20⟩ ⟨1,1,7,7,16,20,16,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,16,20,16,20⟩ ⟨⟨16,by decide⟩,rfl,rfl⟩

theorem metac1_39:Covered 1 (occurs 1) ⟨1,1,5,7,16,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,16,20,11,20⟩ ⟨1,1,5,7,16,20,16,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,16,20,16,20⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_40) (by simpa only [upper] using metac1_43)

theorem metac1_37:Covered 1 (occurs 1) ⟨1,1,5,7,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,20,11,20⟩ ⟨1,1,5,7,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,11,20,11,20⟩ ⟨2,by decide⟩ 15 (by simpa only [lower] using metac1_38) (by simpa only [upper] using metac1_39)

theorem metac1_44:Covered 1 (occurs 1) ⟨2,2,5,7,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,5,7,11,20,11,20⟩ ⟨2,2,5,7,11,20,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,5,7,11,20,11,20⟩ ⟨⟨17,by decide⟩,rfl,rfl⟩

theorem metac1_36:Covered 1 (occurs 1) ⟨1,2,5,7,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,5,7,11,20,11,20⟩ ⟨1,2,5,7,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,5,7,11,20,11,20⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_37) (by simpa only [upper] using metac1_44)

theorem metac1_45:Covered 1 (occurs 1) ⟨3,3,5,7,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨3,3,5,7,11,20,11,20⟩ ⟨3,3,6,7,11,20,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,3,6,7,11,20,11,20⟩ ⟨⟨18,by decide⟩,rfl,rfl⟩

theorem metac1_35:Covered 1 (occurs 1) ⟨1,3,5,7,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,11,20,11,20⟩ ⟨1,3,5,7,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,5,7,11,20,11,20⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_36) (by simpa only [upper] using metac1_45)

theorem metac1_33:Covered 1 (occurs 1) ⟨1,3,2,7,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,11,20,11,20⟩ ⟨1,3,2,7,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,11,20,11,20⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_34) (by simpa only [upper] using metac1_35)

theorem metac1_46:Covered 1 (occurs 1) ⟨1,3,8,12,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,11,20,11,20⟩ ⟨1,3,8,12,11,20,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,11,20,11,20⟩ ⟨⟨19,by decide⟩,rfl,rfl⟩

theorem metac1_32:Covered 1 (occurs 1) ⟨1,3,2,12,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,11,20,11,20⟩ ⟨1,3,2,12,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,11,20,11,20⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_33) (by simpa only [upper] using metac1_46)

theorem metac1_47:Covered 1 (occurs 1) ⟨4,6,2,12,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,11,20,11,20⟩ ⟨4,6,8,12,11,20,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,11,20,11,20⟩ ⟨⟨20,by decide⟩,rfl,rfl⟩

theorem metac1_31:Covered 1 (occurs 1) ⟨1,11,2,12,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,11,20,11,20⟩ ⟨1,6,2,12,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,11,20,11,20⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_32) (by simpa only [upper] using metac1_47)

theorem metac1_48:Covered 1 (occurs 1) ⟨1,11,13,23,11,20,11,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,11,20,11,20⟩ ⟨1,11,13,23,11,20,11,20⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,11,20,11,20⟩ ⟨⟨21,by decide⟩,rfl,rfl⟩

theorem metac1_30:Covered 1 (occurs 1) ⟨1,11,2,23,11,20,1,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,11,20,1,20⟩ ⟨1,11,2,23,11,20,11,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,11,20,11,20⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_31) (by simpa only [upper] using metac1_48)

theorem metac1_6:Covered 1 (occurs 1) ⟨1,11,2,23,1,20,1,20⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,20,1,20⟩ ⟨1,11,2,23,1,20,1,20⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,20,1,20⟩ ⟨2,by decide⟩ 10 (by simpa only [lower] using metac1_7) (by simpa only [upper] using metac1_30)

theorem metac1_53:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,21,40⟩ ⟨1,3,2,8,1,5,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,8,1,5,21,40⟩ ⟨⟨22,by decide⟩,rfl,rfl⟩

theorem metac1_54:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,21,40⟩ ⟨4,5,8,10,4,5,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,21,40⟩ ⟨⟨23,by decide⟩,rfl,rfl⟩

theorem metac1_52:Covered 1 (occurs 1) ⟨1,5,2,15,1,5,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,15,1,5,21,40⟩ ⟨1,5,2,10,1,5,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,21,40⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_53) (by simpa only [upper] using metac1_54)

theorem metac1_56:Covered 1 (occurs 1) ⟨1,5,2,8,6,10,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,8,6,10,21,40⟩ ⟨1,4,2,8,6,10,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,4,2,8,6,10,21,40⟩ ⟨⟨24,by decide⟩,rfl,rfl⟩

theorem metac1_57:Covered 1 (occurs 1) ⟨1,5,9,15,6,10,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,9,15,6,10,21,40⟩ ⟨1,5,9,15,6,10,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,5,9,15,6,10,21,40⟩ ⟨⟨25,by decide⟩,rfl,rfl⟩

theorem metac1_55:Covered 1 (occurs 1) ⟨1,5,2,15,6,10,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,15,6,10,21,40⟩ ⟨1,5,2,15,6,10,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,15,6,10,21,40⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac1_56) (by simpa only [upper] using metac1_57)

theorem metac1_51:Covered 1 (occurs 1) ⟨1,5,2,20,1,10,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,20,1,10,21,40⟩ ⟨1,5,2,15,1,10,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,15,1,10,21,40⟩ ⟨2,by decide⟩ 5 (by simpa only [lower] using metac1_52) (by simpa only [upper] using metac1_55)

theorem metac1_58:Covered 1 (occurs 1) ⟨6,10,2,20,1,10,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨6,10,2,20,1,10,21,40⟩ ⟨6,10,12,20,6,10,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨6,10,12,20,6,10,21,40⟩ ⟨⟨26,by decide⟩,rfl,rfl⟩

theorem metac1_50:Covered 1 (occurs 1) ⟨1,11,2,23,1,10,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,10,21,40⟩ ⟨1,10,2,20,1,10,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,10,2,20,1,10,21,40⟩ ⟨0,by decide⟩ 5 (by simpa only [lower] using metac1_51) (by simpa only [upper] using metac1_58)

theorem metac1_63:Covered 1 (occurs 1) ⟨1,3,2,4,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,11,20,21,40⟩ ⟨1,2,2,4,11,20,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,4,11,20,21,40⟩ ⟨⟨27,by decide⟩,rfl,rfl⟩

theorem metac1_68:Covered 1 (occurs 1) ⟨1,1,5,7,11,15,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,15,21,30⟩ ⟨1,1,5,7,11,15,21,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,11,15,21,30⟩ ⟨⟨28,by decide⟩,rfl,rfl⟩

theorem metac1_72:Covered 1 (occurs 1) ⟨1,1,5,6,16,18,21,25⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,18,21,25⟩ ⟨1,1,5,6,16,18,21,25⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,16,18,21,25⟩ ⟨⟨29,by decide⟩,rfl,rfl⟩

theorem metac1_73:Covered 1 (occurs 1) ⟨1,1,5,6,19,20,21,25⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,19,20,21,25⟩ ⟨1,1,5,6,19,20,21,25⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,19,20,21,25⟩ ⟨⟨30,by decide⟩,rfl,rfl⟩

theorem metac1_71:Covered 1 (occurs 1) ⟨1,1,5,6,16,20,21,25⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,20,21,25⟩ ⟨1,1,5,6,16,20,21,25⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,16,20,21,25⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_72) (by simpa only [upper] using metac1_73)

theorem metac1_74:Covered 1 (occurs 1) ⟨1,1,7,7,16,20,21,25⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,16,20,21,25⟩ ⟨1,1,7,7,16,20,21,25⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,16,20,21,25⟩ ⟨⟨31,by decide⟩,rfl,rfl⟩

theorem metac1_70:Covered 1 (occurs 1) ⟨1,1,5,7,16,20,21,25⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,16,20,21,25⟩ ⟨1,1,5,7,16,20,21,25⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,16,20,21,25⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_71) (by simpa only [upper] using metac1_74)

theorem metac1_77:Covered 1 (occurs 1) ⟨1,1,5,6,16,18,26,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,18,26,30⟩ ⟨1,1,5,6,16,18,26,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,16,18,26,30⟩ ⟨⟨32,by decide⟩,rfl,rfl⟩

theorem metac1_78:Covered 1 (occurs 1) ⟨1,1,5,6,19,20,26,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,19,20,26,30⟩ ⟨1,1,5,6,19,20,26,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,19,20,26,30⟩ ⟨⟨33,by decide⟩,rfl,rfl⟩

theorem metac1_76:Covered 1 (occurs 1) ⟨1,1,5,6,16,20,26,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,20,26,30⟩ ⟨1,1,5,6,16,20,26,30⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,16,20,26,30⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_77) (by simpa only [upper] using metac1_78)

theorem metac1_79:Covered 1 (occurs 1) ⟨1,1,7,7,16,20,26,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,16,20,26,30⟩ ⟨1,1,7,7,16,20,26,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,16,20,26,30⟩ ⟨⟨34,by decide⟩,rfl,rfl⟩

theorem metac1_75:Covered 1 (occurs 1) ⟨1,1,5,7,16,20,26,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,16,20,26,30⟩ ⟨1,1,5,7,16,20,26,30⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,16,20,26,30⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_76) (by simpa only [upper] using metac1_79)

theorem metac1_69:Covered 1 (occurs 1) ⟨1,1,5,7,16,20,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,16,20,21,30⟩ ⟨1,1,5,7,16,20,21,30⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,16,20,21,30⟩ ⟨3,by decide⟩ 25 (by simpa only [lower] using metac1_70) (by simpa only [upper] using metac1_75)

theorem metac1_67:Covered 1 (occurs 1) ⟨1,1,5,7,11,20,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,20,21,30⟩ ⟨1,1,5,7,11,20,21,30⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,11,20,21,30⟩ ⟨2,by decide⟩ 15 (by simpa only [lower] using metac1_68) (by simpa only [upper] using metac1_69)

theorem metac1_81:Covered 1 (occurs 1) ⟨1,1,5,7,11,15,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,15,31,40⟩ ⟨1,1,5,7,11,15,31,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,11,15,31,40⟩ ⟨⟨35,by decide⟩,rfl,rfl⟩

theorem metac1_85:Covered 1 (occurs 1) ⟨1,1,5,6,16,18,31,35⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,18,31,35⟩ ⟨1,1,5,6,16,18,31,35⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,16,18,31,35⟩ ⟨⟨36,by decide⟩,rfl,rfl⟩

theorem metac1_86:Covered 1 (occurs 1) ⟨1,1,5,6,19,20,31,35⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,19,20,31,35⟩ ⟨1,1,5,6,19,20,31,35⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,19,20,31,35⟩ ⟨⟨37,by decide⟩,rfl,rfl⟩

theorem metac1_84:Covered 1 (occurs 1) ⟨1,1,5,6,16,20,31,35⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,20,31,35⟩ ⟨1,1,5,6,16,20,31,35⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,16,20,31,35⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_85) (by simpa only [upper] using metac1_86)

theorem metac1_88:Covered 1 (occurs 1) ⟨1,1,5,6,16,18,36,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,18,36,40⟩ ⟨1,1,5,6,16,18,36,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,16,18,36,40⟩ ⟨⟨38,by decide⟩,rfl,rfl⟩

theorem metac1_89:Covered 1 (occurs 1) ⟨1,1,5,6,19,20,36,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,19,20,36,40⟩ ⟨1,1,5,6,19,20,36,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,19,20,36,40⟩ ⟨⟨39,by decide⟩,rfl,rfl⟩

theorem metac1_87:Covered 1 (occurs 1) ⟨1,1,5,6,16,20,36,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,20,36,40⟩ ⟨1,1,5,6,16,20,36,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,16,20,36,40⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_88) (by simpa only [upper] using metac1_89)

theorem metac1_83:Covered 1 (occurs 1) ⟨1,1,5,6,16,20,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,16,20,31,40⟩ ⟨1,1,5,6,16,20,31,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,16,20,31,40⟩ ⟨3,by decide⟩ 35 (by simpa only [lower] using metac1_84) (by simpa only [upper] using metac1_87)

theorem metac1_90:Covered 1 (occurs 1) ⟨1,1,7,7,16,20,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,16,20,31,40⟩ ⟨1,1,7,7,16,20,31,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,16,20,31,40⟩ ⟨⟨40,by decide⟩,rfl,rfl⟩

theorem metac1_82:Covered 1 (occurs 1) ⟨1,1,5,7,16,20,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,16,20,31,40⟩ ⟨1,1,5,7,16,20,31,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,16,20,31,40⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_83) (by simpa only [upper] using metac1_90)

theorem metac1_80:Covered 1 (occurs 1) ⟨1,1,5,7,11,20,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,20,31,40⟩ ⟨1,1,5,7,11,20,31,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,11,20,31,40⟩ ⟨2,by decide⟩ 15 (by simpa only [lower] using metac1_81) (by simpa only [upper] using metac1_82)

theorem metac1_66:Covered 1 (occurs 1) ⟨1,1,5,7,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,11,20,21,40⟩ ⟨1,1,5,7,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,11,20,21,40⟩ ⟨3,by decide⟩ 30 (by simpa only [lower] using metac1_67) (by simpa only [upper] using metac1_80)

theorem metac1_91:Covered 1 (occurs 1) ⟨2,2,5,7,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,5,7,11,20,21,40⟩ ⟨2,2,5,7,11,20,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,5,7,11,20,21,40⟩ ⟨⟨41,by decide⟩,rfl,rfl⟩

theorem metac1_65:Covered 1 (occurs 1) ⟨1,2,5,7,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,5,7,11,20,21,40⟩ ⟨1,2,5,7,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,5,7,11,20,21,40⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_66) (by simpa only [upper] using metac1_91)

theorem metac1_92:Covered 1 (occurs 1) ⟨3,3,5,7,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨3,3,5,7,11,20,21,40⟩ ⟨3,3,6,7,11,20,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,3,6,7,11,20,21,40⟩ ⟨⟨42,by decide⟩,rfl,rfl⟩

theorem metac1_64:Covered 1 (occurs 1) ⟨1,3,5,7,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,11,20,21,40⟩ ⟨1,3,5,7,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,5,7,11,20,21,40⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_65) (by simpa only [upper] using metac1_92)

theorem metac1_62:Covered 1 (occurs 1) ⟨1,3,2,7,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,11,20,21,40⟩ ⟨1,3,2,7,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,11,20,21,40⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_63) (by simpa only [upper] using metac1_64)

theorem metac1_93:Covered 1 (occurs 1) ⟨1,3,8,12,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,11,20,21,40⟩ ⟨1,3,8,12,11,20,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,11,20,21,40⟩ ⟨⟨43,by decide⟩,rfl,rfl⟩

theorem metac1_61:Covered 1 (occurs 1) ⟨1,3,2,12,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,11,20,21,40⟩ ⟨1,3,2,12,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,11,20,21,40⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_62) (by simpa only [upper] using metac1_93)

theorem metac1_94:Covered 1 (occurs 1) ⟨4,6,2,12,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,11,20,21,40⟩ ⟨4,6,8,12,11,20,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,11,20,21,40⟩ ⟨⟨44,by decide⟩,rfl,rfl⟩

theorem metac1_60:Covered 1 (occurs 1) ⟨1,11,2,12,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,11,20,21,40⟩ ⟨1,6,2,12,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,11,20,21,40⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_61) (by simpa only [upper] using metac1_94)

theorem metac1_95:Covered 1 (occurs 1) ⟨1,11,13,23,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,11,20,21,40⟩ ⟨1,11,13,23,11,20,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,11,20,21,40⟩ ⟨⟨45,by decide⟩,rfl,rfl⟩

theorem metac1_59:Covered 1 (occurs 1) ⟨1,11,2,23,11,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,11,20,21,40⟩ ⟨1,11,2,23,11,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,11,20,21,40⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_60) (by simpa only [upper] using metac1_95)

theorem metac1_49:Covered 1 (occurs 1) ⟨1,11,2,23,1,20,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,20,21,40⟩ ⟨1,11,2,23,1,20,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,20,21,40⟩ ⟨2,by decide⟩ 10 (by simpa only [lower] using metac1_50) (by simpa only [upper] using metac1_59)

theorem metac1_5:Covered 1 (occurs 1) ⟨1,11,2,23,1,20,1,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,20,1,40⟩ ⟨1,11,2,23,1,20,1,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,20,1,40⟩ ⟨3,by decide⟩ 20 (by simpa only [lower] using metac1_6) (by simpa only [upper] using metac1_49)

theorem metac1_105:Covered 1 (occurs 1) ⟨1,1,2,2,21,30,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,2,21,30,21,30⟩ ⟨1,1,2,2,21,30,21,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,2,21,30,21,30⟩ ⟨⟨46,by decide⟩,rfl,rfl⟩

theorem metac1_107:Covered 1 (occurs 1) ⟨1,1,3,3,21,25,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,3,3,21,25,21,30⟩ ⟨1,1,3,3,21,25,21,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,3,3,21,25,21,30⟩ ⟨⟨47,by decide⟩,rfl,rfl⟩

theorem metac1_108:Covered 1 (occurs 1) ⟨1,1,3,3,26,30,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,3,3,26,30,21,30⟩ ⟨1,1,3,3,26,30,26,30⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,3,3,26,30,26,30⟩ ⟨⟨48,by decide⟩,rfl,rfl⟩

theorem metac1_106:Covered 1 (occurs 1) ⟨1,1,3,3,21,30,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,3,3,21,30,21,30⟩ ⟨1,1,3,3,21,30,21,30⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,3,3,21,30,21,30⟩ ⟨2,by decide⟩ 25 (by simpa only [lower] using metac1_107) (by simpa only [upper] using metac1_108)

theorem metac1_104:Covered 1 (occurs 1) ⟨1,1,2,3,21,30,21,30⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,21,30,21,30⟩ ⟨1,1,2,3,21,30,21,30⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,21,30,21,30⟩ ⟨1,by decide⟩ 2 (by simpa only [lower] using metac1_105) (by simpa only [upper] using metac1_106)

theorem metac1_110:Covered 1 (occurs 1) ⟨1,1,2,2,21,30,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,2,21,30,31,40⟩ ⟨1,1,2,2,21,30,31,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,2,21,30,31,40⟩ ⟨⟨49,by decide⟩,rfl,rfl⟩

theorem metac1_111:Covered 1 (occurs 1) ⟨1,1,3,3,21,30,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,3,3,21,30,31,40⟩ ⟨1,1,3,3,21,30,31,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,3,3,21,30,31,40⟩ ⟨⟨50,by decide⟩,rfl,rfl⟩

theorem metac1_109:Covered 1 (occurs 1) ⟨1,1,2,3,21,30,31,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,21,30,31,40⟩ ⟨1,1,2,3,21,30,31,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,21,30,31,40⟩ ⟨1,by decide⟩ 2 (by simpa only [lower] using metac1_110) (by simpa only [upper] using metac1_111)

theorem metac1_103:Covered 1 (occurs 1) ⟨1,1,2,3,21,30,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,21,30,21,40⟩ ⟨1,1,2,3,21,30,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,21,30,21,40⟩ ⟨3,by decide⟩ 30 (by simpa only [lower] using metac1_104) (by simpa only [upper] using metac1_109)

theorem metac1_112:Covered 1 (occurs 1) ⟨1,1,2,3,31,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,31,40,21,40⟩ ⟨1,1,2,3,31,40,31,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,31,40,31,40⟩ ⟨⟨51,by decide⟩,rfl,rfl⟩

theorem metac1_102:Covered 1 (occurs 1) ⟨1,1,2,3,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,21,40,21,40⟩ ⟨1,1,2,3,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,21,40,21,40⟩ ⟨2,by decide⟩ 30 (by simpa only [lower] using metac1_103) (by simpa only [upper] using metac1_112)

theorem metac1_113:Covered 1 (occurs 1) ⟨1,1,4,4,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,21,40,21,40⟩ ⟨1,1,4,4,21,40,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,21,40,21,40⟩ ⟨⟨52,by decide⟩,rfl,rfl⟩

theorem metac1_101:Covered 1 (occurs 1) ⟨1,1,2,4,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,4,21,40,21,40⟩ ⟨1,1,2,4,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,4,21,40,21,40⟩ ⟨1,by decide⟩ 3 (by simpa only [lower] using metac1_102) (by simpa only [upper] using metac1_113)

theorem metac1_114:Covered 1 (occurs 1) ⟨2,2,2,4,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,2,4,21,40,21,40⟩ ⟨2,2,4,4,21,40,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,4,4,21,40,21,40⟩ ⟨⟨53,by decide⟩,rfl,rfl⟩

theorem metac1_100:Covered 1 (occurs 1) ⟨1,3,2,4,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,21,40,21,40⟩ ⟨1,2,2,4,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,2,4,21,40,21,40⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_101) (by simpa only [upper] using metac1_114)

theorem metac1_115:Covered 1 (occurs 1) ⟨1,3,5,7,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,21,40,21,40⟩ ⟨1,3,5,7,21,40,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,5,7,21,40,21,40⟩ ⟨⟨54,by decide⟩,rfl,rfl⟩

theorem metac1_99:Covered 1 (occurs 1) ⟨1,3,2,7,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,21,40,21,40⟩ ⟨1,3,2,7,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,21,40,21,40⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_100) (by simpa only [upper] using metac1_115)

theorem metac1_116:Covered 1 (occurs 1) ⟨1,3,8,12,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,21,40,21,40⟩ ⟨1,3,8,12,21,40,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,21,40,21,40⟩ ⟨⟨55,by decide⟩,rfl,rfl⟩

theorem metac1_98:Covered 1 (occurs 1) ⟨1,3,2,12,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,21,40,21,40⟩ ⟨1,3,2,12,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,21,40,21,40⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_99) (by simpa only [upper] using metac1_116)

theorem metac1_117:Covered 1 (occurs 1) ⟨4,6,2,12,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,21,40,21,40⟩ ⟨4,6,8,12,21,40,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,21,40,21,40⟩ ⟨⟨56,by decide⟩,rfl,rfl⟩

theorem metac1_97:Covered 1 (occurs 1) ⟨1,11,2,12,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,21,40,21,40⟩ ⟨1,6,2,12,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,21,40,21,40⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_98) (by simpa only [upper] using metac1_117)

theorem metac1_118:Covered 1 (occurs 1) ⟨1,11,13,23,21,40,21,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,21,40,21,40⟩ ⟨1,11,13,23,21,40,21,40⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,21,40,21,40⟩ ⟨⟨57,by decide⟩,rfl,rfl⟩

theorem metac1_96:Covered 1 (occurs 1) ⟨1,11,2,23,21,40,1,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,21,40,1,40⟩ ⟨1,11,2,23,21,40,21,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,21,40,21,40⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_97) (by simpa only [upper] using metac1_118)

theorem metac1_4:Covered 1 (occurs 1) ⟨1,11,2,23,1,70,1,40⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,70,1,40⟩ ⟨1,11,2,23,1,40,1,40⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,40,1,40⟩ ⟨2,by decide⟩ 20 (by simpa only [lower] using metac1_5) (by simpa only [upper] using metac1_96)

theorem metac1_125:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,41,79⟩ ⟨1,3,2,8,1,5,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,8,1,5,41,79⟩ ⟨⟨58,by decide⟩,rfl,rfl⟩

theorem metac1_126:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,41,79⟩ ⟨4,5,8,10,4,5,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,41,79⟩ ⟨⟨59,by decide⟩,rfl,rfl⟩

theorem metac1_124:Covered 1 (occurs 1) ⟨1,5,2,14,1,5,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,14,1,5,41,79⟩ ⟨1,5,2,10,1,5,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,41,79⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_125) (by simpa only [upper] using metac1_126)

theorem metac1_128:Covered 1 (occurs 1) ⟨1,5,2,8,6,9,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,8,6,9,41,79⟩ ⟨1,4,2,8,6,9,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,4,2,8,6,9,41,79⟩ ⟨⟨60,by decide⟩,rfl,rfl⟩

theorem metac1_129:Covered 1 (occurs 1) ⟨1,5,9,14,6,9,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,9,14,6,9,41,79⟩ ⟨1,5,9,14,6,9,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,5,9,14,6,9,41,79⟩ ⟨⟨61,by decide⟩,rfl,rfl⟩

theorem metac1_127:Covered 1 (occurs 1) ⟨1,5,2,14,6,9,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,14,6,9,41,79⟩ ⟨1,5,2,14,6,9,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,14,6,9,41,79⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac1_128) (by simpa only [upper] using metac1_129)

theorem metac1_123:Covered 1 (occurs 1) ⟨1,5,2,18,1,9,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,18,1,9,41,79⟩ ⟨1,5,2,14,1,9,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,14,1,9,41,79⟩ ⟨2,by decide⟩ 5 (by simpa only [lower] using metac1_124) (by simpa only [upper] using metac1_127)

theorem metac1_130:Covered 1 (occurs 1) ⟨6,9,2,18,1,9,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨6,9,2,18,1,9,41,79⟩ ⟨6,9,12,18,6,9,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨6,9,12,18,6,9,41,79⟩ ⟨⟨62,by decide⟩,rfl,rfl⟩

theorem metac1_122:Covered 1 (occurs 1) ⟨1,11,2,23,1,9,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,9,41,79⟩ ⟨1,9,2,18,1,9,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,9,2,18,1,9,41,79⟩ ⟨0,by decide⟩ 5 (by simpa only [lower] using metac1_123) (by simpa only [upper] using metac1_130)

theorem metac1_135:Covered 1 (occurs 1) ⟨1,3,2,4,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,10,18,41,79⟩ ⟨1,2,2,4,10,18,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,4,10,18,41,79⟩ ⟨⟨63,by decide⟩,rfl,rfl⟩

theorem metac1_140:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,41,60⟩ ⟨1,1,5,7,10,14,41,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,10,14,41,60⟩ ⟨⟨64,by decide⟩,rfl,rfl⟩

theorem metac1_143:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,41,50⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,41,50⟩ ⟨1,1,5,6,15,18,41,50⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,15,18,41,50⟩ ⟨⟨65,by decide⟩,rfl,rfl⟩

theorem metac1_144:Covered 1 (occurs 1) ⟨1,1,7,7,15,18,41,50⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,15,18,41,50⟩ ⟨1,1,7,7,15,18,41,50⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,15,18,41,50⟩ ⟨⟨66,by decide⟩,rfl,rfl⟩

theorem metac1_142:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,41,50⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,41,50⟩ ⟨1,1,5,7,15,18,41,50⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,41,50⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_143) (by simpa only [upper] using metac1_144)

theorem metac1_146:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,51,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,51,60⟩ ⟨1,1,5,6,15,18,51,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,15,18,51,60⟩ ⟨⟨67,by decide⟩,rfl,rfl⟩

theorem metac1_147:Covered 1 (occurs 1) ⟨1,1,7,7,15,18,51,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,15,18,51,60⟩ ⟨1,1,7,7,15,18,51,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,15,18,51,60⟩ ⟨⟨68,by decide⟩,rfl,rfl⟩

theorem metac1_145:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,51,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,51,60⟩ ⟨1,1,5,7,15,18,51,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,51,60⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_146) (by simpa only [upper] using metac1_147)

theorem metac1_141:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,41,60⟩ ⟨1,1,5,7,15,18,41,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,41,60⟩ ⟨3,by decide⟩ 50 (by simpa only [lower] using metac1_142) (by simpa only [upper] using metac1_145)

theorem metac1_139:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,41,60⟩ ⟨1,1,5,7,10,18,41,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,41,60⟩ ⟨2,by decide⟩ 14 (by simpa only [lower] using metac1_140) (by simpa only [upper] using metac1_141)

theorem metac1_149:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,61,79⟩ ⟨1,1,5,7,10,14,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,10,14,61,79⟩ ⟨⟨69,by decide⟩,rfl,rfl⟩

theorem metac1_151:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,61,79⟩ ⟨1,1,5,6,15,18,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,15,18,61,79⟩ ⟨⟨70,by decide⟩,rfl,rfl⟩

theorem metac1_152:Covered 1 (occurs 1) ⟨1,1,7,7,15,18,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,15,18,61,79⟩ ⟨1,1,7,7,15,18,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,15,18,61,79⟩ ⟨⟨71,by decide⟩,rfl,rfl⟩

theorem metac1_150:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,61,79⟩ ⟨1,1,5,7,15,18,61,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,61,79⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_151) (by simpa only [upper] using metac1_152)

theorem metac1_148:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,61,79⟩ ⟨1,1,5,7,10,18,61,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,61,79⟩ ⟨2,by decide⟩ 14 (by simpa only [lower] using metac1_149) (by simpa only [upper] using metac1_150)

theorem metac1_138:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,41,79⟩ ⟨1,1,5,7,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,41,79⟩ ⟨3,by decide⟩ 60 (by simpa only [lower] using metac1_139) (by simpa only [upper] using metac1_148)

theorem metac1_153:Covered 1 (occurs 1) ⟨2,2,5,7,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,5,7,10,18,41,79⟩ ⟨2,2,5,7,10,18,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,5,7,10,18,41,79⟩ ⟨⟨72,by decide⟩,rfl,rfl⟩

theorem metac1_137:Covered 1 (occurs 1) ⟨1,2,5,7,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,5,7,10,18,41,79⟩ ⟨1,2,5,7,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,5,7,10,18,41,79⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_138) (by simpa only [upper] using metac1_153)

theorem metac1_154:Covered 1 (occurs 1) ⟨3,3,5,7,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨3,3,5,7,10,18,41,79⟩ ⟨3,3,6,7,10,18,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,3,6,7,10,18,41,79⟩ ⟨⟨73,by decide⟩,rfl,rfl⟩

theorem metac1_136:Covered 1 (occurs 1) ⟨1,3,5,7,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,10,18,41,79⟩ ⟨1,3,5,7,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,5,7,10,18,41,79⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_137) (by simpa only [upper] using metac1_154)

theorem metac1_134:Covered 1 (occurs 1) ⟨1,3,2,7,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,10,18,41,79⟩ ⟨1,3,2,7,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,10,18,41,79⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_135) (by simpa only [upper] using metac1_136)

theorem metac1_155:Covered 1 (occurs 1) ⟨1,3,8,12,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,10,18,41,79⟩ ⟨1,3,8,12,10,18,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,10,18,41,79⟩ ⟨⟨74,by decide⟩,rfl,rfl⟩

theorem metac1_133:Covered 1 (occurs 1) ⟨1,3,2,12,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,10,18,41,79⟩ ⟨1,3,2,12,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,10,18,41,79⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_134) (by simpa only [upper] using metac1_155)

theorem metac1_156:Covered 1 (occurs 1) ⟨4,6,2,12,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,10,18,41,79⟩ ⟨4,6,8,12,10,18,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,10,18,41,79⟩ ⟨⟨75,by decide⟩,rfl,rfl⟩

theorem metac1_132:Covered 1 (occurs 1) ⟨1,11,2,12,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,10,18,41,79⟩ ⟨1,6,2,12,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,10,18,41,79⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_133) (by simpa only [upper] using metac1_156)

theorem metac1_157:Covered 1 (occurs 1) ⟨1,11,13,23,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,10,18,41,79⟩ ⟨1,11,13,23,10,18,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,10,18,41,79⟩ ⟨⟨76,by decide⟩,rfl,rfl⟩

theorem metac1_131:Covered 1 (occurs 1) ⟨1,11,2,23,10,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,10,18,41,79⟩ ⟨1,11,2,23,10,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,10,18,41,79⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_132) (by simpa only [upper] using metac1_157)

theorem metac1_121:Covered 1 (occurs 1) ⟨1,11,2,23,1,18,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,18,41,79⟩ ⟨1,11,2,23,1,18,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,18,41,79⟩ ⟨2,by decide⟩ 9 (by simpa only [lower] using metac1_122) (by simpa only [upper] using metac1_131)

theorem metac1_166:Covered 1 (occurs 1) ⟨1,1,2,3,19,27,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,27,41,60⟩ ⟨1,1,2,3,19,27,41,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,19,27,41,60⟩ ⟨⟨77,by decide⟩,rfl,rfl⟩

theorem metac1_167:Covered 1 (occurs 1) ⟨1,1,2,3,28,35,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,28,35,41,60⟩ ⟨1,1,2,3,28,35,41,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,28,35,41,60⟩ ⟨⟨78,by decide⟩,rfl,rfl⟩

theorem metac1_165:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,41,60⟩ ⟨1,1,2,3,19,35,41,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,41,60⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_166) (by simpa only [upper] using metac1_167)

theorem metac1_169:Covered 1 (occurs 1) ⟨1,1,2,3,19,27,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,27,61,79⟩ ⟨1,1,2,3,19,27,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,19,27,61,79⟩ ⟨⟨79,by decide⟩,rfl,rfl⟩

theorem metac1_170:Covered 1 (occurs 1) ⟨1,1,2,3,28,35,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,28,35,61,79⟩ ⟨1,1,2,3,28,35,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,28,35,61,79⟩ ⟨⟨80,by decide⟩,rfl,rfl⟩

theorem metac1_168:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,61,79⟩ ⟨1,1,2,3,19,35,61,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,61,79⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_169) (by simpa only [upper] using metac1_170)

theorem metac1_164:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,41,79⟩ ⟨1,1,2,3,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,41,79⟩ ⟨3,by decide⟩ 60 (by simpa only [lower] using metac1_165) (by simpa only [upper] using metac1_168)

theorem metac1_175:Covered 1 (occurs 1) ⟨1,1,4,4,19,23,41,50⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,23,41,50⟩ ⟨1,1,4,4,19,23,41,50⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,19,23,41,50⟩ ⟨⟨81,by decide⟩,rfl,rfl⟩

theorem metac1_176:Covered 1 (occurs 1) ⟨1,1,4,4,24,27,41,50⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,24,27,41,50⟩ ⟨1,1,4,4,24,27,41,50⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,24,27,41,50⟩ ⟨⟨82,by decide⟩,rfl,rfl⟩

theorem metac1_174:Covered 1 (occurs 1) ⟨1,1,4,4,19,27,41,50⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,27,41,50⟩ ⟨1,1,4,4,19,27,41,50⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,4,4,19,27,41,50⟩ ⟨2,by decide⟩ 23 (by simpa only [lower] using metac1_175) (by simpa only [upper] using metac1_176)

theorem metac1_178:Covered 1 (occurs 1) ⟨1,1,4,4,19,23,51,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,23,51,60⟩ ⟨1,1,4,4,19,23,51,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,19,23,51,60⟩ ⟨⟨83,by decide⟩,rfl,rfl⟩

theorem metac1_179:Covered 1 (occurs 1) ⟨1,1,4,4,24,27,51,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,24,27,51,60⟩ ⟨1,1,4,4,24,27,51,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,24,27,51,60⟩ ⟨⟨84,by decide⟩,rfl,rfl⟩

theorem metac1_177:Covered 1 (occurs 1) ⟨1,1,4,4,19,27,51,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,27,51,60⟩ ⟨1,1,4,4,19,27,51,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,4,4,19,27,51,60⟩ ⟨2,by decide⟩ 23 (by simpa only [lower] using metac1_178) (by simpa only [upper] using metac1_179)

theorem metac1_173:Covered 1 (occurs 1) ⟨1,1,4,4,19,27,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,27,41,60⟩ ⟨1,1,4,4,19,27,41,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,4,4,19,27,41,60⟩ ⟨3,by decide⟩ 50 (by simpa only [lower] using metac1_174) (by simpa only [upper] using metac1_177)

theorem metac1_180:Covered 1 (occurs 1) ⟨1,1,4,4,28,35,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,28,35,41,60⟩ ⟨1,1,4,4,28,35,41,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,28,35,41,60⟩ ⟨⟨85,by decide⟩,rfl,rfl⟩

theorem metac1_172:Covered 1 (occurs 1) ⟨1,1,4,4,19,35,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,35,41,60⟩ ⟨1,1,4,4,19,35,41,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,4,4,19,35,41,60⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_173) (by simpa only [upper] using metac1_180)

theorem metac1_181:Covered 1 (occurs 1) ⟨1,1,4,4,19,35,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,35,61,79⟩ ⟨1,1,4,4,19,35,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,19,35,61,79⟩ ⟨⟨86,by decide⟩,rfl,rfl⟩

theorem metac1_171:Covered 1 (occurs 1) ⟨1,1,4,4,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,35,41,79⟩ ⟨1,1,4,4,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,4,4,19,35,41,79⟩ ⟨3,by decide⟩ 60 (by simpa only [lower] using metac1_172) (by simpa only [upper] using metac1_181)

theorem metac1_163:Covered 1 (occurs 1) ⟨1,1,2,4,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,4,19,35,41,79⟩ ⟨1,1,2,4,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,4,19,35,41,79⟩ ⟨1,by decide⟩ 3 (by simpa only [lower] using metac1_164) (by simpa only [upper] using metac1_171)

theorem metac1_184:Covered 1 (occurs 1) ⟨2,2,4,4,19,27,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,4,4,19,27,41,60⟩ ⟨2,2,4,4,19,27,41,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,4,4,19,27,41,60⟩ ⟨⟨87,by decide⟩,rfl,rfl⟩

theorem metac1_185:Covered 1 (occurs 1) ⟨2,2,4,4,28,35,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,4,4,28,35,41,60⟩ ⟨2,2,4,4,28,35,41,60⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,4,4,28,35,41,60⟩ ⟨⟨88,by decide⟩,rfl,rfl⟩

theorem metac1_183:Covered 1 (occurs 1) ⟨2,2,4,4,19,35,41,60⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,4,4,19,35,41,60⟩ ⟨2,2,4,4,19,35,41,60⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨2,2,4,4,19,35,41,60⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_184) (by simpa only [upper] using metac1_185)

theorem metac1_186:Covered 1 (occurs 1) ⟨2,2,4,4,19,35,61,79⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,4,4,19,35,61,79⟩ ⟨2,2,4,4,19,35,61,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,4,4,19,35,61,79⟩ ⟨⟨89,by decide⟩,rfl,rfl⟩

theorem metac1_182:Covered 1 (occurs 1) ⟨2,2,2,4,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,2,4,19,35,41,79⟩ ⟨2,2,4,4,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨2,2,4,4,19,35,41,79⟩ ⟨3,by decide⟩ 60 (by simpa only [lower] using metac1_183) (by simpa only [upper] using metac1_186)

theorem metac1_162:Covered 1 (occurs 1) ⟨1,3,2,4,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,19,35,41,79⟩ ⟨1,2,2,4,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,2,4,19,35,41,79⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_163) (by simpa only [upper] using metac1_182)

theorem metac1_187:Covered 1 (occurs 1) ⟨1,3,5,7,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,19,35,41,79⟩ ⟨1,3,5,7,19,35,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,5,7,19,35,41,79⟩ ⟨⟨90,by decide⟩,rfl,rfl⟩

theorem metac1_161:Covered 1 (occurs 1) ⟨1,3,2,7,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,19,35,41,79⟩ ⟨1,3,2,7,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,19,35,41,79⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_162) (by simpa only [upper] using metac1_187)

theorem metac1_188:Covered 1 (occurs 1) ⟨1,3,8,12,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,19,35,41,79⟩ ⟨1,3,8,12,19,35,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,19,35,41,79⟩ ⟨⟨91,by decide⟩,rfl,rfl⟩

theorem metac1_160:Covered 1 (occurs 1) ⟨1,3,2,12,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,19,35,41,79⟩ ⟨1,3,2,12,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,19,35,41,79⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_161) (by simpa only [upper] using metac1_188)

theorem metac1_189:Covered 1 (occurs 1) ⟨4,6,2,12,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,19,35,41,79⟩ ⟨4,6,8,12,19,35,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,19,35,41,79⟩ ⟨⟨92,by decide⟩,rfl,rfl⟩

theorem metac1_159:Covered 1 (occurs 1) ⟨1,11,2,12,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,19,35,41,79⟩ ⟨1,6,2,12,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,19,35,41,79⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_160) (by simpa only [upper] using metac1_189)

theorem metac1_190:Covered 1 (occurs 1) ⟨1,11,13,23,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,19,35,41,79⟩ ⟨1,11,13,23,19,35,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,19,35,41,79⟩ ⟨⟨93,by decide⟩,rfl,rfl⟩

theorem metac1_158:Covered 1 (occurs 1) ⟨1,11,2,23,19,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,19,35,41,79⟩ ⟨1,11,2,23,19,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,19,35,41,79⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_159) (by simpa only [upper] using metac1_190)

theorem metac1_120:Covered 1 (occurs 1) ⟨1,11,2,23,1,35,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,35,41,79⟩ ⟨1,11,2,23,1,35,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,35,41,79⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_121) (by simpa only [upper] using metac1_158)

theorem metac1_191:Covered 1 (occurs 1) ⟨1,11,2,23,36,70,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,36,70,41,79⟩ ⟨1,11,2,23,36,70,41,79⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,2,23,36,70,41,79⟩ ⟨⟨94,by decide⟩,rfl,rfl⟩

theorem metac1_119:Covered 1 (occurs 1) ⟨1,11,2,23,1,70,41,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,70,41,79⟩ ⟨1,11,2,23,1,70,41,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,70,41,79⟩ ⟨2,by decide⟩ 35 (by simpa only [lower] using metac1_120) (by simpa only [upper] using metac1_191)

theorem metac1_3:Covered 1 (occurs 1) ⟨1,11,2,23,1,70,1,79⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,70,1,79⟩ ⟨1,11,2,23,1,70,1,79⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,70,1,79⟩ ⟨3,by decide⟩ 40 (by simpa only [lower] using metac1_4) (by simpa only [upper] using metac1_119)

theorem metac1_198:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,80,157⟩ ⟨1,3,2,8,1,5,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,8,1,5,80,157⟩ ⟨⟨95,by decide⟩,rfl,rfl⟩

theorem metac1_199:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,80,157⟩ ⟨4,5,8,10,4,5,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,80,157⟩ ⟨⟨96,by decide⟩,rfl,rfl⟩

theorem metac1_197:Covered 1 (occurs 1) ⟨1,5,2,14,1,5,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,14,1,5,80,157⟩ ⟨1,5,2,10,1,5,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,80,157⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_198) (by simpa only [upper] using metac1_199)

theorem metac1_201:Covered 1 (occurs 1) ⟨1,5,2,8,6,9,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,8,6,9,80,157⟩ ⟨1,4,2,8,6,9,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,4,2,8,6,9,80,157⟩ ⟨⟨97,by decide⟩,rfl,rfl⟩

theorem metac1_202:Covered 1 (occurs 1) ⟨1,5,9,14,6,9,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,9,14,6,9,80,157⟩ ⟨1,5,9,14,6,9,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,5,9,14,6,9,80,157⟩ ⟨⟨98,by decide⟩,rfl,rfl⟩

theorem metac1_200:Covered 1 (occurs 1) ⟨1,5,2,14,6,9,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,14,6,9,80,157⟩ ⟨1,5,2,14,6,9,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,14,6,9,80,157⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac1_201) (by simpa only [upper] using metac1_202)

theorem metac1_196:Covered 1 (occurs 1) ⟨1,5,2,18,1,9,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,18,1,9,80,157⟩ ⟨1,5,2,14,1,9,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,14,1,9,80,157⟩ ⟨2,by decide⟩ 5 (by simpa only [lower] using metac1_197) (by simpa only [upper] using metac1_200)

theorem metac1_203:Covered 1 (occurs 1) ⟨6,9,2,18,1,9,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨6,9,2,18,1,9,80,157⟩ ⟨6,9,12,18,6,9,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨6,9,12,18,6,9,80,157⟩ ⟨⟨99,by decide⟩,rfl,rfl⟩

theorem metac1_195:Covered 1 (occurs 1) ⟨1,11,2,23,1,9,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,9,80,157⟩ ⟨1,9,2,18,1,9,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,9,2,18,1,9,80,157⟩ ⟨0,by decide⟩ 5 (by simpa only [lower] using metac1_196) (by simpa only [upper] using metac1_203)

theorem metac1_208:Covered 1 (occurs 1) ⟨1,3,2,4,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,10,18,80,157⟩ ⟨1,2,2,4,10,18,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,4,10,18,80,157⟩ ⟨⟨100,by decide⟩,rfl,rfl⟩

theorem metac1_213:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,80,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,80,118⟩ ⟨1,1,5,7,10,14,80,118⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,10,14,80,118⟩ ⟨⟨101,by decide⟩,rfl,rfl⟩

theorem metac1_217:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,80,89⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,80,89⟩ ⟨1,1,5,6,15,18,80,89⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,15,18,80,89⟩ ⟨⟨102,by decide⟩,rfl,rfl⟩

theorem metac1_219:Covered 1 (occurs 1) ⟨1,1,5,5,15,18,90,99⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,5,15,18,90,99⟩ ⟨1,1,5,5,15,18,90,99⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,5,15,18,90,99⟩ ⟨⟨103,by decide⟩,rfl,rfl⟩

theorem metac1_220:Covered 1 (occurs 1) ⟨1,1,6,6,15,18,90,99⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,6,6,15,18,90,99⟩ ⟨1,1,6,6,15,18,90,99⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,6,6,15,18,90,99⟩ ⟨⟨104,by decide⟩,rfl,rfl⟩

theorem metac1_218:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,90,99⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,90,99⟩ ⟨1,1,5,6,15,18,90,99⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,15,18,90,99⟩ ⟨1,by decide⟩ 5 (by simpa only [lower] using metac1_219) (by simpa only [upper] using metac1_220)

theorem metac1_216:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,80,99⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,80,99⟩ ⟨1,1,5,6,15,18,80,99⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,15,18,80,99⟩ ⟨3,by decide⟩ 89 (by simpa only [lower] using metac1_217) (by simpa only [upper] using metac1_218)

theorem metac1_221:Covered 1 (occurs 1) ⟨1,1,7,7,15,18,80,99⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,15,18,80,99⟩ ⟨1,1,7,7,15,18,80,99⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,15,18,80,99⟩ ⟨⟨105,by decide⟩,rfl,rfl⟩

theorem metac1_215:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,80,99⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,80,99⟩ ⟨1,1,5,7,15,18,80,99⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,80,99⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_216) (by simpa only [upper] using metac1_221)

theorem metac1_224:Covered 1 (occurs 1) ⟨1,1,5,5,15,18,100,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,5,15,18,100,118⟩ ⟨1,1,5,5,15,18,100,118⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,5,15,18,100,118⟩ ⟨⟨106,by decide⟩,rfl,rfl⟩

theorem metac1_225:Covered 1 (occurs 1) ⟨1,1,6,6,15,18,100,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,6,6,15,18,100,118⟩ ⟨1,1,6,6,15,18,100,118⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,6,6,15,18,100,118⟩ ⟨⟨107,by decide⟩,rfl,rfl⟩

theorem metac1_223:Covered 1 (occurs 1) ⟨1,1,5,6,15,18,100,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,15,18,100,118⟩ ⟨1,1,5,6,15,18,100,118⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,6,15,18,100,118⟩ ⟨1,by decide⟩ 5 (by simpa only [lower] using metac1_224) (by simpa only [upper] using metac1_225)

theorem metac1_226:Covered 1 (occurs 1) ⟨1,1,7,7,15,18,100,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,15,18,100,118⟩ ⟨1,1,7,7,15,18,100,118⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,15,18,100,118⟩ ⟨⟨108,by decide⟩,rfl,rfl⟩

theorem metac1_222:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,100,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,100,118⟩ ⟨1,1,5,7,15,18,100,118⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,100,118⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_223) (by simpa only [upper] using metac1_226)

theorem metac1_214:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,80,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,80,118⟩ ⟨1,1,5,7,15,18,80,118⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,15,18,80,118⟩ ⟨3,by decide⟩ 99 (by simpa only [lower] using metac1_215) (by simpa only [upper] using metac1_222)

theorem metac1_212:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,80,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,80,118⟩ ⟨1,1,5,7,10,18,80,118⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,80,118⟩ ⟨2,by decide⟩ 14 (by simpa only [lower] using metac1_213) (by simpa only [upper] using metac1_214)

theorem metac1_229:Covered 1 (occurs 1) ⟨1,1,5,6,10,14,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,10,14,119,157⟩ ⟨1,1,5,6,10,14,119,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,10,14,119,157⟩ ⟨⟨109,by decide⟩,rfl,rfl⟩

theorem metac1_230:Covered 1 (occurs 1) ⟨1,1,7,7,10,14,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,10,14,119,157⟩ ⟨1,1,7,7,10,14,119,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,10,14,119,157⟩ ⟨⟨110,by decide⟩,rfl,rfl⟩

theorem metac1_228:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,119,157⟩ ⟨1,1,5,7,10,14,119,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,14,119,157⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_229) (by simpa only [upper] using metac1_230)

theorem metac1_231:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,119,157⟩ ⟨1,1,5,7,15,18,119,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,15,18,119,157⟩ ⟨⟨111,by decide⟩,rfl,rfl⟩

theorem metac1_227:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,119,157⟩ ⟨1,1,5,7,10,18,119,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,119,157⟩ ⟨2,by decide⟩ 14 (by simpa only [lower] using metac1_228) (by simpa only [upper] using metac1_231)

theorem metac1_211:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,80,157⟩ ⟨1,1,5,7,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,80,157⟩ ⟨3,by decide⟩ 118 (by simpa only [lower] using metac1_212) (by simpa only [upper] using metac1_227)

theorem metac1_232:Covered 1 (occurs 1) ⟨2,2,5,7,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,5,7,10,18,80,157⟩ ⟨2,2,5,7,10,18,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,5,7,10,18,80,157⟩ ⟨⟨112,by decide⟩,rfl,rfl⟩

theorem metac1_210:Covered 1 (occurs 1) ⟨1,2,5,7,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,5,7,10,18,80,157⟩ ⟨1,2,5,7,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,5,7,10,18,80,157⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_211) (by simpa only [upper] using metac1_232)

theorem metac1_233:Covered 1 (occurs 1) ⟨3,3,5,7,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨3,3,5,7,10,18,80,157⟩ ⟨3,3,6,7,10,18,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,3,6,7,10,18,80,157⟩ ⟨⟨113,by decide⟩,rfl,rfl⟩

theorem metac1_209:Covered 1 (occurs 1) ⟨1,3,5,7,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,10,18,80,157⟩ ⟨1,3,5,7,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,5,7,10,18,80,157⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_210) (by simpa only [upper] using metac1_233)

theorem metac1_207:Covered 1 (occurs 1) ⟨1,3,2,7,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,10,18,80,157⟩ ⟨1,3,2,7,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,10,18,80,157⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_208) (by simpa only [upper] using metac1_209)

theorem metac1_234:Covered 1 (occurs 1) ⟨1,3,8,12,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,10,18,80,157⟩ ⟨1,3,8,12,10,18,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,10,18,80,157⟩ ⟨⟨114,by decide⟩,rfl,rfl⟩

theorem metac1_206:Covered 1 (occurs 1) ⟨1,3,2,12,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,10,18,80,157⟩ ⟨1,3,2,12,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,10,18,80,157⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_207) (by simpa only [upper] using metac1_234)

theorem metac1_235:Covered 1 (occurs 1) ⟨4,6,2,12,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,10,18,80,157⟩ ⟨4,6,8,12,10,18,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,10,18,80,157⟩ ⟨⟨115,by decide⟩,rfl,rfl⟩

theorem metac1_205:Covered 1 (occurs 1) ⟨1,11,2,12,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,10,18,80,157⟩ ⟨1,6,2,12,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,10,18,80,157⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_206) (by simpa only [upper] using metac1_235)

theorem metac1_236:Covered 1 (occurs 1) ⟨1,11,13,23,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,10,18,80,157⟩ ⟨1,11,13,23,10,18,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,10,18,80,157⟩ ⟨⟨116,by decide⟩,rfl,rfl⟩

theorem metac1_204:Covered 1 (occurs 1) ⟨1,11,2,23,10,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,10,18,80,157⟩ ⟨1,11,2,23,10,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,10,18,80,157⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_205) (by simpa only [upper] using metac1_236)

theorem metac1_194:Covered 1 (occurs 1) ⟨1,11,2,23,1,18,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,18,80,157⟩ ⟨1,11,2,23,1,18,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,18,80,157⟩ ⟨2,by decide⟩ 9 (by simpa only [lower] using metac1_195) (by simpa only [upper] using metac1_204)

theorem metac1_245:Covered 1 (occurs 1) ⟨1,1,2,3,19,27,80,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,27,80,118⟩ ⟨1,1,2,3,19,27,80,118⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,19,27,80,118⟩ ⟨⟨117,by decide⟩,rfl,rfl⟩

theorem metac1_246:Covered 1 (occurs 1) ⟨1,1,2,3,28,35,80,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,28,35,80,118⟩ ⟨1,1,2,3,28,35,80,118⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,28,35,80,118⟩ ⟨⟨118,by decide⟩,rfl,rfl⟩

theorem metac1_244:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,80,118⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,80,118⟩ ⟨1,1,2,3,19,35,80,118⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,80,118⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_245) (by simpa only [upper] using metac1_246)

theorem metac1_248:Covered 1 (occurs 1) ⟨1,1,2,3,19,27,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,27,119,157⟩ ⟨1,1,2,3,19,27,119,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,19,27,119,157⟩ ⟨⟨119,by decide⟩,rfl,rfl⟩

theorem metac1_249:Covered 1 (occurs 1) ⟨1,1,2,3,28,35,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,28,35,119,157⟩ ⟨1,1,2,3,28,35,119,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,28,35,119,157⟩ ⟨⟨120,by decide⟩,rfl,rfl⟩

theorem metac1_247:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,119,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,119,157⟩ ⟨1,1,2,3,19,35,119,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,119,157⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_248) (by simpa only [upper] using metac1_249)

theorem metac1_243:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,80,157⟩ ⟨1,1,2,3,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,80,157⟩ ⟨3,by decide⟩ 118 (by simpa only [lower] using metac1_244) (by simpa only [upper] using metac1_247)

theorem metac1_250:Covered 1 (occurs 1) ⟨1,1,4,4,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,35,80,157⟩ ⟨1,1,4,4,19,35,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,19,35,80,157⟩ ⟨⟨121,by decide⟩,rfl,rfl⟩

theorem metac1_242:Covered 1 (occurs 1) ⟨1,1,2,4,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,4,19,35,80,157⟩ ⟨1,1,2,4,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,4,19,35,80,157⟩ ⟨1,by decide⟩ 3 (by simpa only [lower] using metac1_243) (by simpa only [upper] using metac1_250)

theorem metac1_251:Covered 1 (occurs 1) ⟨2,2,2,4,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,2,4,19,35,80,157⟩ ⟨2,2,4,4,19,35,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,4,4,19,35,80,157⟩ ⟨⟨122,by decide⟩,rfl,rfl⟩

theorem metac1_241:Covered 1 (occurs 1) ⟨1,3,2,4,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,19,35,80,157⟩ ⟨1,2,2,4,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,2,4,19,35,80,157⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_242) (by simpa only [upper] using metac1_251)

theorem metac1_252:Covered 1 (occurs 1) ⟨1,3,5,7,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,19,35,80,157⟩ ⟨1,3,5,7,19,35,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,5,7,19,35,80,157⟩ ⟨⟨123,by decide⟩,rfl,rfl⟩

theorem metac1_240:Covered 1 (occurs 1) ⟨1,3,2,7,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,19,35,80,157⟩ ⟨1,3,2,7,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,19,35,80,157⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_241) (by simpa only [upper] using metac1_252)

theorem metac1_253:Covered 1 (occurs 1) ⟨1,3,8,12,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,19,35,80,157⟩ ⟨1,3,8,12,19,35,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,19,35,80,157⟩ ⟨⟨124,by decide⟩,rfl,rfl⟩

theorem metac1_239:Covered 1 (occurs 1) ⟨1,3,2,12,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,19,35,80,157⟩ ⟨1,3,2,12,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,19,35,80,157⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_240) (by simpa only [upper] using metac1_253)

theorem metac1_254:Covered 1 (occurs 1) ⟨4,6,2,12,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,19,35,80,157⟩ ⟨4,6,8,12,19,35,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,19,35,80,157⟩ ⟨⟨125,by decide⟩,rfl,rfl⟩

theorem metac1_238:Covered 1 (occurs 1) ⟨1,11,2,12,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,19,35,80,157⟩ ⟨1,6,2,12,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,19,35,80,157⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_239) (by simpa only [upper] using metac1_254)

theorem metac1_255:Covered 1 (occurs 1) ⟨1,11,13,23,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,19,35,80,157⟩ ⟨1,11,13,23,19,35,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,19,35,80,157⟩ ⟨⟨126,by decide⟩,rfl,rfl⟩

theorem metac1_237:Covered 1 (occurs 1) ⟨1,11,2,23,19,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,19,35,80,157⟩ ⟨1,11,2,23,19,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,19,35,80,157⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_238) (by simpa only [upper] using metac1_255)

theorem metac1_193:Covered 1 (occurs 1) ⟨1,11,2,23,1,35,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,35,80,157⟩ ⟨1,11,2,23,1,35,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,35,80,157⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_194) (by simpa only [upper] using metac1_237)

theorem metac1_256:Covered 1 (occurs 1) ⟨1,11,2,23,36,70,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,36,70,80,157⟩ ⟨1,11,2,23,36,70,80,157⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,2,23,36,70,80,157⟩ ⟨⟨127,by decide⟩,rfl,rfl⟩

theorem metac1_192:Covered 1 (occurs 1) ⟨1,11,2,23,1,70,80,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,70,80,157⟩ ⟨1,11,2,23,1,70,80,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,70,80,157⟩ ⟨2,by decide⟩ 35 (by simpa only [lower] using metac1_193) (by simpa only [upper] using metac1_256)

theorem metac1_2:Covered 1 (occurs 1) ⟨1,11,2,23,1,70,1,157⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,70,1,157⟩ ⟨1,11,2,23,1,70,1,157⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,70,1,157⟩ ⟨3,by decide⟩ 79 (by simpa only [lower] using metac1_3) (by simpa only [upper] using metac1_192)

theorem metac1_264:Covered 1 (occurs 1) ⟨1,3,2,8,1,3,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,8,1,3,158,314⟩ ⟨1,3,2,6,1,3,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,2,6,1,3,158,314⟩ ⟨⟨128,by decide⟩,rfl,rfl⟩

theorem metac1_266:Covered 1 (occurs 1) ⟨1,3,2,5,4,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,5,4,5,158,314⟩ ⟨1,2,2,5,4,5,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,5,4,5,158,314⟩ ⟨⟨129,by decide⟩,rfl,rfl⟩

theorem metac1_268:Covered 1 (occurs 1) ⟨1,2,6,8,4,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,6,8,4,5,158,314⟩ ⟨1,2,6,7,4,5,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,6,7,4,5,158,314⟩ ⟨⟨130,by decide⟩,rfl,rfl⟩

theorem metac1_269:Covered 1 (occurs 1) ⟨3,3,6,8,4,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨3,3,6,8,4,5,158,314⟩ ⟨3,3,6,8,4,5,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,3,6,8,4,5,158,314⟩ ⟨⟨131,by decide⟩,rfl,rfl⟩

theorem metac1_267:Covered 1 (occurs 1) ⟨1,3,6,8,4,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,6,8,4,5,158,314⟩ ⟨1,3,6,8,4,5,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,6,8,4,5,158,314⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_268) (by simpa only [upper] using metac1_269)

theorem metac1_265:Covered 1 (occurs 1) ⟨1,3,2,8,4,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,8,4,5,158,314⟩ ⟨1,3,2,8,4,5,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,8,4,5,158,314⟩ ⟨1,by decide⟩ 5 (by simpa only [lower] using metac1_266) (by simpa only [upper] using metac1_267)

theorem metac1_263:Covered 1 (occurs 1) ⟨1,3,2,10,1,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,10,1,5,158,314⟩ ⟨1,3,2,8,1,5,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,8,1,5,158,314⟩ ⟨2,by decide⟩ 3 (by simpa only [lower] using metac1_264) (by simpa only [upper] using metac1_265)

theorem metac1_270:Covered 1 (occurs 1) ⟨4,5,2,10,1,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨4,5,2,10,1,5,158,314⟩ ⟨4,5,8,10,4,5,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,5,8,10,4,5,158,314⟩ ⟨⟨132,by decide⟩,rfl,rfl⟩

theorem metac1_262:Covered 1 (occurs 1) ⟨1,5,2,14,1,5,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,14,1,5,158,314⟩ ⟨1,5,2,10,1,5,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,10,1,5,158,314⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_263) (by simpa only [upper] using metac1_270)

theorem metac1_274:Covered 1 (occurs 1) ⟨1,2,2,5,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,2,5,6,9,158,314⟩ ⟨1,2,2,5,6,9,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,5,6,9,158,314⟩ ⟨⟨133,by decide⟩,rfl,rfl⟩

theorem metac1_275:Covered 1 (occurs 1) ⟨1,2,6,8,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,6,8,6,9,158,314⟩ ⟨1,2,6,8,6,9,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,6,8,6,9,158,314⟩ ⟨⟨134,by decide⟩,rfl,rfl⟩

theorem metac1_273:Covered 1 (occurs 1) ⟨1,2,2,8,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,2,8,6,9,158,314⟩ ⟨1,2,2,8,6,9,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,2,8,6,9,158,314⟩ ⟨1,by decide⟩ 5 (by simpa only [lower] using metac1_274) (by simpa only [upper] using metac1_275)

theorem metac1_276:Covered 1 (occurs 1) ⟨3,4,2,8,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨3,4,2,8,6,9,158,314⟩ ⟨3,4,6,8,6,9,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,4,6,8,6,9,158,314⟩ ⟨⟨135,by decide⟩,rfl,rfl⟩

theorem metac1_272:Covered 1 (occurs 1) ⟨1,5,2,8,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,8,6,9,158,314⟩ ⟨1,4,2,8,6,9,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,4,2,8,6,9,158,314⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_273) (by simpa only [upper] using metac1_276)

theorem metac1_277:Covered 1 (occurs 1) ⟨1,5,9,14,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,9,14,6,9,158,314⟩ ⟨1,5,9,14,6,9,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,5,9,14,6,9,158,314⟩ ⟨⟨136,by decide⟩,rfl,rfl⟩

theorem metac1_271:Covered 1 (occurs 1) ⟨1,5,2,14,6,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,14,6,9,158,314⟩ ⟨1,5,2,14,6,9,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,14,6,9,158,314⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac1_272) (by simpa only [upper] using metac1_277)

theorem metac1_261:Covered 1 (occurs 1) ⟨1,5,2,18,1,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,5,2,18,1,9,158,314⟩ ⟨1,5,2,14,1,9,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,5,2,14,1,9,158,314⟩ ⟨2,by decide⟩ 5 (by simpa only [lower] using metac1_262) (by simpa only [upper] using metac1_271)

theorem metac1_278:Covered 1 (occurs 1) ⟨6,9,2,18,1,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨6,9,2,18,1,9,158,314⟩ ⟨6,9,12,18,6,9,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨6,9,12,18,6,9,158,314⟩ ⟨⟨137,by decide⟩,rfl,rfl⟩

theorem metac1_260:Covered 1 (occurs 1) ⟨1,11,2,23,1,9,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,9,158,314⟩ ⟨1,9,2,18,1,9,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,9,2,18,1,9,158,314⟩ ⟨0,by decide⟩ 5 (by simpa only [lower] using metac1_261) (by simpa only [upper] using metac1_278)

theorem metac1_283:Covered 1 (occurs 1) ⟨1,3,2,4,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,10,18,158,314⟩ ⟨1,2,2,4,10,18,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,2,2,4,10,18,158,314⟩ ⟨⟨138,by decide⟩,rfl,rfl⟩

theorem metac1_290:Covered 1 (occurs 1) ⟨1,1,5,6,10,14,158,197⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,6,10,14,158,197⟩ ⟨1,1,5,6,10,14,158,197⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,6,10,14,158,197⟩ ⟨⟨139,by decide⟩,rfl,rfl⟩

theorem metac1_291:Covered 1 (occurs 1) ⟨1,1,7,7,10,14,158,197⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,7,7,10,14,158,197⟩ ⟨1,1,7,7,10,14,158,197⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,7,7,10,14,158,197⟩ ⟨⟨140,by decide⟩,rfl,rfl⟩

theorem metac1_289:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,158,197⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,158,197⟩ ⟨1,1,5,7,10,14,158,197⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,14,158,197⟩ ⟨1,by decide⟩ 6 (by simpa only [lower] using metac1_290) (by simpa only [upper] using metac1_291)

theorem metac1_292:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,198,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,198,236⟩ ⟨1,1,5,7,10,14,198,236⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,10,14,198,236⟩ ⟨⟨141,by decide⟩,rfl,rfl⟩

theorem metac1_288:Covered 1 (occurs 1) ⟨1,1,5,7,10,14,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,14,158,236⟩ ⟨1,1,5,7,10,14,158,236⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,14,158,236⟩ ⟨3,by decide⟩ 197 (by simpa only [lower] using metac1_289) (by simpa only [upper] using metac1_292)

theorem metac1_293:Covered 1 (occurs 1) ⟨1,1,5,7,15,18,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,15,18,158,236⟩ ⟨1,1,5,7,15,18,158,236⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,15,18,158,236⟩ ⟨⟨142,by decide⟩,rfl,rfl⟩

theorem metac1_287:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,158,236⟩ ⟨1,1,5,7,10,18,158,236⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,158,236⟩ ⟨2,by decide⟩ 14 (by simpa only [lower] using metac1_288) (by simpa only [upper] using metac1_293)

theorem metac1_294:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,237,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,237,314⟩ ⟨1,1,5,7,10,18,237,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,5,7,10,18,237,314⟩ ⟨⟨143,by decide⟩,rfl,rfl⟩

theorem metac1_286:Covered 1 (occurs 1) ⟨1,1,5,7,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,5,7,10,18,158,314⟩ ⟨1,1,5,7,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,5,7,10,18,158,314⟩ ⟨3,by decide⟩ 236 (by simpa only [lower] using metac1_287) (by simpa only [upper] using metac1_294)

theorem metac1_295:Covered 1 (occurs 1) ⟨2,2,5,7,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,5,7,10,18,158,314⟩ ⟨2,2,5,7,10,18,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,5,7,10,18,158,314⟩ ⟨⟨144,by decide⟩,rfl,rfl⟩

theorem metac1_285:Covered 1 (occurs 1) ⟨1,2,5,7,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,2,5,7,10,18,158,314⟩ ⟨1,2,5,7,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,5,7,10,18,158,314⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_286) (by simpa only [upper] using metac1_295)

theorem metac1_296:Covered 1 (occurs 1) ⟨3,3,5,7,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨3,3,5,7,10,18,158,314⟩ ⟨3,3,6,7,10,18,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨3,3,6,7,10,18,158,314⟩ ⟨⟨145,by decide⟩,rfl,rfl⟩

theorem metac1_284:Covered 1 (occurs 1) ⟨1,3,5,7,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,10,18,158,314⟩ ⟨1,3,5,7,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,5,7,10,18,158,314⟩ ⟨0,by decide⟩ 2 (by simpa only [lower] using metac1_285) (by simpa only [upper] using metac1_296)

theorem metac1_282:Covered 1 (occurs 1) ⟨1,3,2,7,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,10,18,158,314⟩ ⟨1,3,2,7,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,10,18,158,314⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_283) (by simpa only [upper] using metac1_284)

theorem metac1_297:Covered 1 (occurs 1) ⟨1,3,8,12,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,10,18,158,314⟩ ⟨1,3,8,12,10,18,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,10,18,158,314⟩ ⟨⟨146,by decide⟩,rfl,rfl⟩

theorem metac1_281:Covered 1 (occurs 1) ⟨1,3,2,12,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,10,18,158,314⟩ ⟨1,3,2,12,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,10,18,158,314⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_282) (by simpa only [upper] using metac1_297)

theorem metac1_298:Covered 1 (occurs 1) ⟨4,6,2,12,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,10,18,158,314⟩ ⟨4,6,8,12,10,18,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,10,18,158,314⟩ ⟨⟨147,by decide⟩,rfl,rfl⟩

theorem metac1_280:Covered 1 (occurs 1) ⟨1,11,2,12,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,10,18,158,314⟩ ⟨1,6,2,12,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,10,18,158,314⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_281) (by simpa only [upper] using metac1_298)

theorem metac1_299:Covered 1 (occurs 1) ⟨1,11,13,23,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,10,18,158,314⟩ ⟨1,11,13,23,10,18,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,10,18,158,314⟩ ⟨⟨148,by decide⟩,rfl,rfl⟩

theorem metac1_279:Covered 1 (occurs 1) ⟨1,11,2,23,10,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,10,18,158,314⟩ ⟨1,11,2,23,10,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,10,18,158,314⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_280) (by simpa only [upper] using metac1_299)

theorem metac1_259:Covered 1 (occurs 1) ⟨1,11,2,23,1,18,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,18,158,314⟩ ⟨1,11,2,23,1,18,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,18,158,314⟩ ⟨2,by decide⟩ 9 (by simpa only [lower] using metac1_260) (by simpa only [upper] using metac1_279)

theorem metac1_309:Covered 1 (occurs 1) ⟨1,1,2,2,19,27,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,2,19,27,158,236⟩ ⟨1,1,2,2,19,27,158,236⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,2,19,27,158,236⟩ ⟨⟨149,by decide⟩,rfl,rfl⟩

theorem metac1_310:Covered 1 (occurs 1) ⟨1,1,3,3,19,27,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,3,3,19,27,158,236⟩ ⟨1,1,3,3,19,27,158,236⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,3,3,19,27,158,236⟩ ⟨⟨150,by decide⟩,rfl,rfl⟩

theorem metac1_308:Covered 1 (occurs 1) ⟨1,1,2,3,19,27,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,27,158,236⟩ ⟨1,1,2,3,19,27,158,236⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,27,158,236⟩ ⟨1,by decide⟩ 2 (by simpa only [lower] using metac1_309) (by simpa only [upper] using metac1_310)

theorem metac1_311:Covered 1 (occurs 1) ⟨1,1,2,3,28,35,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,28,35,158,236⟩ ⟨1,1,2,3,28,35,158,236⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,28,35,158,236⟩ ⟨⟨151,by decide⟩,rfl,rfl⟩

theorem metac1_307:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,158,236⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,158,236⟩ ⟨1,1,2,3,19,35,158,236⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,158,236⟩ ⟨2,by decide⟩ 27 (by simpa only [lower] using metac1_308) (by simpa only [upper] using metac1_311)

theorem metac1_312:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,237,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,237,314⟩ ⟨1,1,2,3,19,35,237,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,2,3,19,35,237,314⟩ ⟨⟨152,by decide⟩,rfl,rfl⟩

theorem metac1_306:Covered 1 (occurs 1) ⟨1,1,2,3,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,3,19,35,158,314⟩ ⟨1,1,2,3,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,3,19,35,158,314⟩ ⟨3,by decide⟩ 236 (by simpa only [lower] using metac1_307) (by simpa only [upper] using metac1_312)

theorem metac1_313:Covered 1 (occurs 1) ⟨1,1,4,4,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,4,4,19,35,158,314⟩ ⟨1,1,4,4,19,35,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,1,4,4,19,35,158,314⟩ ⟨⟨153,by decide⟩,rfl,rfl⟩

theorem metac1_305:Covered 1 (occurs 1) ⟨1,1,2,4,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,1,2,4,19,35,158,314⟩ ⟨1,1,2,4,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,1,2,4,19,35,158,314⟩ ⟨1,by decide⟩ 3 (by simpa only [lower] using metac1_306) (by simpa only [upper] using metac1_313)

theorem metac1_314:Covered 1 (occurs 1) ⟨2,2,2,4,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨2,2,2,4,19,35,158,314⟩ ⟨2,2,4,4,19,35,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨2,2,4,4,19,35,158,314⟩ ⟨⟨154,by decide⟩,rfl,rfl⟩

theorem metac1_304:Covered 1 (occurs 1) ⟨1,3,2,4,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,4,19,35,158,314⟩ ⟨1,2,2,4,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,2,2,4,19,35,158,314⟩ ⟨0,by decide⟩ 1 (by simpa only [lower] using metac1_305) (by simpa only [upper] using metac1_314)

theorem metac1_315:Covered 1 (occurs 1) ⟨1,3,5,7,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,5,7,19,35,158,314⟩ ⟨1,3,5,7,19,35,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,5,7,19,35,158,314⟩ ⟨⟨155,by decide⟩,rfl,rfl⟩

theorem metac1_303:Covered 1 (occurs 1) ⟨1,3,2,7,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,7,19,35,158,314⟩ ⟨1,3,2,7,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,7,19,35,158,314⟩ ⟨1,by decide⟩ 4 (by simpa only [lower] using metac1_304) (by simpa only [upper] using metac1_315)

theorem metac1_316:Covered 1 (occurs 1) ⟨1,3,8,12,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,8,12,19,35,158,314⟩ ⟨1,3,8,12,19,35,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,3,8,12,19,35,158,314⟩ ⟨⟨156,by decide⟩,rfl,rfl⟩

theorem metac1_302:Covered 1 (occurs 1) ⟨1,3,2,12,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,3,2,12,19,35,158,314⟩ ⟨1,3,2,12,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,3,2,12,19,35,158,314⟩ ⟨1,by decide⟩ 7 (by simpa only [lower] using metac1_303) (by simpa only [upper] using metac1_316)

theorem metac1_317:Covered 1 (occurs 1) ⟨4,6,2,12,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨4,6,2,12,19,35,158,314⟩ ⟨4,6,8,12,19,35,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨4,6,8,12,19,35,158,314⟩ ⟨⟨157,by decide⟩,rfl,rfl⟩

theorem metac1_301:Covered 1 (occurs 1) ⟨1,11,2,12,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,12,19,35,158,314⟩ ⟨1,6,2,12,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,6,2,12,19,35,158,314⟩ ⟨0,by decide⟩ 3 (by simpa only [lower] using metac1_302) (by simpa only [upper] using metac1_317)

theorem metac1_318:Covered 1 (occurs 1) ⟨1,11,13,23,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,13,23,19,35,158,314⟩ ⟨1,11,13,23,19,35,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,13,23,19,35,158,314⟩ ⟨⟨158,by decide⟩,rfl,rfl⟩

theorem metac1_300:Covered 1 (occurs 1) ⟨1,11,2,23,19,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,19,35,158,314⟩ ⟨1,11,2,23,19,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,19,35,158,314⟩ ⟨1,by decide⟩ 12 (by simpa only [lower] using metac1_301) (by simpa only [upper] using metac1_318)

theorem metac1_258:Covered 1 (occurs 1) ⟨1,11,2,23,1,35,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,35,158,314⟩ ⟨1,11,2,23,1,35,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,35,158,314⟩ ⟨2,by decide⟩ 18 (by simpa only [lower] using metac1_259) (by simpa only [upper] using metac1_300)

theorem metac1_319:Covered 1 (occurs 1) ⟨1,11,2,23,36,70,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,36,70,158,314⟩ ⟨1,11,2,23,36,70,158,314⟩ (by decide+kernel)
 exact covered_leaf 1 (occurs 1) ⟨1,11,2,23,36,70,158,314⟩ ⟨⟨159,by decide⟩,rfl,rfl⟩

theorem metac1_257:Covered 1 (occurs 1) ⟨1,11,2,23,1,70,158,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,1,70,158,314⟩ ⟨1,11,2,23,1,70,158,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,70,158,314⟩ ⟨2,by decide⟩ 35 (by simpa only [lower] using metac1_258) (by simpa only [upper] using metac1_319)

theorem metac1_1:Covered 1 (occurs 1) ⟨1,11,2,23,0,70,0,314⟩:=by
 apply AO 1 (occurs 1) ⟨1,11,2,23,0,70,0,314⟩ ⟨1,11,2,23,1,70,1,314⟩ (by decide+kernel)
 exact BJ 1 (occurs 1) ⟨1,11,2,23,1,70,1,314⟩ ⟨3,by decide⟩ 157 (by simpa only [lower] using metac1_2) (by simpa only [upper] using metac1_257)

theorem metac2_328:Covered 2 (occurs 2) ⟨2,6,4,22,2,11,2,11⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,22,2,11,2,11⟩ ⟨2,6,4,17,2,11,2,11⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,17,2,11,2,11⟩ ⟨⟨160,by decide⟩,rfl,rfl⟩

theorem metac2_329:Covered 2 (occurs 2) ⟨7,11,4,22,2,11,2,11⟩:=by
 apply AO 2 (occurs 2) ⟨7,11,4,22,2,11,2,11⟩ ⟨7,11,14,22,7,11,7,11⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨7,11,14,22,7,11,7,11⟩ ⟨⟨161,by decide⟩,rfl,rfl⟩

theorem metac2_327:Covered 2 (occurs 2) ⟨2,11,4,22,2,11,2,11⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,22,2,11,2,11⟩ ⟨2,11,4,22,2,11,2,11⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,22,2,11,2,11⟩ ⟨0,by decide⟩ 6 (by simpa only [lower] using metac2_328) (by simpa only [upper] using metac2_329)

theorem metac2_331:Covered 2 (occurs 2) ⟨2,6,4,22,2,11,12,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,22,2,11,12,21⟩ ⟨2,6,4,17,2,11,12,21⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,17,2,11,12,21⟩ ⟨⟨162,by decide⟩,rfl,rfl⟩

theorem metac2_332:Covered 2 (occurs 2) ⟨7,11,4,22,2,11,12,21⟩:=by
 apply AO 2 (occurs 2) ⟨7,11,4,22,2,11,12,21⟩ ⟨7,11,14,22,7,11,12,21⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨7,11,14,22,7,11,12,21⟩ ⟨⟨163,by decide⟩,rfl,rfl⟩

theorem metac2_330:Covered 2 (occurs 2) ⟨2,11,4,22,2,11,12,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,22,2,11,12,21⟩ ⟨2,11,4,22,2,11,12,21⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,22,2,11,12,21⟩ ⟨0,by decide⟩ 6 (by simpa only [lower] using metac2_331) (by simpa only [upper] using metac2_332)

theorem metac2_326:Covered 2 (occurs 2) ⟨2,11,4,23,2,11,2,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,11,2,21⟩ ⟨2,11,4,22,2,11,2,21⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,22,2,11,2,21⟩ ⟨3,by decide⟩ 11 (by simpa only [lower] using metac2_327) (by simpa only [upper] using metac2_330)

theorem metac2_334:Covered 2 (occurs 2) ⟨2,11,4,13,12,21,12,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,12,21,12,21⟩ ⟨2,6,4,13,12,21,12,21⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,13,12,21,12,21⟩ ⟨⟨164,by decide⟩,rfl,rfl⟩

theorem metac2_335:Covered 2 (occurs 2) ⟨2,11,14,23,12,21,12,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,12,21,12,21⟩ ⟨2,11,14,23,12,21,12,21⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,12,21,12,21⟩ ⟨⟨165,by decide⟩,rfl,rfl⟩

theorem metac2_333:Covered 2 (occurs 2) ⟨2,11,4,23,12,21,2,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,12,21,2,21⟩ ⟨2,11,4,23,12,21,12,21⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,12,21,12,21⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_334) (by simpa only [upper] using metac2_335)

theorem metac2_325:Covered 2 (occurs 2) ⟨2,11,4,23,2,21,2,21⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,21,2,21⟩ ⟨2,11,4,23,2,21,2,21⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,21,2,21⟩ ⟨2,by decide⟩ 11 (by simpa only [lower] using metac2_326) (by simpa only [upper] using metac2_333)

theorem metac2_338:Covered 2 (occurs 2) ⟨2,6,4,22,2,11,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,22,2,11,22,41⟩ ⟨2,6,4,17,2,11,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,17,2,11,22,41⟩ ⟨⟨166,by decide⟩,rfl,rfl⟩

theorem metac2_339:Covered 2 (occurs 2) ⟨7,11,4,22,2,11,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨7,11,4,22,2,11,22,41⟩ ⟨7,11,14,22,7,11,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨7,11,14,22,7,11,22,41⟩ ⟨⟨167,by decide⟩,rfl,rfl⟩

theorem metac2_337:Covered 2 (occurs 2) ⟨2,11,4,23,2,11,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,11,22,41⟩ ⟨2,11,4,22,2,11,22,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,22,2,11,22,41⟩ ⟨0,by decide⟩ 6 (by simpa only [lower] using metac2_338) (by simpa only [upper] using metac2_339)

theorem metac2_341:Covered 2 (occurs 2) ⟨2,11,4,13,12,21,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,12,21,22,41⟩ ⟨2,6,4,13,12,21,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,13,12,21,22,41⟩ ⟨⟨168,by decide⟩,rfl,rfl⟩

theorem metac2_342:Covered 2 (occurs 2) ⟨2,11,14,23,12,21,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,12,21,22,41⟩ ⟨2,11,14,23,12,21,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,12,21,22,41⟩ ⟨⟨169,by decide⟩,rfl,rfl⟩

theorem metac2_340:Covered 2 (occurs 2) ⟨2,11,4,23,12,21,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,12,21,22,41⟩ ⟨2,11,4,23,12,21,22,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,12,21,22,41⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_341) (by simpa only [upper] using metac2_342)

theorem metac2_336:Covered 2 (occurs 2) ⟨2,11,4,23,2,21,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,21,22,41⟩ ⟨2,11,4,23,2,21,22,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,21,22,41⟩ ⟨2,by decide⟩ 11 (by simpa only [lower] using metac2_337) (by simpa only [upper] using metac2_340)

theorem metac2_324:Covered 2 (occurs 2) ⟨2,11,4,23,2,21,2,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,21,2,41⟩ ⟨2,11,4,23,2,21,2,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,21,2,41⟩ ⟨3,by decide⟩ 21 (by simpa only [lower] using metac2_325) (by simpa only [upper] using metac2_336)

theorem metac2_345:Covered 2 (occurs 2) ⟨2,6,4,8,22,41,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,8,22,41,22,41⟩ ⟨2,4,4,8,22,41,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,4,4,8,22,41,22,41⟩ ⟨⟨170,by decide⟩,rfl,rfl⟩

theorem metac2_346:Covered 2 (occurs 2) ⟨2,6,9,13,22,41,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,9,13,22,41,22,41⟩ ⟨2,6,9,13,22,41,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,9,13,22,41,22,41⟩ ⟨⟨171,by decide⟩,rfl,rfl⟩

theorem metac2_344:Covered 2 (occurs 2) ⟨2,11,4,13,22,41,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,22,41,22,41⟩ ⟨2,6,4,13,22,41,22,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,6,4,13,22,41,22,41⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac2_345) (by simpa only [upper] using metac2_346)

theorem metac2_347:Covered 2 (occurs 2) ⟨2,11,14,23,22,41,22,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,22,41,22,41⟩ ⟨2,11,14,23,22,41,22,41⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,22,41,22,41⟩ ⟨⟨172,by decide⟩,rfl,rfl⟩

theorem metac2_343:Covered 2 (occurs 2) ⟨2,11,4,23,22,41,2,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,22,41,2,41⟩ ⟨2,11,4,23,22,41,22,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,22,41,22,41⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_344) (by simpa only [upper] using metac2_347)

theorem metac2_323:Covered 2 (occurs 2) ⟨2,11,4,23,2,70,2,41⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,70,2,41⟩ ⟨2,11,4,23,2,41,2,41⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,41,2,41⟩ ⟨2,by decide⟩ 21 (by simpa only [lower] using metac2_324) (by simpa only [upper] using metac2_343)

theorem metac2_352:Covered 2 (occurs 2) ⟨2,6,4,20,2,10,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,20,2,10,42,80⟩ ⟨2,6,4,16,2,10,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,16,2,10,42,80⟩ ⟨⟨173,by decide⟩,rfl,rfl⟩

theorem metac2_353:Covered 2 (occurs 2) ⟨7,10,4,20,2,10,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨7,10,4,20,2,10,42,80⟩ ⟨7,10,14,20,7,10,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨7,10,14,20,7,10,42,80⟩ ⟨⟨174,by decide⟩,rfl,rfl⟩

theorem metac2_351:Covered 2 (occurs 2) ⟨2,11,4,23,2,10,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,10,42,80⟩ ⟨2,10,4,20,2,10,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,10,4,20,2,10,42,80⟩ ⟨0,by decide⟩ 6 (by simpa only [lower] using metac2_352) (by simpa only [upper] using metac2_353)

theorem metac2_355:Covered 2 (occurs 2) ⟨2,11,4,13,11,19,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,11,19,42,80⟩ ⟨2,6,4,13,11,19,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,13,11,19,42,80⟩ ⟨⟨175,by decide⟩,rfl,rfl⟩

theorem metac2_356:Covered 2 (occurs 2) ⟨2,11,14,23,11,19,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,11,19,42,80⟩ ⟨2,11,14,23,11,19,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,11,19,42,80⟩ ⟨⟨176,by decide⟩,rfl,rfl⟩

theorem metac2_354:Covered 2 (occurs 2) ⟨2,11,4,23,11,19,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,11,19,42,80⟩ ⟨2,11,4,23,11,19,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,11,19,42,80⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_355) (by simpa only [upper] using metac2_356)

theorem metac2_350:Covered 2 (occurs 2) ⟨2,11,4,23,2,19,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,19,42,80⟩ ⟨2,11,4,23,2,19,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,19,42,80⟩ ⟨2,by decide⟩ 10 (by simpa only [lower] using metac2_351) (by simpa only [upper] using metac2_354)

theorem metac2_359:Covered 2 (occurs 2) ⟨2,6,4,8,20,36,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,8,20,36,42,80⟩ ⟨2,4,4,8,20,36,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,4,4,8,20,36,42,80⟩ ⟨⟨177,by decide⟩,rfl,rfl⟩

theorem metac2_360:Covered 2 (occurs 2) ⟨2,6,9,13,20,36,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,9,13,20,36,42,80⟩ ⟨2,6,9,13,20,36,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,9,13,20,36,42,80⟩ ⟨⟨178,by decide⟩,rfl,rfl⟩

theorem metac2_358:Covered 2 (occurs 2) ⟨2,11,4,13,20,36,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,20,36,42,80⟩ ⟨2,6,4,13,20,36,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,6,4,13,20,36,42,80⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac2_359) (by simpa only [upper] using metac2_360)

theorem metac2_361:Covered 2 (occurs 2) ⟨2,11,14,23,20,36,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,20,36,42,80⟩ ⟨2,11,14,23,20,36,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,20,36,42,80⟩ ⟨⟨179,by decide⟩,rfl,rfl⟩

theorem metac2_357:Covered 2 (occurs 2) ⟨2,11,4,23,20,36,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,20,36,42,80⟩ ⟨2,11,4,23,20,36,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,20,36,42,80⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_358) (by simpa only [upper] using metac2_361)

theorem metac2_349:Covered 2 (occurs 2) ⟨2,11,4,23,2,36,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,36,42,80⟩ ⟨2,11,4,23,2,36,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,36,42,80⟩ ⟨2,by decide⟩ 19 (by simpa only [lower] using metac2_350) (by simpa only [upper] using metac2_357)

theorem metac2_362:Covered 2 (occurs 2) ⟨2,11,4,23,37,70,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,37,70,42,80⟩ ⟨2,11,4,23,37,70,42,80⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,4,23,37,70,42,80⟩ ⟨⟨180,by decide⟩,rfl,rfl⟩

theorem metac2_348:Covered 2 (occurs 2) ⟨2,11,4,23,2,70,42,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,70,42,80⟩ ⟨2,11,4,23,2,70,42,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,70,42,80⟩ ⟨2,by decide⟩ 36 (by simpa only [lower] using metac2_349) (by simpa only [upper] using metac2_362)

theorem metac2_322:Covered 2 (occurs 2) ⟨2,11,4,23,2,70,2,80⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,70,2,80⟩ ⟨2,11,4,23,2,70,2,80⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,70,2,80⟩ ⟨3,by decide⟩ 41 (by simpa only [lower] using metac2_323) (by simpa only [upper] using metac2_348)

theorem metac2_367:Covered 2 (occurs 2) ⟨2,6,4,20,2,10,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,20,2,10,81,158⟩ ⟨2,6,4,16,2,10,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,16,2,10,81,158⟩ ⟨⟨181,by decide⟩,rfl,rfl⟩

theorem metac2_368:Covered 2 (occurs 2) ⟨7,10,4,20,2,10,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨7,10,4,20,2,10,81,158⟩ ⟨7,10,14,20,7,10,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨7,10,14,20,7,10,81,158⟩ ⟨⟨182,by decide⟩,rfl,rfl⟩

theorem metac2_366:Covered 2 (occurs 2) ⟨2,11,4,23,2,10,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,10,81,158⟩ ⟨2,10,4,20,2,10,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,10,4,20,2,10,81,158⟩ ⟨0,by decide⟩ 6 (by simpa only [lower] using metac2_367) (by simpa only [upper] using metac2_368)

theorem metac2_370:Covered 2 (occurs 2) ⟨2,11,4,13,11,19,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,11,19,81,158⟩ ⟨2,6,4,13,11,19,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,13,11,19,81,158⟩ ⟨⟨183,by decide⟩,rfl,rfl⟩

theorem metac2_371:Covered 2 (occurs 2) ⟨2,11,14,23,11,19,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,11,19,81,158⟩ ⟨2,11,14,23,11,19,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,11,19,81,158⟩ ⟨⟨184,by decide⟩,rfl,rfl⟩

theorem metac2_369:Covered 2 (occurs 2) ⟨2,11,4,23,11,19,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,11,19,81,158⟩ ⟨2,11,4,23,11,19,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,11,19,81,158⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_370) (by simpa only [upper] using metac2_371)

theorem metac2_365:Covered 2 (occurs 2) ⟨2,11,4,23,2,19,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,19,81,158⟩ ⟨2,11,4,23,2,19,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,19,81,158⟩ ⟨2,by decide⟩ 10 (by simpa only [lower] using metac2_366) (by simpa only [upper] using metac2_369)

theorem metac2_374:Covered 2 (occurs 2) ⟨2,6,4,8,20,36,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,8,20,36,81,158⟩ ⟨2,4,4,8,20,36,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,4,4,8,20,36,81,158⟩ ⟨⟨185,by decide⟩,rfl,rfl⟩

theorem metac2_375:Covered 2 (occurs 2) ⟨2,6,9,13,20,36,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,9,13,20,36,81,158⟩ ⟨2,6,9,13,20,36,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,9,13,20,36,81,158⟩ ⟨⟨186,by decide⟩,rfl,rfl⟩

theorem metac2_373:Covered 2 (occurs 2) ⟨2,11,4,13,20,36,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,20,36,81,158⟩ ⟨2,6,4,13,20,36,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,6,4,13,20,36,81,158⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac2_374) (by simpa only [upper] using metac2_375)

theorem metac2_376:Covered 2 (occurs 2) ⟨2,11,14,23,20,36,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,20,36,81,158⟩ ⟨2,11,14,23,20,36,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,20,36,81,158⟩ ⟨⟨187,by decide⟩,rfl,rfl⟩

theorem metac2_372:Covered 2 (occurs 2) ⟨2,11,4,23,20,36,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,20,36,81,158⟩ ⟨2,11,4,23,20,36,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,20,36,81,158⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_373) (by simpa only [upper] using metac2_376)

theorem metac2_364:Covered 2 (occurs 2) ⟨2,11,4,23,2,36,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,36,81,158⟩ ⟨2,11,4,23,2,36,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,36,81,158⟩ ⟨2,by decide⟩ 19 (by simpa only [lower] using metac2_365) (by simpa only [upper] using metac2_372)

theorem metac2_378:Covered 2 (occurs 2) ⟨2,11,4,13,37,70,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,37,70,81,158⟩ ⟨2,6,4,13,37,70,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,13,37,70,81,158⟩ ⟨⟨188,by decide⟩,rfl,rfl⟩

theorem metac2_379:Covered 2 (occurs 2) ⟨2,11,14,23,37,70,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,37,70,81,158⟩ ⟨2,11,14,23,37,70,81,158⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,37,70,81,158⟩ ⟨⟨189,by decide⟩,rfl,rfl⟩

theorem metac2_377:Covered 2 (occurs 2) ⟨2,11,4,23,37,70,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,37,70,81,158⟩ ⟨2,11,4,23,37,70,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,37,70,81,158⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_378) (by simpa only [upper] using metac2_379)

theorem metac2_363:Covered 2 (occurs 2) ⟨2,11,4,23,2,70,81,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,70,81,158⟩ ⟨2,11,4,23,2,70,81,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,70,81,158⟩ ⟨2,by decide⟩ 36 (by simpa only [lower] using metac2_364) (by simpa only [upper] using metac2_377)

theorem metac2_321:Covered 2 (occurs 2) ⟨2,11,4,23,2,70,2,158⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,70,2,158⟩ ⟨2,11,4,23,2,70,2,158⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,70,2,158⟩ ⟨3,by decide⟩ 80 (by simpa only [lower] using metac2_322) (by simpa only [upper] using metac2_363)

theorem metac2_384:Covered 2 (occurs 2) ⟨2,6,4,20,2,10,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,20,2,10,159,314⟩ ⟨2,6,4,16,2,10,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,16,2,10,159,314⟩ ⟨⟨190,by decide⟩,rfl,rfl⟩

theorem metac2_385:Covered 2 (occurs 2) ⟨7,10,4,20,2,10,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨7,10,4,20,2,10,159,314⟩ ⟨7,10,14,20,7,10,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨7,10,14,20,7,10,159,314⟩ ⟨⟨191,by decide⟩,rfl,rfl⟩

theorem metac2_383:Covered 2 (occurs 2) ⟨2,11,4,23,2,10,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,10,159,314⟩ ⟨2,10,4,20,2,10,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,10,4,20,2,10,159,314⟩ ⟨0,by decide⟩ 6 (by simpa only [lower] using metac2_384) (by simpa only [upper] using metac2_385)

theorem metac2_387:Covered 2 (occurs 2) ⟨2,11,4,13,11,19,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,11,19,159,314⟩ ⟨2,6,4,13,11,19,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,4,13,11,19,159,314⟩ ⟨⟨192,by decide⟩,rfl,rfl⟩

theorem metac2_388:Covered 2 (occurs 2) ⟨2,11,14,23,11,19,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,11,19,159,314⟩ ⟨2,11,14,23,11,19,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,11,19,159,314⟩ ⟨⟨193,by decide⟩,rfl,rfl⟩

theorem metac2_386:Covered 2 (occurs 2) ⟨2,11,4,23,11,19,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,11,19,159,314⟩ ⟨2,11,4,23,11,19,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,11,19,159,314⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_387) (by simpa only [upper] using metac2_388)

theorem metac2_382:Covered 2 (occurs 2) ⟨2,11,4,23,2,19,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,19,159,314⟩ ⟨2,11,4,23,2,19,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,19,159,314⟩ ⟨2,by decide⟩ 10 (by simpa only [lower] using metac2_383) (by simpa only [upper] using metac2_386)

theorem metac2_391:Covered 2 (occurs 2) ⟨2,6,4,8,20,36,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,8,20,36,159,314⟩ ⟨2,4,4,8,20,36,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,4,4,8,20,36,159,314⟩ ⟨⟨194,by decide⟩,rfl,rfl⟩

theorem metac2_392:Covered 2 (occurs 2) ⟨2,6,9,13,20,36,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,9,13,20,36,159,314⟩ ⟨2,6,9,13,20,36,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,9,13,20,36,159,314⟩ ⟨⟨195,by decide⟩,rfl,rfl⟩

theorem metac2_390:Covered 2 (occurs 2) ⟨2,11,4,13,20,36,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,20,36,159,314⟩ ⟨2,6,4,13,20,36,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,6,4,13,20,36,159,314⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac2_391) (by simpa only [upper] using metac2_392)

theorem metac2_393:Covered 2 (occurs 2) ⟨2,11,14,23,20,36,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,20,36,159,314⟩ ⟨2,11,14,23,20,36,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,20,36,159,314⟩ ⟨⟨196,by decide⟩,rfl,rfl⟩

theorem metac2_389:Covered 2 (occurs 2) ⟨2,11,4,23,20,36,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,20,36,159,314⟩ ⟨2,11,4,23,20,36,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,20,36,159,314⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_390) (by simpa only [upper] using metac2_393)

theorem metac2_381:Covered 2 (occurs 2) ⟨2,11,4,23,2,36,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,36,159,314⟩ ⟨2,11,4,23,2,36,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,36,159,314⟩ ⟨2,by decide⟩ 19 (by simpa only [lower] using metac2_382) (by simpa only [upper] using metac2_389)

theorem metac2_396:Covered 2 (occurs 2) ⟨2,6,4,8,37,70,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,4,8,37,70,159,314⟩ ⟨2,4,4,8,37,70,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,4,4,8,37,70,159,314⟩ ⟨⟨197,by decide⟩,rfl,rfl⟩

theorem metac2_397:Covered 2 (occurs 2) ⟨2,6,9,13,37,70,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,6,9,13,37,70,159,314⟩ ⟨2,6,9,13,37,70,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,6,9,13,37,70,159,314⟩ ⟨⟨198,by decide⟩,rfl,rfl⟩

theorem metac2_395:Covered 2 (occurs 2) ⟨2,11,4,13,37,70,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,13,37,70,159,314⟩ ⟨2,6,4,13,37,70,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,6,4,13,37,70,159,314⟩ ⟨1,by decide⟩ 8 (by simpa only [lower] using metac2_396) (by simpa only [upper] using metac2_397)

theorem metac2_398:Covered 2 (occurs 2) ⟨2,11,14,23,37,70,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,14,23,37,70,159,314⟩ ⟨2,11,14,23,37,70,159,314⟩ (by decide+kernel)
 exact covered_leaf 2 (occurs 2) ⟨2,11,14,23,37,70,159,314⟩ ⟨⟨199,by decide⟩,rfl,rfl⟩

theorem metac2_394:Covered 2 (occurs 2) ⟨2,11,4,23,37,70,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,37,70,159,314⟩ ⟨2,11,4,23,37,70,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,37,70,159,314⟩ ⟨1,by decide⟩ 13 (by simpa only [lower] using metac2_395) (by simpa only [upper] using metac2_398)

theorem metac2_380:Covered 2 (occurs 2) ⟨2,11,4,23,2,70,159,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,2,70,159,314⟩ ⟨2,11,4,23,2,70,159,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,70,159,314⟩ ⟨2,by decide⟩ 36 (by simpa only [lower] using metac2_381) (by simpa only [upper] using metac2_394)

theorem metac2_320:Covered 2 (occurs 2) ⟨2,11,4,23,0,70,0,314⟩:=by
 apply AO 2 (occurs 2) ⟨2,11,4,23,0,70,0,314⟩ ⟨2,11,4,23,2,70,2,314⟩ (by decide+kernel)
 exact BJ 2 (occurs 2) ⟨2,11,4,23,2,70,2,314⟩ ⟨3,by decide⟩ 158 (by simpa only [lower] using metac2_321) (by simpa only [upper] using metac2_380)

theorem metac3_403:Covered 3 (occurs 3) ⟨3,11,6,23,3,22,3,41⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,22,3,41⟩ ⟨3,11,6,23,3,22,3,41⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,6,23,3,22,3,41⟩ ⟨⟨200,by decide⟩,rfl,rfl⟩

theorem metac3_405:Covered 3 (occurs 3) ⟨3,11,6,14,23,41,23,41⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,14,23,41,23,41⟩ ⟨3,7,6,14,23,41,23,41⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,7,6,14,23,41,23,41⟩ ⟨⟨201,by decide⟩,rfl,rfl⟩

theorem metac3_406:Covered 3 (occurs 3) ⟨3,11,15,23,23,41,23,41⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,15,23,23,41,23,41⟩ ⟨3,11,15,23,23,41,23,41⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,15,23,23,41,23,41⟩ ⟨⟨202,by decide⟩,rfl,rfl⟩

theorem metac3_404:Covered 3 (occurs 3) ⟨3,11,6,23,23,41,3,41⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,23,41,3,41⟩ ⟨3,11,6,23,23,41,23,41⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,23,41,23,41⟩ ⟨1,by decide⟩ 14 (by simpa only [lower] using metac3_405) (by simpa only [upper] using metac3_406)

theorem metac3_402:Covered 3 (occurs 3) ⟨3,11,6,23,3,70,3,41⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,70,3,41⟩ ⟨3,11,6,23,3,41,3,41⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,41,3,41⟩ ⟨2,by decide⟩ 22 (by simpa only [lower] using metac3_403) (by simpa only [upper] using metac3_404)

theorem metac3_408:Covered 3 (occurs 3) ⟨3,11,6,23,3,36,42,80⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,36,42,80⟩ ⟨3,11,6,23,3,36,42,80⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,6,23,3,36,42,80⟩ ⟨⟨203,by decide⟩,rfl,rfl⟩

theorem metac3_410:Covered 3 (occurs 3) ⟨3,11,6,14,37,70,42,80⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,14,37,70,42,80⟩ ⟨3,7,6,14,37,70,42,80⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,7,6,14,37,70,42,80⟩ ⟨⟨204,by decide⟩,rfl,rfl⟩

theorem metac3_411:Covered 3 (occurs 3) ⟨3,11,15,23,37,70,42,80⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,15,23,37,70,42,80⟩ ⟨3,11,15,23,37,70,42,80⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,15,23,37,70,42,80⟩ ⟨⟨205,by decide⟩,rfl,rfl⟩

theorem metac3_409:Covered 3 (occurs 3) ⟨3,11,6,23,37,70,42,80⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,37,70,42,80⟩ ⟨3,11,6,23,37,70,42,80⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,37,70,42,80⟩ ⟨1,by decide⟩ 14 (by simpa only [lower] using metac3_410) (by simpa only [upper] using metac3_411)

theorem metac3_407:Covered 3 (occurs 3) ⟨3,11,6,23,3,70,42,80⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,70,42,80⟩ ⟨3,11,6,23,3,70,42,80⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,70,42,80⟩ ⟨2,by decide⟩ 36 (by simpa only [lower] using metac3_408) (by simpa only [upper] using metac3_409)

theorem metac3_401:Covered 3 (occurs 3) ⟨3,11,6,23,3,70,3,80⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,70,3,80⟩ ⟨3,11,6,23,3,70,3,80⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,70,3,80⟩ ⟨3,by decide⟩ 41 (by simpa only [lower] using metac3_402) (by simpa only [upper] using metac3_407)

theorem metac3_413:Covered 3 (occurs 3) ⟨3,11,6,23,3,36,81,158⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,36,81,158⟩ ⟨3,11,6,23,3,36,81,158⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,6,23,3,36,81,158⟩ ⟨⟨206,by decide⟩,rfl,rfl⟩

theorem metac3_415:Covered 3 (occurs 3) ⟨3,11,6,14,37,70,81,158⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,14,37,70,81,158⟩ ⟨3,7,6,14,37,70,81,158⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,7,6,14,37,70,81,158⟩ ⟨⟨207,by decide⟩,rfl,rfl⟩

theorem metac3_416:Covered 3 (occurs 3) ⟨3,11,15,23,37,70,81,158⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,15,23,37,70,81,158⟩ ⟨3,11,15,23,37,70,81,158⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,15,23,37,70,81,158⟩ ⟨⟨208,by decide⟩,rfl,rfl⟩

theorem metac3_414:Covered 3 (occurs 3) ⟨3,11,6,23,37,70,81,158⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,37,70,81,158⟩ ⟨3,11,6,23,37,70,81,158⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,37,70,81,158⟩ ⟨1,by decide⟩ 14 (by simpa only [lower] using metac3_415) (by simpa only [upper] using metac3_416)

theorem metac3_412:Covered 3 (occurs 3) ⟨3,11,6,23,3,70,81,158⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,70,81,158⟩ ⟨3,11,6,23,3,70,81,158⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,70,81,158⟩ ⟨2,by decide⟩ 36 (by simpa only [lower] using metac3_413) (by simpa only [upper] using metac3_414)

theorem metac3_400:Covered 3 (occurs 3) ⟨3,11,6,23,3,70,3,158⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,70,3,158⟩ ⟨3,11,6,23,3,70,3,158⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,70,3,158⟩ ⟨3,by decide⟩ 80 (by simpa only [lower] using metac3_401) (by simpa only [upper] using metac3_412)

theorem metac3_419:Covered 3 (occurs 3) ⟨3,11,6,23,3,19,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,19,159,314⟩ ⟨3,11,6,23,3,19,159,314⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,6,23,3,19,159,314⟩ ⟨⟨209,by decide⟩,rfl,rfl⟩

theorem metac3_421:Covered 3 (occurs 3) ⟨3,11,6,14,20,36,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,14,20,36,159,314⟩ ⟨3,7,6,14,20,36,159,314⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,7,6,14,20,36,159,314⟩ ⟨⟨210,by decide⟩,rfl,rfl⟩

theorem metac3_422:Covered 3 (occurs 3) ⟨3,11,15,23,20,36,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,15,23,20,36,159,314⟩ ⟨3,11,15,23,20,36,159,314⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,15,23,20,36,159,314⟩ ⟨⟨211,by decide⟩,rfl,rfl⟩

theorem metac3_420:Covered 3 (occurs 3) ⟨3,11,6,23,20,36,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,20,36,159,314⟩ ⟨3,11,6,23,20,36,159,314⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,20,36,159,314⟩ ⟨1,by decide⟩ 14 (by simpa only [lower] using metac3_421) (by simpa only [upper] using metac3_422)

theorem metac3_418:Covered 3 (occurs 3) ⟨3,11,6,23,3,36,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,36,159,314⟩ ⟨3,11,6,23,3,36,159,314⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,36,159,314⟩ ⟨2,by decide⟩ 19 (by simpa only [lower] using metac3_419) (by simpa only [upper] using metac3_420)

theorem metac3_424:Covered 3 (occurs 3) ⟨3,11,6,14,37,70,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,14,37,70,159,314⟩ ⟨3,7,6,14,37,70,159,314⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,7,6,14,37,70,159,314⟩ ⟨⟨212,by decide⟩,rfl,rfl⟩

theorem metac3_425:Covered 3 (occurs 3) ⟨3,11,15,23,37,70,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,15,23,37,70,159,314⟩ ⟨3,11,15,23,37,70,159,314⟩ (by decide+kernel)
 exact covered_leaf 3 (occurs 3) ⟨3,11,15,23,37,70,159,314⟩ ⟨⟨213,by decide⟩,rfl,rfl⟩

theorem metac3_423:Covered 3 (occurs 3) ⟨3,11,6,23,37,70,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,37,70,159,314⟩ ⟨3,11,6,23,37,70,159,314⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,37,70,159,314⟩ ⟨1,by decide⟩ 14 (by simpa only [lower] using metac3_424) (by simpa only [upper] using metac3_425)

theorem metac3_417:Covered 3 (occurs 3) ⟨3,11,6,23,3,70,159,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,3,70,159,314⟩ ⟨3,11,6,23,3,70,159,314⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,70,159,314⟩ ⟨2,by decide⟩ 36 (by simpa only [lower] using metac3_418) (by simpa only [upper] using metac3_423)

theorem metac3_399:Covered 3 (occurs 3) ⟨3,11,6,23,0,70,0,314⟩:=by
 apply AO 3 (occurs 3) ⟨3,11,6,23,0,70,0,314⟩ ⟨3,11,6,23,3,70,3,314⟩ (by decide+kernel)
 exact BJ 3 (occurs 3) ⟨3,11,6,23,3,70,3,314⟩ ⟨3,by decide⟩ 158 (by simpa only [lower] using metac3_400) (by simpa only [upper] using metac3_417)

theorem metac4_426:Covered 4 (occurs 4) ⟨4,11,8,23,0,70,0,314⟩:=by
 apply AO 4 (occurs 4) ⟨4,11,8,23,0,70,0,314⟩ ⟨4,11,8,23,4,70,4,314⟩ (by decide+kernel)
 exact covered_leaf 4 (occurs 4) ⟨4,11,8,23,4,70,4,314⟩ ⟨⟨214,by decide⟩,rfl,rfl⟩

theorem metac5_427:Covered 5 (occurs 5) ⟨5,11,10,23,0,70,0,314⟩:=by
 apply AO 5 (occurs 5) ⟨5,11,10,23,0,70,0,314⟩ ⟨5,11,10,23,5,70,5,314⟩ (by decide+kernel)
 exact covered_leaf 5 (occurs 5) ⟨5,11,10,23,5,70,5,314⟩ ⟨⟨215,by decide⟩,rfl,rfl⟩

theorem metac6_428:Covered 6 (occurs 6) ⟨6,11,12,23,0,70,0,314⟩:=by
 apply AO 6 (occurs 6) ⟨6,11,12,23,0,70,0,314⟩ ⟨6,11,12,23,6,70,6,314⟩ (by decide+kernel)
 exact covered_leaf 6 (occurs 6) ⟨6,11,12,23,6,70,6,314⟩ ⟨⟨216,by decide⟩,rfl,rfl⟩

theorem metac7_429:Covered 7 (occurs 7) ⟨7,11,14,23,0,70,0,314⟩:=by
 apply AO 7 (occurs 7) ⟨7,11,14,23,0,70,0,314⟩ ⟨7,11,14,23,7,70,7,314⟩ (by decide+kernel)
 exact covered_leaf 7 (occurs 7) ⟨7,11,14,23,7,70,7,314⟩ ⟨⟨217,by decide⟩,rfl,rfl⟩

theorem metac8_430:Covered 8 (occurs 8) ⟨8,11,16,23,0,70,0,314⟩:=by
 apply AO 8 (occurs 8) ⟨8,11,16,23,0,70,0,314⟩ ⟨8,11,16,23,8,70,8,314⟩ (by decide+kernel)
 exact covered_leaf 8 (occurs 8) ⟨8,11,16,23,8,70,8,314⟩ ⟨⟨218,by decide⟩,rfl,rfl⟩

theorem metac9_431:Covered 9 (occurs 9) ⟨9,11,18,23,0,70,0,314⟩:=by
 apply AO 9 (occurs 9) ⟨9,11,18,23,0,70,0,314⟩ ⟨9,11,18,23,9,70,9,314⟩ (by decide+kernel)
 exact covered_leaf 9 (occurs 9) ⟨9,11,18,23,9,70,9,314⟩ ⟨⟨219,by decide⟩,rfl,rfl⟩

theorem metac10_432:Covered 10 (occurs 10) ⟨10,11,20,23,0,70,0,314⟩:=by
 apply AO 10 (occurs 10) ⟨10,11,20,23,0,70,0,314⟩ ⟨10,11,20,23,10,70,10,314⟩ (by decide+kernel)
 exact covered_leaf 10 (occurs 10) ⟨10,11,20,23,10,70,10,314⟩ ⟨⟨220,by decide⟩,rfl,rfl⟩

theorem metac11_433:Covered 11 (occurs 11) ⟨11,11,22,23,0,70,0,314⟩:=by
 apply AO 11 (occurs 11) ⟨11,11,22,23,0,70,0,314⟩ ⟨11,11,22,23,11,70,11,314⟩ (by decide+kernel)
 exact covered_leaf 11 (occurs 11) ⟨11,11,22,23,11,70,11,314⟩ ⟨⟨221,by decide⟩,rfl,rfl⟩
theorem meta_covered (m:ℕ) (hm:0<m) (hh:m≤11):Covered m (occurs m) (root m):=by
 interval_cases m
 · exact metac1_1
 · exact metac2_320
 · exact metac3_399
 · exact metac4_426
 · exact metac5_427
 · exact metac6_428
 · exact metac7_429
 · exact metac8_430
 · exact metac9_431
 · exact metac10_432
 · exact metac11_433

theorem covered (fixedNew:Degrees) (low t y r cap:ℕ) (hg:AllGeometry fixedNew low t y r cap) (m:ℕ) (hm:0<m) (hh:m≤11):
 Covered m (Valid fixedNew m low t y r cap) (root m):=by
 intro p hp ha
 obtain ⟨a,⟨i,hiM,hiA⟩,hA⟩:=meta_covered m hm hh p hp ha
 refine ⟨a,?_,hA⟩
 rw [←hiA,←hiM]
 exact leaf_valid i fixedNew low t y r cap (hg i)

end JG

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower.GI
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF GZ
open HI FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def degrees (i:Fin 321):Degrees:=
 let p:=CN.profile i
 ⟨p.B,p.U,p.L,p.k,p.n0⟩

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem AGF {t y r:ℕ} (i:Fin 321) (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) t y r)
 (hFT:(CN.profile i).L<wt AT P.F):
 P.seeds.card<2000000000000000∨ ∃S:Source P.F,Fits S (degrees i):=by
 let p:=CN.profile i
 rcases VT p (CN.shape i) (CN.kernel i)
   (CN.positive i) (CN.dimension i)
   nodes P.u0 P.u1 hI P.F P.irreducible hFT r y t (by have:=P.rlow;omega)
   (by have:=P.rlow;have:=P.ylow;omega) (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega)
   ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · have small:=CN.small i
   exact Or.inl (KY.helper_count p nodes P small.1 small.2.1 small.2.2.1 small.2.2.2.1 Q hQ)
 · exact Or.inr ⟨S,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2⟩

end
namespace Concrete

open AP
def offer:Fin 39→Band:= ![⟨11,58,3599,3724,240017000000000000⟩,⟨12,58,3347,3774,257168000000000000⟩,⟨12,59,3294,3774,261564000000000000⟩,⟨13,55,3322,3699,254556000000000000⟩,⟨13,56,3266,3699,258792000000000000⟩,⟨13,57,3213,3456,248401000000000000⟩,⟨13,57,3457,3699,261937000000000000⟩,⟨13,58,3161,3378,247611000000000000⟩,⟨13,58,3379,3543,256650000000000000⟩,⟨13,58,3544,3560,257410000000000000⟩,⟨13,58,3561,3618,260938000000000000⟩,⟨13,58,3619,3680,264315000000000000⟩,⟨13,58,3681,3684,264601000000000000⟩,⟨13,59,3106,3146,237075000000000000⟩,⟨13,59,3147,3378,251514000000000000⟩,⟨13,59,3379,3543,260704000000000000⟩,⟨13,59,3544,3560,261492000000000000⟩,⟨13,59,3561,3599,263904000000000000⟩,⟨12,55,3394,3571,232614000000000000⟩,⟨12,55,3572,3749,242370000000000000⟩,⟨12,56,3338,3543,235936000000000000⟩,⟨12,56,3544,3749,246740000000000000⟩,⟨12,57,3283,3399,231627000000000000⟩,⟨12,57,3400,3516,237209000000000000⟩,⟨12,57,3517,3749,251109000000000000⟩,⟨13,53,3318,3533,236771000000000000⟩,⟨13,53,3534,3749,248527000000000000⟩,⟨13,54,3261,3383,232273000000000000⟩,⟨13,54,3384,3505,238262000000000000⟩,⟨13,54,3506,3627,244870000000000000⟩,⟨13,54,3628,3749,252250000000000000⟩,⟨12,51,3347,4000,240784000000000000⟩,⟨13,53,3681,4000,264947000000000000⟩,⟨13,60,3055,3120,246333000000000000⟩,⟨12,58,3681,3899,265620000000000000⟩,⟨12,59,3681,3850,266791000000000000⟩,⟨13,58,3681,3800,273000000000000000⟩,⟨12,59,3561,3680,255098000000000000⟩,⟨12,60,3055,3274,242771000000000000⟩]
def sourceIndex:Fin 39→Fin 321:= ![⟨314,by decide⟩,⟨316,by decide⟩,⟨316,by decide⟩,⟨316,by decide⟩,⟨316,by decide⟩,⟨316,by decide⟩,⟨317,by decide⟩,⟨316,by decide⟩,⟨317,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨318,by decide⟩,⟨318,by decide⟩,⟨316,by decide⟩,⟨316,by decide⟩,⟨317,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨317,by decide⟩,⟨314,by decide⟩,⟨316,by decide⟩,⟨314,by decide⟩,⟨316,by decide⟩,⟨317,by decide⟩,⟨314,by decide⟩,⟨316,by decide⟩,⟨314,by decide⟩,⟨316,by decide⟩,⟨317,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨316,by decide⟩,⟨314,by decide⟩,⟨310,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨310,by decide⟩]
theorem geometry0:JG.AllGeometry (degrees (sourceIndex ⟨0,by decide⟩)) (offer ⟨0,by decide⟩).T0 (offer ⟨0,by decide⟩).T1 (offer ⟨0,by decide⟩).B (offer ⟨0,by decide⟩).R (offer ⟨0,by decide⟩).count:=by decide+kernel
theorem geometry1:JG.AllGeometry (degrees (sourceIndex ⟨1,by decide⟩)) (offer ⟨1,by decide⟩).T0 (offer ⟨1,by decide⟩).T1 (offer ⟨1,by decide⟩).B (offer ⟨1,by decide⟩).R (offer ⟨1,by decide⟩).count:=by decide+kernel
theorem geometry2:JG.AllGeometry (degrees (sourceIndex ⟨2,by decide⟩)) (offer ⟨2,by decide⟩).T0 (offer ⟨2,by decide⟩).T1 (offer ⟨2,by decide⟩).B (offer ⟨2,by decide⟩).R (offer ⟨2,by decide⟩).count:=by decide+kernel
theorem geometry3:JG.AllGeometry (degrees (sourceIndex ⟨3,by decide⟩)) (offer ⟨3,by decide⟩).T0 (offer ⟨3,by decide⟩).T1 (offer ⟨3,by decide⟩).B (offer ⟨3,by decide⟩).R (offer ⟨3,by decide⟩).count:=by decide+kernel
theorem geometry4:JG.AllGeometry (degrees (sourceIndex ⟨4,by decide⟩)) (offer ⟨4,by decide⟩).T0 (offer ⟨4,by decide⟩).T1 (offer ⟨4,by decide⟩).B (offer ⟨4,by decide⟩).R (offer ⟨4,by decide⟩).count:=by decide+kernel
theorem geometry5:JG.AllGeometry (degrees (sourceIndex ⟨5,by decide⟩)) (offer ⟨5,by decide⟩).T0 (offer ⟨5,by decide⟩).T1 (offer ⟨5,by decide⟩).B (offer ⟨5,by decide⟩).R (offer ⟨5,by decide⟩).count:=by decide+kernel
theorem geometry6:JG.AllGeometry (degrees (sourceIndex ⟨6,by decide⟩)) (offer ⟨6,by decide⟩).T0 (offer ⟨6,by decide⟩).T1 (offer ⟨6,by decide⟩).B (offer ⟨6,by decide⟩).R (offer ⟨6,by decide⟩).count:=by decide+kernel
theorem geometry7:JG.AllGeometry (degrees (sourceIndex ⟨7,by decide⟩)) (offer ⟨7,by decide⟩).T0 (offer ⟨7,by decide⟩).T1 (offer ⟨7,by decide⟩).B (offer ⟨7,by decide⟩).R (offer ⟨7,by decide⟩).count:=by decide+kernel
theorem geometry8:JG.AllGeometry (degrees (sourceIndex ⟨8,by decide⟩)) (offer ⟨8,by decide⟩).T0 (offer ⟨8,by decide⟩).T1 (offer ⟨8,by decide⟩).B (offer ⟨8,by decide⟩).R (offer ⟨8,by decide⟩).count:=by decide+kernel
theorem geometry9:JG.AllGeometry (degrees (sourceIndex ⟨9,by decide⟩)) (offer ⟨9,by decide⟩).T0 (offer ⟨9,by decide⟩).T1 (offer ⟨9,by decide⟩).B (offer ⟨9,by decide⟩).R (offer ⟨9,by decide⟩).count:=by decide+kernel
theorem geometry10:JG.AllGeometry (degrees (sourceIndex ⟨10,by decide⟩)) (offer ⟨10,by decide⟩).T0 (offer ⟨10,by decide⟩).T1 (offer ⟨10,by decide⟩).B (offer ⟨10,by decide⟩).R (offer ⟨10,by decide⟩).count:=by decide+kernel
theorem geometry11:JG.AllGeometry (degrees (sourceIndex ⟨11,by decide⟩)) (offer ⟨11,by decide⟩).T0 (offer ⟨11,by decide⟩).T1 (offer ⟨11,by decide⟩).B (offer ⟨11,by decide⟩).R (offer ⟨11,by decide⟩).count:=by decide+kernel
theorem geometry12:JG.AllGeometry (degrees (sourceIndex ⟨12,by decide⟩)) (offer ⟨12,by decide⟩).T0 (offer ⟨12,by decide⟩).T1 (offer ⟨12,by decide⟩).B (offer ⟨12,by decide⟩).R (offer ⟨12,by decide⟩).count:=by decide+kernel
theorem geometry13:JG.AllGeometry (degrees (sourceIndex ⟨13,by decide⟩)) (offer ⟨13,by decide⟩).T0 (offer ⟨13,by decide⟩).T1 (offer ⟨13,by decide⟩).B (offer ⟨13,by decide⟩).R (offer ⟨13,by decide⟩).count:=by decide+kernel
theorem geometry14:JG.AllGeometry (degrees (sourceIndex ⟨14,by decide⟩)) (offer ⟨14,by decide⟩).T0 (offer ⟨14,by decide⟩).T1 (offer ⟨14,by decide⟩).B (offer ⟨14,by decide⟩).R (offer ⟨14,by decide⟩).count:=by decide+kernel
theorem geometry15:JG.AllGeometry (degrees (sourceIndex ⟨15,by decide⟩)) (offer ⟨15,by decide⟩).T0 (offer ⟨15,by decide⟩).T1 (offer ⟨15,by decide⟩).B (offer ⟨15,by decide⟩).R (offer ⟨15,by decide⟩).count:=by decide+kernel
theorem geometry16:JG.AllGeometry (degrees (sourceIndex ⟨16,by decide⟩)) (offer ⟨16,by decide⟩).T0 (offer ⟨16,by decide⟩).T1 (offer ⟨16,by decide⟩).B (offer ⟨16,by decide⟩).R (offer ⟨16,by decide⟩).count:=by decide+kernel
theorem geometry17:JG.AllGeometry (degrees (sourceIndex ⟨17,by decide⟩)) (offer ⟨17,by decide⟩).T0 (offer ⟨17,by decide⟩).T1 (offer ⟨17,by decide⟩).B (offer ⟨17,by decide⟩).R (offer ⟨17,by decide⟩).count:=by decide+kernel
theorem geometry18:JG.AllGeometry (degrees (sourceIndex ⟨18,by decide⟩)) (offer ⟨18,by decide⟩).T0 (offer ⟨18,by decide⟩).T1 (offer ⟨18,by decide⟩).B (offer ⟨18,by decide⟩).R (offer ⟨18,by decide⟩).count:=by decide+kernel
theorem geometry19:JG.AllGeometry (degrees (sourceIndex ⟨19,by decide⟩)) (offer ⟨19,by decide⟩).T0 (offer ⟨19,by decide⟩).T1 (offer ⟨19,by decide⟩).B (offer ⟨19,by decide⟩).R (offer ⟨19,by decide⟩).count:=by decide+kernel
theorem geometry20:JG.AllGeometry (degrees (sourceIndex ⟨20,by decide⟩)) (offer ⟨20,by decide⟩).T0 (offer ⟨20,by decide⟩).T1 (offer ⟨20,by decide⟩).B (offer ⟨20,by decide⟩).R (offer ⟨20,by decide⟩).count:=by decide+kernel
theorem geometry21:JG.AllGeometry (degrees (sourceIndex ⟨21,by decide⟩)) (offer ⟨21,by decide⟩).T0 (offer ⟨21,by decide⟩).T1 (offer ⟨21,by decide⟩).B (offer ⟨21,by decide⟩).R (offer ⟨21,by decide⟩).count:=by decide+kernel
theorem geometry22:JG.AllGeometry (degrees (sourceIndex ⟨22,by decide⟩)) (offer ⟨22,by decide⟩).T0 (offer ⟨22,by decide⟩).T1 (offer ⟨22,by decide⟩).B (offer ⟨22,by decide⟩).R (offer ⟨22,by decide⟩).count:=by decide+kernel
theorem geometry23:JG.AllGeometry (degrees (sourceIndex ⟨23,by decide⟩)) (offer ⟨23,by decide⟩).T0 (offer ⟨23,by decide⟩).T1 (offer ⟨23,by decide⟩).B (offer ⟨23,by decide⟩).R (offer ⟨23,by decide⟩).count:=by decide+kernel
theorem geometry24:JG.AllGeometry (degrees (sourceIndex ⟨24,by decide⟩)) (offer ⟨24,by decide⟩).T0 (offer ⟨24,by decide⟩).T1 (offer ⟨24,by decide⟩).B (offer ⟨24,by decide⟩).R (offer ⟨24,by decide⟩).count:=by decide+kernel
theorem geometry25:JG.AllGeometry (degrees (sourceIndex ⟨25,by decide⟩)) (offer ⟨25,by decide⟩).T0 (offer ⟨25,by decide⟩).T1 (offer ⟨25,by decide⟩).B (offer ⟨25,by decide⟩).R (offer ⟨25,by decide⟩).count:=by decide+kernel
theorem geometry26:JG.AllGeometry (degrees (sourceIndex ⟨26,by decide⟩)) (offer ⟨26,by decide⟩).T0 (offer ⟨26,by decide⟩).T1 (offer ⟨26,by decide⟩).B (offer ⟨26,by decide⟩).R (offer ⟨26,by decide⟩).count:=by decide+kernel
theorem geometry27:JG.AllGeometry (degrees (sourceIndex ⟨27,by decide⟩)) (offer ⟨27,by decide⟩).T0 (offer ⟨27,by decide⟩).T1 (offer ⟨27,by decide⟩).B (offer ⟨27,by decide⟩).R (offer ⟨27,by decide⟩).count:=by decide+kernel
theorem geometry28:JG.AllGeometry (degrees (sourceIndex ⟨28,by decide⟩)) (offer ⟨28,by decide⟩).T0 (offer ⟨28,by decide⟩).T1 (offer ⟨28,by decide⟩).B (offer ⟨28,by decide⟩).R (offer ⟨28,by decide⟩).count:=by decide+kernel
theorem geometry29:JG.AllGeometry (degrees (sourceIndex ⟨29,by decide⟩)) (offer ⟨29,by decide⟩).T0 (offer ⟨29,by decide⟩).T1 (offer ⟨29,by decide⟩).B (offer ⟨29,by decide⟩).R (offer ⟨29,by decide⟩).count:=by decide+kernel
theorem geometry30:JG.AllGeometry (degrees (sourceIndex ⟨30,by decide⟩)) (offer ⟨30,by decide⟩).T0 (offer ⟨30,by decide⟩).T1 (offer ⟨30,by decide⟩).B (offer ⟨30,by decide⟩).R (offer ⟨30,by decide⟩).count:=by decide+kernel
theorem geometry31:JG.AllGeometry (degrees (sourceIndex ⟨31,by decide⟩)) (offer ⟨31,by decide⟩).T0 (offer ⟨31,by decide⟩).T1 (offer ⟨31,by decide⟩).B (offer ⟨31,by decide⟩).R (offer ⟨31,by decide⟩).count:=by decide+kernel
theorem geometry32:JG.AllGeometry (degrees (sourceIndex ⟨32,by decide⟩)) (offer ⟨32,by decide⟩).T0 (offer ⟨32,by decide⟩).T1 (offer ⟨32,by decide⟩).B (offer ⟨32,by decide⟩).R (offer ⟨32,by decide⟩).count:=by decide+kernel
theorem geometry33:JG.AllGeometry (degrees (sourceIndex ⟨33,by decide⟩)) (offer ⟨33,by decide⟩).T0 (offer ⟨33,by decide⟩).T1 (offer ⟨33,by decide⟩).B (offer ⟨33,by decide⟩).R (offer ⟨33,by decide⟩).count:=by decide+kernel
theorem geometry34:JG.AllGeometry (degrees (sourceIndex ⟨34,by decide⟩)) (offer ⟨34,by decide⟩).T0 (offer ⟨34,by decide⟩).T1 (offer ⟨34,by decide⟩).B (offer ⟨34,by decide⟩).R (offer ⟨34,by decide⟩).count:=by decide+kernel
theorem geometry35:JG.AllGeometry (degrees (sourceIndex ⟨35,by decide⟩)) (offer ⟨35,by decide⟩).T0 (offer ⟨35,by decide⟩).T1 (offer ⟨35,by decide⟩).B (offer ⟨35,by decide⟩).R (offer ⟨35,by decide⟩).count:=by decide+kernel
theorem geometry36:JG.AllGeometry (degrees (sourceIndex ⟨36,by decide⟩)) (offer ⟨36,by decide⟩).T0 (offer ⟨36,by decide⟩).T1 (offer ⟨36,by decide⟩).B (offer ⟨36,by decide⟩).R (offer ⟨36,by decide⟩).count:=by decide+kernel
theorem geometry37:JG.AllGeometry (degrees (sourceIndex ⟨37,by decide⟩)) (offer ⟨37,by decide⟩).T0 (offer ⟨37,by decide⟩).T1 (offer ⟨37,by decide⟩).B (offer ⟨37,by decide⟩).R (offer ⟨37,by decide⟩).count:=by decide+kernel
theorem geometry38:JG.AllGeometry (degrees (sourceIndex ⟨38,by decide⟩)) (offer ⟨38,by decide⟩).T0 (offer ⟨38,by decide⟩).T1 (offer ⟨38,by decide⟩).B (offer ⟨38,by decide⟩).R (offer ⟨38,by decide⟩).count:=by decide+kernel
theorem geometry (i:Fin 39):JG.AllGeometry (degrees (sourceIndex i)) (offer i).T0 (offer i).T1 (offer i).B (offer i).R (offer i).count:=by
 fin_cases i
 · exact geometry0
 · exact geometry1
 · exact geometry2
 · exact geometry3
 · exact geometry4
 · exact geometry5
 · exact geometry6
 · exact geometry7
 · exact geometry8
 · exact geometry9
 · exact geometry10
 · exact geometry11
 · exact geometry12
 · exact geometry13
 · exact geometry14
 · exact geometry15
 · exact geometry16
 · exact geometry17
 · exact geometry18
 · exact geometry19
 · exact geometry20
 · exact geometry21
 · exact geometry22
 · exact geometry23
 · exact geometry24
 · exact geometry25
 · exact geometry26
 · exact geometry27
 · exact geometry28
 · exact geometry29
 · exact geometry30
 · exact geometry31
 · exact geometry32
 · exact geometry33
 · exact geometry34
 · exact geometry35
 · exact geometry36
 · exact geometry37
 · exact geometry38

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem packet_count (i:Fin 39) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) (offer i).T1 (offer i).B (offer i).R)
 (hFT:(offer i).T0≤wt AT P.F):P.seeds.card≤(offer i).count:=by
 have hL:(CN.profile (sourceIndex i)).L<(offer i).T0:=by fin_cases i<;>decide+kernel
 rcases AGF (sourceIndex i) nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
 · exact hs.le.trans (by fin_cases i<;>decide)
 exact ATV.AKJ (degrees (sourceIndex i))
   (by fin_cases i<;>decide) nodes hI P hFT SZ hZ (by fin_cases i<;>decide)
   (by fin_cases i<;>decide+kernel) (JG.covered _ _ _ _ _ _ (geometry i))

end Concrete
end ProximityPrize.SubmissionLower.GI
end
section
namespace ProximityPrize.SubmissionLower
namespace AJK
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF GZ
open HI FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

open GI AP
def offer:Fin 5→Band:= ![⟨13,60,3103,3378,255414000000000000⟩,⟨13,60,3379,3543,264756000000000000⟩,⟨13,60,3544,3560,265572000000000000⟩,⟨13,60,3561,3618,269219000000000000⟩,⟨13,60,3619,3680,273287000000000000⟩]
def sourceIndex:Fin 5→Fin 321:= ![⟨316,by decide⟩,⟨317,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩,⟨314,by decide⟩]
theorem geometry0:JG.AllGeometry (degrees (sourceIndex ⟨0,by decide⟩)) (offer ⟨0,by decide⟩).T0 (offer ⟨0,by decide⟩).T1 (offer ⟨0,by decide⟩).B (offer ⟨0,by decide⟩).R (offer ⟨0,by decide⟩).count:=by decide+kernel
theorem geometry1:JG.AllGeometry (degrees (sourceIndex ⟨1,by decide⟩)) (offer ⟨1,by decide⟩).T0 (offer ⟨1,by decide⟩).T1 (offer ⟨1,by decide⟩).B (offer ⟨1,by decide⟩).R (offer ⟨1,by decide⟩).count:=by decide+kernel
theorem geometry2:JG.AllGeometry (degrees (sourceIndex ⟨2,by decide⟩)) (offer ⟨2,by decide⟩).T0 (offer ⟨2,by decide⟩).T1 (offer ⟨2,by decide⟩).B (offer ⟨2,by decide⟩).R (offer ⟨2,by decide⟩).count:=by decide+kernel
theorem geometry3:JG.AllGeometry (degrees (sourceIndex ⟨3,by decide⟩)) (offer ⟨3,by decide⟩).T0 (offer ⟨3,by decide⟩).T1 (offer ⟨3,by decide⟩).B (offer ⟨3,by decide⟩).R (offer ⟨3,by decide⟩).count:=by decide+kernel
theorem geometry4:JG.AllGeometry (degrees (sourceIndex ⟨4,by decide⟩)) (offer ⟨4,by decide⟩).T0 (offer ⟨4,by decide⟩).T1 (offer ⟨4,by decide⟩).B (offer ⟨4,by decide⟩).R (offer ⟨4,by decide⟩).count:=by decide+kernel
theorem geometry (i:Fin 5):JG.AllGeometry (degrees (sourceIndex i)) (offer i).T0 (offer i).T1 (offer i).B (offer i).R (offer i).count:=by
 fin_cases i
 · exact geometry0
 · exact geometry1
 · exact geometry2
 · exact geometry3
 · exact geometry4
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem packet_count (i:Fin 5) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) (offer i).T1 (offer i).B (offer i).R)
 (hFT:(offer i).T0≤wt AT P.F):P.seeds.card≤(offer i).count:=by
 have hL:(CN.profile (sourceIndex i)).L<(offer i).T0:=by fin_cases i<;>decide+kernel
 rcases AGF (sourceIndex i) nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
 · exact hs.le.trans (by fin_cases i<;>decide)
 exact ATV.AKJ (degrees (sourceIndex i))
   (by fin_cases i<;>decide) nodes hI P hFT SZ hZ (by fin_cases i<;>decide)
   (by fin_cases i<;>decide+kernel) (JG.covered _ _ _ _ _ _ (geometry i))

end
end AJK

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace CP
open DR (Box Contains Empty lower upper)
open PA
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
inductive Tree where
 | empty:Tree
 | leaf:ℕ→Tree
 | node:Fin 4→ℕ→Tree→Tree→Tree

def decode:ℕ→ℕ→Tree × ℕ
 | 0,code=>(.empty,code)
 | n+1,code=>
  if code%4=0 then (.leaf (code/4%65536),code/262144)
  else if code%4=1 then
   let left:=decode n (code/1048576)
   let right:=decode n left.2
   (.node ⟨code/4%4,Nat.mod_lt _ (by decide)⟩ (code/16%65536) left.1 right.1,right.2)
  else (.empty,code/4)

def subset (a b:Box):Prop:=
 b.slo≤a.slo∧a.shi≤b.shi∧b.blo≤a.blo∧a.bhi≤b.bhi∧
 b.ulo≤a.ulo∧a.uhi≤b.uhi∧b.tlo≤a.tlo∧a.thi≤b.thi
instance (a b:Box):Decidable (subset a b):=by unfold subset;infer_instance

def check (boxes:ℕ→Box) (N m:ℕ):Tree→Box→Bool
 | .empty,a=>decide (Empty (normalize m 8 a))
 | .leaf i,a=>decide (i<N∧subset (normalize m 8 a) (boxes i))
 | .node axis pivot left right,a=>
   let b:=normalize m 8 a
   check boxes N m left (lower b axis pivot) && check boxes N m right (upper b axis pivot)

theorem sound (boxes:ℕ→Box) (N m:ℕ) (valid:Box→Prop)
 (hv: ∀i,i<N→valid (boxes i)) (tree:Tree) (a:Box)
 (h:check boxes N m tree a=true):Covered m valid a:=by
 induction tree generalizing a with
 | empty=>
  simp only [check,decide_eq_true_eq] at h
  intro p hp ha
  have hb:=ATG m 8 a p hp ha
  unfold DR.Empty Contains at*
  omega
 | leaf i=>
  simp only [check,decide_eq_true_eq] at h
  intro p hp ha
  have hb:=ATG m 8 a p hp ha
  refine ⟨boxes i,hv i h.1,?_⟩
  have hs:=h.2
  unfold subset Contains at*
  omega
 | node axis pivot left right ihl ihr=>
  simp only [check,Bool.and_eq_true] at h
  apply AO m valid a (normalize m 8 a) rfl
  exact BJ m valid _ axis pivot (ihl _ h.1) (ihr _ h.2)
def listBox (xs:List Box) (i:ℕ):Box:=(xs[i]?).getD ⟨0,0,0,0,0,0,0,0⟩
theorem listBox_valid (xs:List Box) (valid:Box→Prop)
 (h: ∀a∈xs,valid a) (i:ℕ) (hi:i<xs.length):valid (listBox xs i):=by
 have hh:=h xs[i] (List.getElem_mem hi)
 simpa only [listBox,List.getElem?_eq_getElem hi,Option.getD_some] using hh
end CP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace MJ
open FF ZGL
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def p0:Parameters:=⟨38,354,16,7,52,0,1⟩
theorem shape0:Shape p0:=by constructor<;>decide+kernel
theorem middle0 (h:ℕ) (hh:h≤7):52≤(p0.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem CPO:AM.AW p0.cutoff 131071 354 16 7 52=3564497745234:=by decide+kernel
theorem rank0:AR.rankBound 38 354 16 7 52=13597106:=by decide+kernel
theorem dimension0:Dimension p0 97989970:=by
 exact AZ p0 97989970 3564497745234 13597106 (by decide) (by decide) (by decide) (by decide) (by decide) middle0 CPO rank0 (by decide)

def p1:Parameters:=⟨38,531,16,7,52,0,1⟩
theorem shape1:Shape p1:=by constructor<;>decide+kernel
theorem middle1 (h:ℕ) (hh:h≤7):52≤(p1.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem COM:AM.AW p1.cutoff 131071 531 16 7 52=5459830538994:=by decide+kernel
theorem rank1:AR.rankBound 38 531 16 7 52=20748437:=by decide+kernel
theorem dimension1:Dimension p1 20752270066:=by
 exact AZ p1 20752270066 5459830538994 20748437 (by decide) (by decide) (by decide) (by decide) (by decide) middle1 COM rank1 (by decide)

def p2:Parameters:=⟨38,708,16,7,52,0,1⟩
theorem shape2:Shape p2:=by constructor<;>decide+kernel
theorem middle2 (h:ℕ) (hh:h≤7):52≤(p2.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem CNU:AM.AW p2.cutoff 131071 708 16 7 52=7355163332754:=by decide+kernel
theorem rank2:AR.rankBound 38 708 16 7 52=27899768:=by decide+kernel
theorem dimension2:Dimension p2 41406550162:=by
 exact AZ p2 41406550162 7355163332754 27899768 (by decide) (by decide) (by decide) (by decide) (by decide) middle2 CNU rank2 (by decide)

def p3:Parameters:=⟨38,1062,16,7,52,0,1⟩
theorem shape3:Shape p3:=by constructor<;>decide+kernel
theorem middle3 (h:ℕ) (hh:h≤7):52≤(p3.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem CNC:AM.AW p3.cutoff 131071 1062 16 7 52=11145828920274:=by decide+kernel
theorem rank3:AR.rankBound 38 1062 16 7 52=42202430:=by decide+kernel
theorem dimension3:Dimension p3 82715110354:=by
 exact AZ p3 82715110354 11145828920274 42202430 (by decide) (by decide) (by decide) (by decide) (by decide) middle3 CNC rank3 (by decide)

def p4:Parameters:=⟨38,1770,16,7,52,0,1⟩
theorem shape4:Shape p4:=by constructor<;>decide+kernel
theorem middle4 (h:ℕ) (hh:h≤7):52≤(p4.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem COY:AM.AW p4.cutoff 131071 1770 16 7 52=18727160095314:=by decide+kernel
theorem rank4:AR.rankBound 38 1770 16 7 52=70807754:=by decide+kernel
theorem dimension4:Dimension p4 165332230738:=by
 exact AZ p4 165332230738 18727160095314 70807754 (by decide) (by decide) (by decide) (by decide) (by decide) middle4 COY rank4 (by decide)

def p5:Parameters:=⟨36,375,15,7,49,0,1⟩
theorem shape5:Shape p5:=by constructor<;>decide+kernel
theorem middle5 (h:ℕ) (hh:h≤7):49≤(p5.cutoff h+15-1)/131071:=by interval_cases h<;>decide+kernel
theorem CPF:AM.AW p5.cutoff 131071 375 15 7 49=3086119086726:=by decide+kernel
theorem rank5:AR.rankBound 36 375 15 7 49=11772598:=by decide+kernel
theorem dimension5:Dimension p5 3156614:=by
 exact AZ p5 3156614 3086119086726 11772598 (by decide) (by decide) (by decide) (by decide) (by decide) middle5 CPF rank5 (by decide)

def p6:Parameters:=⟨34,419,14,6,46,0,1⟩
theorem shape6:Shape p6:=by constructor<;>decide+kernel
theorem middle6 (h:ℕ) (hh:h≤6):46≤(p6.cutoff h+14-1)/131071:=by interval_cases h<;>decide+kernel
theorem CMZ:AM.AW p6.cutoff 131071 419 14 6 46=2730093701510:=by decide+kernel
theorem rank6:AR.rankBound 34 419 14 6 46=10414269:=by decide+kernel
theorem dimension6:Dimension p6 55568774:=by
 exact AZ p6 55568774 2730093701510 10414269 (by decide) (by decide) (by decide) (by decide) (by decide) middle6 CMZ rank6 (by decide)

def p7:Parameters:=⟨30,586,12,6,41,0,1⟩
theorem shape7:Shape p7:=by constructor<;>decide+kernel
theorem middle7 (h:ℕ) (hh:h≤6):41≤(p7.cutoff h+12-1)/131071:=by interval_cases h<;>decide+kernel
theorem CMX:AM.AW p7.cutoff 131071 586 12 6 41=2383595175192:=by decide+kernel
theorem rank7:AR.rankBound 30 586 12 6 41=9092636:=by decide+kernel
theorem dimension7:Dimension p7 15203608:=by
 exact AZ p7 15203608 2383595175192 9092636 (by decide) (by decide) (by decide) (by decide) (by decide) middle7 CMX rank7 (by decide)

def p8:Parameters:=⟨40,339,17,8,55,0,1⟩
theorem shape8:Shape p8:=by constructor<;>decide+kernel
theorem middle8 (h:ℕ) (hh:h≤8):55≤(p8.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem COE:AM.AW p8.cutoff 131071 339 17 8 55=4207825676994:=by decide+kernel
theorem rank8:AR.rankBound 40 339 17 8 55=16050976:=by decide+kernel
theorem dimension8:Dimension p8 158624450:=by
 exact AZ p8 158624450 4207825676994 16050976 (by decide) (by decide) (by decide) (by decide) (by decide) middle8 COE rank8 (by decide)

def p9:Parameters:=⟨40,508,17,8,55,0,1⟩
theorem shape9:Shape p9:=by constructor<;>decide+kernel
theorem middle9 (h:ℕ) (hh:h≤8):55≤(p9.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem COS:AM.AW p9.cutoff 131071 508 17 8 55=6453629857809:=by decide+kernel
theorem rank9:AR.rankBound 40 508 17 8 55=24515172:=by decide+kernel
theorem dimension9:Dimension p9 27124609041:=by
 exact AZ p9 27124609041 6453629857809 24515172 (by decide) (by decide) (by decide) (by decide) (by decide) middle9 COS rank9 (by decide)

def p10:Parameters:=⟨40,678,17,8,55,0,1⟩
theorem shape10:Shape p10:=by constructor<;>decide+kernel
theorem middle10 (h:ℕ) (hh:h≤8):55≤(p10.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BVI:AM.AW p10.cutoff 131071 678 17 8 55=8712722820759:=by decide+kernel
theorem rank10:AR.rankBound 40 678 17 8 55=33029452:=by decide+kernel
theorem dimension10:Dimension p10 54250155671:=by
 exact AZ p10 54250155671 8712722820759 33029452 (by decide) (by decide) (by decide) (by decide) (by decide) middle10 BVI rank10 (by decide)

def p11:Parameters:=⟨40,1017,17,8,55,0,1⟩
theorem shape11:Shape p11:=by constructor<;>decide+kernel
theorem middle11 (h:ℕ) (hh:h≤8):55≤(p11.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BTL:AM.AW p11.cutoff 131071 1017 17 8 55=13217619964524:=by decide+kernel
theorem rank11:AR.rankBound 40 1017 17 8 55=50007928:=by decide+kernel
theorem dimension11:Dimension p11 108341686892:=by
 exact AZ p11 108341686892 13217619964524 50007928 (by decide) (by decide) (by decide) (by decide) (by decide) middle11 BTL rank11 (by decide)

def p12:Parameters:=⟨40,1695,17,8,55,0,1⟩
theorem shape12:Shape p12:=by constructor<;>decide+kernel
theorem middle12 (h:ℕ) (hh:h≤8):55≤(p12.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BSP:AM.AW p12.cutoff 131071 1695 17 8 55=22227414252054:=by decide+kernel
theorem rank12:AR.rankBound 40 1695 17 8 55=83964880:=by decide+kernel
theorem dimension12:Dimension p12 216524749334:=by
 exact AZ p12 216524749334 22227414252054 83964880 (by decide) (by decide) (by decide) (by decide) (by decide) middle12 BSP rank12 (by decide)

def p13:Parameters:=⟨40,2712,17,8,55,0,1⟩
theorem shape13:Shape p13:=by constructor<;>decide+kernel
theorem middle13 (h:ℕ) (hh:h≤8):55≤(p13.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BYL:AM.AW p13.cutoff 131071 2712 17 8 55=35742105683349:=by decide+kernel
theorem rank13:AR.rankBound 40 2712 17 8 55=134900308:=by decide+kernel
theorem dimension13:Dimension p13 378799342997:=by
 exact AZ p13 378799342997 35742105683349 134900308 (by decide) (by decide) (by decide) (by decide) (by decide) middle13 BYL rank13 (by decide)

def p14:Parameters:=⟨45,319,20,9,62,0,1⟩
theorem shape14:Shape p14:=by constructor<;>decide+kernel
theorem middle14 (h:ℕ) (hh:h≤9):62≤(p14.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem BUT:AM.AW p14.cutoff 131071 319 20 9 62=6460774887929:=by decide+kernel
theorem rank14:AR.rankBound 45 319 20 9 62=24645458:=by decide+kernel
theorem dimension14:Dimension p14 115945977:=by
 exact AZ p14 115945977 6460774887929 24645458 (by decide) (by decide) (by decide) (by decide) (by decide) middle14 BUT rank14 (by decide)

def p15:Parameters:=⟨45,478,20,9,62,0,1⟩
theorem shape15:Shape p15:=by constructor<;>decide+kernel
theorem middle15 (h:ℕ) (hh:h≤9):62≤(p15.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem BZD:AM.AW p15.cutoff 131071 478 20 9 62=9961655618924:=by decide+kernel
theorem rank15:AR.rankBound 45 478 20 9 62=37810817:=by decide+kernel
theorem dimension15:Dimension p15 49776807276:=by
 exact AZ p15 49776807276 9961655618924 37810817 (by decide) (by decide) (by decide) (by decide) (by decide) middle15 BZD rank15 (by decide)

def p16:Parameters:=⟨45,638,20,9,62,0,1⟩
theorem shape16:Shape p16:=by constructor<;>decide+kernel
theorem middle16 (h:ℕ) (hh:h≤9):62≤(p16.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem DKR:AM.AW p16.cutoff 131071 638 20 9 62=13484554467724:=by decide+kernel
theorem rank16:AR.rankBound 45 638 20 9 62=51058977:=by decide+kernel
theorem dimension16:Dimension p16 99750001036:=by
 exact AZ p16 99750001036 13484554467724 51058977 (by decide) (by decide) (by decide) (by decide) (by decide) middle16 DKR rank16 (by decide)

def p17:Parameters:=⟨45,957,20,9,62,0,1⟩
theorem shape17:Shape p17:=by constructor<;>decide+kernel
theorem middle17 (h:ℕ) (hh:h≤9):62≤(p17.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem DIR:AM.AW p17.cutoff 131071 957 20 9 62=20508334047519:=by decide+kernel
theorem rank17:AR.rankBound 45 957 20 9 62=77472496:=by decide+kernel
theorem dimension17:Dimension p17 199384056095:=by
 exact AZ p17 199384056095 20508334047519 77472496 (by decide) (by decide) (by decide) (by decide) (by decide) middle17 DIR rank17 (by decide)

def p18:Parameters:=⟨45,1595,20,9,62,0,1⟩
theorem shape18:Shape p18:=by constructor<;>decide+kernel
theorem middle18 (h:ℕ) (hh:h≤9):62≤(p18.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem DIW:AM.AW p18.cutoff 131071 1595 20 9 62=34555893207109:=by decide+kernel
theorem rank18:AR.rankBound 45 1595 20 9 62=130299534:=by decide+kernel
theorem dimension18:Dimension p18 398652166213:=by
 exact AZ p18 398652166213 34555893207109 130299534 (by decide) (by decide) (by decide) (by decide) (by decide) middle18 DIW rank18 (by decide)

def p19:Parameters:=⟨51,400,23,11,70,0,1⟩
theorem shape19:Shape p19:=by constructor<;>decide+kernel
theorem middle19 (h:ℕ) (hh:h≤11):70≤(p19.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem DJR:AM.AW p19.cutoff 131071 400 23 11 70=13525111441855:=by decide+kernel
theorem rank19:AR.rankBound 51 400 23 11 70=51397405:=by decide+kernel
theorem dimension19:Dimension p19 51590105535:=by
 exact AZ p19 51590105535 13525111441855 51397405 (by decide) (by decide) (by decide) (by decide) (by decide) middle19 DJR rank19 (by decide)

def p20:Parameters:=⟨51,471,23,11,70,0,1⟩
theorem shape20:Shape p20:=by constructor<;>decide+kernel
theorem middle20 (h:ℕ) (hh:h≤11):70≤(p20.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem DLE:AM.AW p20.cutoff 131071 471 23 11 70=16115332865619:=by decide+kernel
theorem rank20:AR.rankBound 51 471 23 11 70=61115885:=by decide+kernel
theorem dimension20:Dimension p20 94170308179:=by
 exact AZ p20 94170308179 16115332865619 61115885 (by decide) (by decide) (by decide) (by decide) (by decide) middle20 DLE rank20 (by decide)
def profile:Fin 21→Parameters:= ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20]
def kernel:Fin 21→ℕ:= ![97989970,20752270066,41406550162,82715110354,165332230738,3156614,55568774,15203608,158624450,27124609041,54250155671,108341686892,216524749334,378799342997,115945977,49776807276,99750001036,199384056095,398652166213,51590105535,94170308179]
theorem shape (i:Fin 21):Shape (profile i):=by
 fin_cases i
 · exact shape0
 · exact shape1
 · exact shape2
 · exact shape3
 · exact shape4
 · exact shape5
 · exact shape6
 · exact shape7
 · exact shape8
 · exact shape9
 · exact shape10
 · exact shape11
 · exact shape12
 · exact shape13
 · exact shape14
 · exact shape15
 · exact shape16
 · exact shape17
 · exact shape18
 · exact shape19
 · exact shape20
theorem dimension (i:Fin 21):Dimension (profile i) (kernel i):=by
 fin_cases i
 · exact dimension0
 · exact dimension1
 · exact dimension2
 · exact dimension3
 · exact dimension4
 · exact dimension5
 · exact dimension6
 · exact dimension7
 · exact dimension8
 · exact dimension9
 · exact dimension10
 · exact dimension11
 · exact dimension12
 · exact dimension13
 · exact dimension14
 · exact dimension15
 · exact dimension16
 · exact dimension17
 · exact dimension18
 · exact dimension19
 · exact dimension20
theorem small (i:Fin 21):(profile i).B≤256∧(profile i).U≤512∧(profile i).L≤4096∧(profile i).s≤64:=by fin_cases i<;>decide
end MJ

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace UU
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF
open HI LV BH DR
open FF ZGL MJ
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
instance (p:DA.SourceCaps) (a:DA.OwnerBox):
 Decidable (DA.Impossible p a):=by unfold DA.Impossible;infer_instance

def pricing (fixed:Degrees) (a:DR.Box) (m:ℕ) (useOwner:Bool):=if useOwner then ownerZ a m else fixed

def BandValid (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 21) (useOwner:Bool) (N:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 0<m∧m≤a.slo∧2*a.slo≤a.bhi∧
 a.shi≤64∧a.bhi≤256∧a.uhi≤512∧a.thi≤4096∧a.thi<low∧p.L<low∧
 SN.Common z low t y r∧MG t y r≤cap∧
 DA.Impossible (caps p) {powerBox p a m with q:=N}∧
 (∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<kernel i∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 pairCost z 1 (ownerFlag a) (flag p.B p.U p.L p.s) t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 21) (useOwner:Bool) (N:ℕ):Decidable (BandValid fixed a m low t y r cap i useOwner N):=by
 unfold BandValid SN.Common Gates;infer_instance



variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem CPT {t y r low cap m:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (SZ:Source P.F) (fixed:Degrees) (hFixed:Fits SZ fixed)
 (hFT:low≤wt AT P.F) (hcap:4000000000000000≤cap)
 (J:DX.Poly (K:=K)) (hJ:Irreducible J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (i:Fin 21) (useOwner:Bool) (N:ℕ) (hc:BandValid fixed a m low t y r cap i useOwner N):
 P.seeds.card≤cap:=by
 classical
 obtain ⟨hm,hms,h2,hs,hb,hu,ht,haf,hpf,hcommon,hid,hstop,hband,hz,huy,hgeo⟩:=hc
 have hsmall:AMK.Small J:=by
   refine ⟨ha.2.1.trans hs,?_⟩
   intro d hd
   have hB:=(le_weightedTotalDegree slopeWeights hd).trans (ha.2.2.2.1.trans hb)
   have hU:=(le_weightedTotalDegree HA hd).trans (ha.2.2.2.2.2.1.trans hu)
   have hT:=(le_weightedTotalDegree totalWeights hd).trans (ha.2.2.2.2.2.2.2.trans ht)
   simp only [JW,slopeWeights,HA,totalWeights] at hB hU hT
   norm_num at hB hU hT
   exact ⟨by omega,by omega,by omega⟩
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hpower:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS J).map (carrierMap P.F):=
   (Polynomial.le_rootMultiplicity_iff hJne).mp (by rw [hroot];omega)
 obtain ⟨SJ,hSJ,hSJd⟩:=ZD.UN P.F a.thi
   (haf.trans_le hFT) P.rdegree hchar J hJ.ne_zero ha.2.2.2.2.2.2.2 1 (by decide) hpower
 have hpricing: ∃S:Source P.F,Fits S (pricing fixed a m useOwner):=by
   cases useOwner with
   | false=>exact ⟨SZ,hFixed⟩
   | true=>exact owner_source P J a m hm ha hms h2 hroot
 obtain ⟨S,hS⟩:=hpricing
 have hpSmall:=MJ.small i
 exact XU.packet_count nodes hN P (profile i) (shape i) (kernel i) (dimension i)
   hpSmall (hpf.trans_le hFT) J hJ a ha m (hms.trans ha.1) hsmall hJne hroot SJ S hSJ hSJd
   (pricing fixed a m useOwner) hS (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
   cap hcap hid ⟨hz,huy,hgeo⟩ N hstop hband


def linearU (a:DR.Box):=max a.bhi a.uhi
def linearT (a:DR.Box):=max (linearU a) a.thi
def LinearValid (a:DR.Box) (low t y r cap:ℕ):Prop:=
 a.shi≤1∧2≤a.bhi∧linearT a<low∧
 AYU.LinearChecks a.bhi (linearU a) (linearT a) t y r cap
instance (a:DR.Box) (low t y r cap:ℕ):Decidable (LinearValid a low t y r cap):=by unfold LinearValid;infer_instance

theorem CUP {t y r low cap:ℕ} {x:I→K}
 (P:Packet x t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt AT P.F) (hid:MG t y r≤cap)
 (J:DX.Poly (K:=K)) (hJ:J≠0) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
 (hc:LinearValid a low t y r cap):P.seeds.card≤cap:=by
 obtain ⟨hs,hB,hL,hchecks⟩:=hc
 have hS:J.degreeOf 1=1:=by have hh:=ha.2.1;change order J≤a.shi at hh;change order J=1;omega
 have hshape: ∀e∈J.support,2*e 1+e 3≤a.bhi∧e 1+e 2+e 3≤linearU a∧e 1+e 2+e 3+e 4≤linearT a:=by
   intro e he
   have hb:=(le_weightedTotalDegree slopeWeights he).trans ha.2.2.2.1
   have hu:Finsupp.weight HA e≤linearU a:=(le_weightedTotalDegree HA he).trans (ha.2.2.2.2.2.1.trans (le_max_right a.bhi a.uhi))
   have ht:Finsupp.weight totalWeights e≤linearT a:=(le_weightedTotalDegree totalWeights he).trans (ha.2.2.2.2.2.2.2.trans (le_max_right (linearU a) a.thi))
   simp only [JW,slopeWeights,HA,totalWeights] at hb hu ht
   norm_num at hb hu ht
   exact ⟨by omega,by omega,by omega⟩
 have hh:=AOR.BNL P J hJ hS a.bhi (linearU a) (linearT a)
   hB (le_max_left _ _) (le_max_left _ _) hshape (hL.trans_le hFT) hroot hchecks.1 hchecks.2.1
 exact hh.trans (max_le hid hchecks.2.2)

end
end UU

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace CMG
open FF ZGL
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def p0:Parameters:=⟨38,354,16,7,52,0,1⟩






def p1:Parameters:=⟨38,531,16,7,52,0,1⟩






def p2:Parameters:=⟨38,708,16,7,52,0,1⟩






def p3:Parameters:=⟨38,1062,16,7,52,0,1⟩






def p4:Parameters:=⟨38,1770,16,7,52,0,1⟩






def p5:Parameters:=⟨34,419,14,6,46,0,1⟩






def p6:Parameters:=⟨30,586,12,6,41,0,1⟩






def p7:Parameters:=⟨40,339,17,8,55,0,1⟩






def p8:Parameters:=⟨40,1017,17,8,55,0,1⟩






def p9:Parameters:=⟨40,1695,17,8,55,0,1⟩






def p10:Parameters:=⟨40,2712,17,8,55,0,1⟩






def p11:Parameters:=⟨45,319,20,9,62,0,1⟩






def p12:Parameters:=⟨45,638,20,9,62,0,1⟩






def p13:Parameters:=⟨45,957,20,9,62,0,1⟩






def p14:Parameters:=⟨51,400,23,11,70,0,1⟩






def p15:Parameters:=⟨51,471,23,11,70,0,1⟩





def profile:Fin 16→Parameters:= ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15]
def kernel:Fin 16→ℕ:= ![97989970,20752270066,41406550162,82715110354,165332230738,55568774,15203608,158624450,108341686892,216524749334,378799342997,115945977,99750001036,199384056095,51590105535,94170308179]



end CMG

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace DOX
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF
open HI LV BH DR
open FF ZGL CMG
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
instance (p:DA.SourceCaps) (a:DA.OwnerBox):
 Decidable (DA.Impossible p a):=by unfold DA.Impossible;infer_instance

def pricing (fixed:Degrees) (a:DR.Box) (m:ℕ) (useOwner:Bool):=if useOwner then ownerZ a m else fixed

def BandValid (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 16) (useOwner:Bool) (N:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 0<m∧m≤a.slo∧2*a.slo≤a.bhi∧
 a.shi≤64∧a.bhi≤256∧a.uhi≤512∧a.thi≤4096∧a.thi<low∧p.L<low∧
 SN.Common z low t y r∧MG t y r≤cap∧
 DA.Impossible (caps p) {powerBox p a m with q:=N}∧
 (∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<kernel i∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 pairCost z 1 (ownerFlag a) (flag p.B p.U p.L p.s) t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 16) (useOwner:Bool) (N:ℕ):Decidable (BandValid fixed a m low t y r cap i useOwner N):=by
 unfold BandValid SN.Common Gates;infer_instance



variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]



def linearU (a:DR.Box):=max a.bhi a.uhi
def linearT (a:DR.Box):=max (linearU a) a.thi
def LinearValid (a:DR.Box) (low t y r cap:ℕ):Prop:=
 a.shi≤1∧2≤a.bhi∧linearT a<low∧
 AYU.LinearChecks a.bhi (linearU a) (linearT a) t y r cap
instance (a:DR.Box) (low t y r cap:ℕ):Decidable (LinearValid a low t y r cap):=by unfold LinearValid;infer_instance



end
end DOX

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ADB
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF GZ
open HI FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def degrees (i:Fin 321):Degrees:=
 let p:=CN.profile i
 ⟨p.B,p.U,p.L,p.k,p.n0⟩

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem AGF {t y r:ℕ} (i:Fin 321) (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) t y r)
 (hFT:(CN.profile i).L<wt AT P.F):
 P.seeds.card<2000000000000000∨ ∃S:Source P.F,Fits S (degrees i):=by
 let p:=CN.profile i
 rcases VT p (CN.shape i) (CN.kernel i)
   (CN.positive i) (CN.dimension i)
   nodes P.u0 P.u1 hI P.F P.irreducible hFT r y t (by have:=P.rlow;omega)
   (by have:=P.rlow;have:=P.ylow;omega) (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega)
   ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · have small:=CN.small i
   exact Or.inl (KY.helper_count p nodes P small.1 small.2.1 small.2.2.1 small.2.2.2.1 Q hQ)
 · exact Or.inr ⟨S,hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2⟩

end
end ADB

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AVB
open FF ZGL HI
open CW DJ CB
open RCN095 RCN234 RCN156
open BD EF DU
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
def frame:Parameters:=⟨130,3894,52,23,177,6,8⟩
theorem shape:Shape frame:=by constructor<;>decide+kernel
theorem middle (h:ℕ) (hh:h≤23):177≤(frame.cutoff h+52-1)/131071:=by interval_cases h<;>decide+kernel
theorem coefficients:AM.AW frame.cutoff 131071 3894 52 23 177=4213262035509362:=by decide+kernel
theorem rank:AR.rankBound 130 3894 52 23 177=16072318038:=by decide+kernel
theorem dimension:Dimension frame 295755890:=by
 exact AZ frame 295755890 4213262035509362 16072318038 (by decide) (by decide) (by decide) (by decide) (by decide) middle coefficients rank (by decide)
def profile (i:Fin 322):Parameters:=if h:i.val<321 then CN.profile ⟨i.val,h⟩ else frame
def degrees (i:Fin 322):Degrees:=let p:=profile i;⟨p.B,p.U,p.L,p.k,p.n0⟩
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem AGF {t y r:ℕ} (i:Fin 322) (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) t y r) (hFT:(profile i).L<wt AT P.F):
 P.seeds.card<2000000000000000∨ ∃S:Source P.F,Fits S (degrees i):=by
 by_cases hi:i.val<321
 · have hh:(CN.profile ⟨i.val,hi⟩).L<wt AT P.F:=by simpa only [profile,dif_pos hi] using hFT
   simpa only [degrees,profile,dif_pos hi,ADB.degrees] using ADB.AGF ⟨i.val,hi⟩ nodes hI P hh
 · have hframe:profile i=frame:=dif_neg hi
   have hf:frame.L<wt AT P.F:=by simpa only [hframe] using hFT
   rcases VT frame shape 295755890 (by decide) dimension
     nodes P.u0 P.u1 hI P.F P.irreducible hf r y t (by have:=P.rlow;omega)
     (by have:=P.rlow;have:=P.ylow;omega) (by have:=P.rlow;have:=P.ylow;have:=P.yt;omega)
     ⟨P.r_weight,P.y_weight,P.total_weight⟩ with ⟨Q,hQ⟩ | ⟨S,hS⟩
   · exact Or.inl (KY.helper_count frame nodes P (by decide) (by decide) (by decide) (by decide) Q hQ)
   · refine Or.inr ⟨S,?_⟩
     simpa only [degrees,hframe] using (show Fits S ⟨frame.B,frame.U,frame.L,frame.k,frame.n0⟩ from ⟨hS.1,hS.2.1,hS.2.2.1,hS.2.2.2.2.1,hS.2.2.2.2.2⟩)

end AVB

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ACU
open MvPolynomial CW DJ
open BX DP DC
open BD DU EF
open CB HI DR LV
open UU AVB
open RCN095 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def fallback:Fin 322:=⟨310,by decide⟩
def Valid (m low t y r cap:ℕ) (a:DR.Box):Prop:=
 BH.check .native (degrees fallback) a m low t y r cap=true∨
 LinearValid a low t y r cap∨
 ∃(i:Fin 21) (useOwner:Bool) (j:Fin 322) (N:ℕ),
   (AVB.profile j).L<low∧
   BandValid (degrees j) a m low t y r cap i useOwner N

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem BLH {m low t y r cap:ℕ}
 (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt AT P.F) (hLow:2985<low)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (J:DX.Poly (K:=K)) (hJ:Irreducible J) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (hJroot:((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
 (hc:Valid m low t y r cap a):P.seeds.card≤cap:=by
 rcases hc with hc | hc | ⟨i,useOwner,j,N,hL,hc⟩
 · have hL:(AVB.profile fallback).L<low:=by
     have hh:(AVB.profile fallback).L=2436:=by decide+kernel
     omega
   rcases AGF fallback nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact (BH.BLQ nodes hI P SZ (degrees fallback) hZ .native a m low cap
     hFT (by omega) (by omega) J hJ ha hroot hJne hc).trans (max_le hid le_rfl)
 · exact CUP P hFT hid J hJ.ne_zero horder a ha hJroot hc
 · rcases AGF j nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact CPT nodes hI P SZ (degrees j) hZ hFT hcap J hJ a ha hroot hJne i useOwner N hc
end
end ACU

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AGH
open DR (Box Contains lower upper)
open HI PA UU AVB
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
abbrev valid (m:ℕ):=ACU.Valid m 3895 3924 60 13 274040000000000000

open CP

def receiptBox (code:ℕ):Box:=
 let x:=code/8589934592
 ⟨x%4096,x/4096%4096,x/4096^2%4096,x/4096^3%4096,
  x/4096^4%4096,x/4096^5%4096,x/4096^6%4096,x/4096^7%4096⟩
def receiptTest (m code:ℕ):Bool:=
 let a:=receiptBox code
 if code%4=0 then BH.check .native (degrees ACU.fallback) a m 3895 3924 60 13 274040000000000000
 else if code%4=1 then decide (LinearValid a 3895 3924 60 13 274040000000000000)
 else if h:code/4%32<21∧code/256%512<322 then
  decide ((AVB.profile ⟨code/256%512,h.2⟩).L<3895∧
   BandValid (degrees ⟨code/256%512,h.2⟩) a m 3895 3924 60 13 274040000000000000
     ⟨code/4%32,h.1⟩ (code/128%2=1) (code/131072%65536))
 else false

theorem receipt_sound (m code:ℕ) (h:receiptTest m code=true):valid m (receiptBox code):=by
 unfold receiptTest at h
 split_ifs at h with h0 h1 h2
 · exact Or.inl h
 · exact Or.inr (Or.inl (of_decide_eq_true h))
 · have hh:=of_decide_eq_true h
   exact Or.inr (Or.inr ⟨⟨code/4%32,h2.1⟩,decide (code/128%2=1),⟨code/256%512,h2.2⟩,code/131072%65536,hh.1,hh.2⟩)

def decodeReceipts:ℕ→ℕ→List ℕ
 | 0,_=>[]
 | n+1,c=>c%2^132::decodeReceipts n (c/2^132)
def d1_0:List ℕ:=decodeReceipts 16 0x1800e01800e01200c00800600000000001800e01800e01200c004004000736b6001800e01800e01200c00200200000001001800e01800e00a00400400200000000001800e00c00801801000c00800000000001800e00c00801200c00600600000000001800e00c00801000c00400400000000001800e00c00a00e00c00200200000000001800e00c00800a00400400200000000001800e00600200c00400600200000000000c00800c00801801000c00800000000000c00800c00801200c00600600000000000c00800c00801000c00400400000000000c00a00c00a00e00c00200200000000000c00800c00800a00400400200000000000c00200600200c00400600200000000
theorem hd1_0:d1_0.all (receiptTest 1)=true:=by decide+kernel
def d1_1:List ℕ:=decodeReceipts 16 0x2e01a02e01a01200c00200200000001002e01a02e01a00a00800400400000000002e01a02e01a00a00800200200000001002e01a02e01a00600400200200000000002e01a01800e02001400e00200053606002e01a01800e01200c00800600000000002e01a01800e01200c004004000736b6002e01a01800e01200c00200200000001002e01a01800e00a00400400200000000002e01a00c00801801000c00800000000002e01a00c00801200c00600600000000002e01a00c00801000c00400400000000002e01a00c00a00e00c00200200000000002e01a00c00800a00400400200000000002e01a00600200c00400600200000000001800e01800e02001400e00200053606
theorem hd1_1:d1_1.all (receiptTest 1)=true:=by decide+kernel
def d1_2:List ℕ:=decodeReceipts 16 0x5a03002e01a00a00800200200000001005a03002e01a00600400200200000000005a03001800e02001400e00200053606005a03001800e01200c00800600000000005a03001800e01200c004004000736b6005a03001800e01200c00200200000001005a03001800e00a00400400200000000005a03000c00801801000c00800000000005a03000c00801200c00600600000000005a03000c00801000c00400400000000005a03000c00a00e00c00200200000000005a03000c00800a00400400200000000005a03000600200c00400600200000000002e01a02e01a02001400e00200053606002e01a02e01a01200c00800600073692002e01a02e01a01200c004004000936ca
theorem hd1_2:d1_2.all (receiptTest 1)=true:=by decide+kernel
def d1_3:List ℕ:=decodeReceipts 16 0xb205c03401c00a0080020020000000100b205c03401c0060040020020000000100b205c01a01002001400e00200053a0600b205c01a01001200c008002000736b200b205c01a01000a0040040020000000000b205c00e00a01c01400e00a0000000000b205c00e00a01600e00800200073a0e00b205c00e00a00c0040060020000000000b205c00800601000c0080060000000000b205c00800200c00400400200000000005a03005a03002001400e00200053a06005a03005a03001200c00800200073a0a005a03005a03000a00400400200073a0e005a03002e01a02001400e00200053a06005a03002e01a01200c00800200073a2e005a03002e01a00a00800400400000000
theorem hd1_3:d1_3.all (receiptTest 1)=true:=by decide+kernel
def d1_4:List ℕ:=decodeReceipts 16 0x1620b401a01001200c004004000736b201620b401a01001200c0020020000000101620b401a01000a0040040020000000001620b400e00a01c01400e00a0000000001620b400e00a01600e00800200073a0e01620b400e00a00c0040060020000000001620b400800601000c0080060000000001620b400800200c0040040020000000000b205c06803602001400e00200053a0600b205c06803601200400800200053a0a00b205c03401c02001400e00200053a0600b205c03401c01200c00800200073a0e00b208803402a00a00800400400073a0e00b208802801c00a00800400400000000008605c03402a00a00800400400073a0e008605c02801c00a00800400400000000
theorem hd1_4:d1_4.all (receiptTest 1)=true:=by decide+kernel
def d1_5:List ℕ:=decodeReceipts 16 0x2c416400800601000c0080060000000002c416400800200c0040040020000000001620b406803602001400e0020005410601620b40680360120040080020007412a01620b403401c02001400e00200053a0601620b403401c01200c0080060007368e01620b403401c01200c004004000736ae01620b403401c01200c00200200000001016210c03402a00a00800400400073a0e016210c02801c00a00800400400000000010a0b403402a00a00800400400073a0e010a0b402801c00a0080040040000000001620b403401c00a0080020020000000101620b403401c0060040020020000000101620b401a01002001400e00200053a0601620b401a01001200c00800600000000
theorem hd1_5:d1_5.all (receiptTest 1)=true:=by decide+kernel
def d1_6:List ℕ:=decodeReceipts 16 0x2c416403401c01200c0080020007413e02c416403401c00a00800400200073f5202c416403401c0060040020020000000102c416401a01002001400e00a0005368602c421601a01602001c00800600033a1e02c421601a01601a01400800600053a0602c421601401001c01400800600053a06021416401a01002001400800600053a0602c416401a01001e01400400200053f0602c416401a01001200c008002000736ae02c416401a01000a0080040040000000002c416401a01000a0080020020000000102c416401a0100060040020020000000002c416400e00a01c01400e00a00053a0602c416400e00a01600e00800200073e0a02c416400e00a00c00400600200000000
theorem hd1_6:d1_6.all (receiptTest 1)=true:=by decide+kernel
def d1_7:List ℕ:=decodeReceipts 16 0x26c21603402a02001c0080080003411e02c426e03402a02001c00600600053a22026c21603402a02001c00600600033f1e02c421603402a01a0140080080005368602c426e03402a01a01400600600053a3a026c21603402a01a01400600600053a0602c421602801c02001c0080060003411e02c421602801c01a01400800600054106021416403401c02001400800600053e0602c426e03402a02001c00400400053a22026c21603402a02001c00400400033e1e02c421603402a01a0140040040005410602c421602801c02001c0040040003411e02c421602801c01a01400400400053e06021416403401c02001400400400053a0602c416403401c02001400200200000001
theorem hd1_7:d1_7.all (receiptTest 1)=true:=by decide+kernel
def d1_8:List ℕ:=decodeReceipts 16 0x21416406803601200c00800600053a0602c426e06805001201000400400053a3a026c2160680500120100040040005410602c426e06805000e00c00400400053a3a026c21606805000e00c00400400053a0602c421604e03601200c00400400054106021416406803601200c00400400053a0602c416406803601200c0020020000000102c416406803600a00400400200053e0602c421603402a02001c00e00e0005368602c426e03402a02001c00c00a00053a22026c21603402a02001c00c00a0003411e02c421603402a01a01400c00a0005368602c421602801c02001400e00a00053686021416403401c02001400e00a0005410602c426e03402a02001c00800800053a22
theorem hd1_8:d1_8.all (receiptTest 1)=true:=by decide+kernel
def d1_9:List ℕ:=decodeReceipts 16 0x2141be06805e02001c00200200033a1a02141ea05c05802001c00200200053a1a02141ea05605002002000200200053a0202141ea05605001e01c0020020003411e01e81be05c05002001c0020020005414e01bc16406805002001c00200200053e4e021416406805001a0140020020005414e021416404e0360200140020020007414e02c426e06805001201000800800053a3a026c21606805e01201000800800033a1a026c21605c05001201000800800053f0602c426e06805001201000600600053a3a026c2160680500120100060060005410602c426e06805000e00c00600600053a3a026c21606805000e00c00600600053a0602c421604e03601200c00800600054106
theorem hd1_9:d1_9.all (receiptTest 1)=true:=by decide+kernel
def _GAM:List ℕ:=decodeReceipts 16 0x26c21606805e01a01800200200033a1a026c24205c05801a01800200200053a1a026c24205605001a01800200200000001024021605c05801a0180020020003411e024021605605001a01800200200000001026c21606805e01601400200200033a1a026c21605c0500160140020020000000102c426e04e04402001c00200200053a22026c24204e04a02002000200200053a02026c24204e04a01e01c00200200000001026c24204804402001c00200200000001024021604e04a02002000200200053a02024021604e04a01e01c00200200000001024021604804402001c0020020000000102c421604203602001c0020020000000102c421604e03601a01400200200000001
theorem hd1_10:_GAM.all (receiptTest 1)=true:=by decide+kernel
def _GAX:List ℕ:=decodeReceipts 16 0x2141be06805e02001c00400400033a1a02141ea05c05802001c00400400053a1a02141ea05605002002000400400053a0202141ea05605001e01c0040040005414e01e81be05c05002001c0040040005414e01bc16406805002001c00400400053e4e021416406805001a0140040040005414e02141ea04e04a02002000400400053a0202141ea04e04a01e01c0040040005410602141ea04804402001c0040040005410601e81be04e04402001c0040040005410602141be04203602001c0040040005410601bc16404e03602001c00400400053e06021416404e03601a01400400400053a0602c421606805002001c0020020005411a02c426e06805001a0140020020005413a
theorem hd1_11:_GAX.all (receiptTest 1)=true:=by decide+kernel
def _GBF:List ℕ:=decodeReceipts 16 0x22a21604e04a01e01c0040040003411e024021604804402002000400400053a02024021604804401e01c0040040003411e02c426e04203602001c00400400053a22026c24204203e02002000400400053a02026c24204203e01e01c0040040003411e024021604203e02001c0040040003411e026c21603c03602001c0040040003411e02c426e04e04401a01400400400053e3a026c24204e04a01a01a00400400033f1e026c24204e04a01801800400400054106026c24204804401a01800400400054106024021604e04401a01800400400054106026c21604e04401601400400400053e0602c426e04203601a01400400400053a3a026c21604203601a01400400400053f06
theorem hd1_12:_GBF.all (receiptTest 1)=true:=by decide+kernel
def _GBG:List ℕ:=decodeReceipts 16 0x26c21606805e01601400400400033a1a026c24205c05801601400400400033e1e026c24205605001601400400400054106024021605c05001601400400400053f0602c426e04e04402001c00400400053a22026c24204e04a02002000400400053a02026c25804e04a01e01c00400400053a22025624204e04a01e01e00400400053a02025624204e04a01c01c0040040003411e026c24204804402002000400400053a02026c25804804401e01e00400400053a02026c25804804401c01c0040040003411e025624204804401e01c0040040003411e024021604e04a02002000400400053a02024022c04e04a01e01e00400400033a1a024022c04e04a01c01c00400400054106
theorem hd1_13:_GBG.all (receiptTest 1)=true:=by decide+kernel
def _GBH:List ℕ:=decodeReceipts 16 0x2141ea04e04a01e01c0060060005410602141ea04804402001c0060060003411e01e81be04e04402001c0060060005410602141be04203602001c0080060005410601bc16404e03602001c00800600053e06021416404e03601a01400800600053e0602c426e06805002001c00400400053f02026c21606805002001c00400400053e1a02c426e06805001a0140040040005413a026c21606805e01a01800400400033a1a026c24205c05801a01800400400053a1a026c24205605001a01a0040040003411e026c24205605401801800400400033f1e026c24205205001801800400400054106024021605c05801a0180040040003411e024021605605001a01800400400054106
theorem hd1_14:_GBH.all (receiptTest 1)=true:=by decide+kernel
def _GBI:List ℕ:=decodeReceipts 16 0x21420005205001e01c0060060003411e01fe1ea05605001e01c0060060003411e01e81be05c05002001c0060060005414e01bc16406805002001c0080060005414e02141be06805e01a01800800800033a1a02141be05c05001a0180080080005410602141be0680500160140080080005410602141be06805e01a01800600600033a1a02141be05c05001a0180060060005410602141be0680500160140060060005410601bc16406805001a01400800600053f0602141ea04e04a02002000800800053a0202141ea04e04a01e01c0080080003411e02141ea04804402001c0080080003411e01e81be04e04402001c0080080005410602141ea04e04a02002000600600053a02
theorem hd1_15:_GBI.all (receiptTest 1)=true:=by decide+kernel
def _GBJ:List ℕ:=decodeReceipts 16 0x2c426e04203601a01400800800053a3a026c21604203601a0140080080005410602c426e04203601a01400600600053a3a026c21604203601a0140060060005410602141be06805e02001c00800800033a1a02141ea05c05802001c00800800053a1a02141ea05605002002000800800053a02021420005605401e01c00800800053a1a021420005205001e01e00800800033a1a021420005205001c01c0080080005410601fe1ea05605001e01c0080080005414e01e81be05c05002001c0080080005414e02141be06805e02001c00600600033a1a02141ea05c05802001c00600600053a1a02141ea05605002002000600600053a02021420005605401e01c00600600053a1a
theorem hd1_16:_GBJ.all (receiptTest 1)=true:=by decide+kernel
def _GBK:List ℕ:=decodeReceipts 16 0x26c24203c03602002000600600053a02026c24203c03601e01c00600600033f1e024021603c03602001c0060060003411e02c426e04e04401a01400800800053e3a026c24204e04a01a01a0080080003411e026c24204e04a01801800800800054106026c24204804401a01a00800800033f1e026c24204804401801800800800054106024021604e04401a01800800800054106026c21604e0440160140080080005410602c426e04e04401a01400600600053e3a026c24204e04a01a01a0060060003411e026c24204e04a01801800600600054106026c24204804401a01800600600054106024021604e04401a01800600600054106026c21604e04401601400600600053f06
theorem hd1_17:_GBK.all (receiptTest 1)=true:=by decide+kernel
def _GBL:List ℕ:=decodeReceipts 16 0x24021604804402002000600600053a02024021604804401e01c0060060003411e02c426e04203602001c00800800053a22026c24204203e02002000800800053a02026c25804203e01e01e00800800053a02026c25804203e01c01c0080080003411e025624204203e01e01c0080080003411e024021604203e02002000800800053a02024021604203e01e01c0080080003411e026c24203c03602002000800800053a02026c24203c03601e01c0080080003411e024021603c03602001c0080080003411e02c426e04203602001c00600600053a22026c24204203e02002000600600053a02026c24204203e01e01c0060060003411e024021604203e02001c0060060003411e
theorem hd1_18:_GBL.all (receiptTest 1)=true:=by decide+kernel
def _GBM:List ℕ:=decodeReceipts 16 0x24021604804402002000800800053a02024021604804401e01c0080080003411e02c426e04e04402001c00600600053a22026c24204e04a02002000600600053a02026c25804e04a01e01c00600600053a22025624204e04a01e01e00600600053a02025624204e04a01c01c0060060003411e026c24204804402002000600600053a02026c25804804401e01e00600600053a02026c25804804401c01c0060060003411e025624204804401e01e00600600033a1a025624204804401c01c0060060003411e024021604e04a02002000600600053a02024022c04e04a01e01e00600600033a1a024022c04e04a01c01c0060060003411e022a21604e04a01e01c0060060003411e
theorem hd1_19:_GBM.all (receiptTest 1)=true:=by decide+kernel
def _GBO:List ℕ:=decodeReceipts 16 0x2c426e04e04402001c00800800053e22026c24204e04a02002000800800053a02026c25804e04a01e01c00800800053a22025624204e04a01e01e00800800053a02025624204e04e01c01c00800800053a1a025624204c04a01c01c0080080003411e026c24204804402002000800800053a02026c25804804401e01e00800800053a02026c25804804401c01c0080080003411e025624204804401e01e00800800033a1a025624204804401c01c0080080003411e024021604e04a02002000800800053a02024022c04e04a01e01e00800800033a1a024022c04e04a01c01c0080080003411e022a21604e04a01e01e00800800033a1a022a21604e04a01c01c00800800054106
theorem hd1_20:_GBO.all (receiptTest 1)=true:=by decide+kernel
def _GBP:List ℕ:=decodeReceipts 16 0x26c24205c05801a01800600600053a1a026c25805605401a01a00600600053a1a025624205605401a01a0060060003411e026c24205205001a01a0060060003411e026c2420560540180180060060003411e026c26405205001801800600600053a3a026225805205001801800600600054106025624205205001801800600600054106024021605c05801a01a00600600053a1a024021605c05801801800600600054106024021605605001a01a0060060003411e024021605605001801800600600054106026c21606805e01601400600600033a1a026c24205c05801601400600600033f1e026c24205605001601400600600054106024021605c05001601400600600054106
theorem hd1_21:_GBP.all (receiptTest 1)=true:=by decide+kernel
def _GBQ:List ℕ:=decodeReceipts 16 0x25624205205001a01a0080080003411e026c2420560540180180080080003411e026c26405205001801800800800053a3a026225805205201801800800800053f1e026225805005001801800800800054106025624205205001801800800800054106024021605c05801a01a00800800053a1a024021605c0580180180080080003411e024021605605001a01a0080080003411e024021605605001801800800800054106026c21606805e01601400800800033a1a026c24205c0580160140080080003411e026c24205605001601400800800054106024021605c0500160140080080005410602c426e06805001a0140060060005413a026c21606805e01a01800600600033a1a
theorem hd1_22:_GBQ.all (receiptTest 1)=true:=by decide+kernel
def _GBR:List ℕ:=decodeReceipts 16 0x1bc16404e03602001c00e00a00054106021416404e03601a01400c00a00053f0602c426e06805002001c00800800054102026c21606805002001c00800800053e1a02c426e06805002001c00600600054102026c21606805002001c00600600053e1a02c426e06805e01a01800800800053a0202c426e05c05001a0180080080005413a02c426e06805001601400800800053f3a026c21606805e01a01800800800033a1a026c24205c05801a01800800800053a1a026c25805605401a01a00800800053a1a025624e05605401a01a00800800053a1a024c24205605401a01a0080080003411e026c26405205001a01a00800800053a3a026225805205001a01a0080080003411e
theorem hd1_23:_GBR.all (receiptTest 1)=true:=by decide+kernel
def _GBS:List ℕ:=decodeReceipts 16 0x1bc16406805001a01400c00a0005410602141be04e04402001c00e00e0005368602141ea04e04a02002000c00c00053a02021420004e04a01e01e00c00c00033a1a021420004e04a01c01c00c00c0005410601fe1ea04e04a01e01c00c00c0003411e02141ea04804402002000c00c00053a0202141ea04804401e01c00c00c0005368601e81be04e04402001c00c00c0005414e02141ea04e04a02002000a00a00053a0202141ea04e04a01e01c00a00a0003411e02141ea04804402002000a00a00053a0202141ea04804401e01c00a00a0005410601e81be04e04402001c00a00a0005412602141be04203602001c00e00e0005368602141be04203602001c00c00a0003411e
theorem hd1_24:_GBS.all (receiptTest 1)=true:=by decide+kernel
def _GBT:List ℕ:=decodeReceipts 16 0x1fe1ea05605401e01c00c00c00053a1a01fe1ea05205001e01c00c00c0005414e01e81be05c05802001c00c00c00053a1a01e81be05605002001c00c00c0005414e02141ea05c05802001c00a00a00053a1a02141ea05605002002000a00a00053a02021420005605401e01c00a00a00053a1a021420005205001e01e00a00a00033a1a021420005205001c01c00a00a0003411e01fe1ea05605001e01c00a00a0005414e01e81be05c05802001c00a00a00053a1a01e81be05605002001c00a00a0005414e01bc16406805002001c00e00a0005414e02141be06805e01a01800c00a00033a1a02141be05c05001a01800c00a0005414e02141be06805001601400a00a00054106
theorem hd1_25:_GBT.all (receiptTest 1)=true:=by decide+kernel
def _GBU:List ℕ:=decodeReceipts 16 0x24021603c03602001c00a00a0003411e02c426e04e04401a01400c00a00053f3a026c21604e04401a01800c00c00053686026c24204e04a01a01a00a00a0003411e026c24204e04a01801800a00a00053686026c24204804401a01800a00a00053686024021604e04401a01800a00a00054106026c21604e04401601400a00a0005410602c421604203601a01400c00a0005368602141be06805002001c00e00e00033a1a02141be06805e02001c00c00a00033a1a02141ea05c05802001c00c00c00053a1a02141ea05605002002000c00c00053a02021420005605401e01c00c00c00053a1a021420005205001e01e00c00c00033a1a021420005205001c01c00c00c00053686
theorem hd1_26:_GBU.all (receiptTest 1)=true:=by decide+kernel
def _GBV:List ℕ:=decodeReceipts 16 0x24021604804402002000a00a00053a02024022c04804401e01e00a00a00033a1a024022c04804401c01c00a00a0003411e022a21604804401e01c00a00a0003411e02c421604203602001c00e00e0005368602c426e04203602001c00c00a00053a22026c21604203e02001c00c00c0003369e026c24204203e02002000a00a00053a02026c25804203e01e01e00a00a00053a02026c25804203e01c01c00a00a0003411e025624204203e01e01c00a00a0003411e024021604203e02002000a00a00053a02024021604203e01e01c00a00a0003411e026c21603c03602001c00c00c00053686026c24203c03602002000a00a00053a02026c24203c03601e01c00a00a0003411e
theorem hd1_27:_GBV.all (receiptTest 1)=true:=by decide+kernel
def _GBW:List ℕ:=decodeReceipts 16 0x25624204e04e01c01c00a00a00053a1a025624e04c04c01c01c00a00a00053a1a025624e04a04a01c01c00a00a0003411e024c24204c04a01c01c00a00a0003411e026c24204804402002000a00a00053a02026c25804804401e01e00a00a00053a02026c26404804801c01c00a00a00053a22026225804804801c01c00a00a0003411e026c25804604401c01c00a00a0003411e025624204804401e01e00a00a00033a1a025624204804401c01c00a00a0003411e024021604e04a02002000a00a00053a02024022c04e04a01e01e00a00a00033a1a024022c04e04a01c01c00a00a0003411e022a21604e04a01e01e00a00a00033a1a022a21604e04a01c01c00a00a0003411e
theorem hd1_28:_GBW.all (receiptTest 1)=true:=by decide+kernel
def _GBX:List ℕ:=decodeReceipts 16 0x26c24204e04a02002000c00c00053a02026c25804e04a01e01c00c00c00053a22025624204e04a01e01e00c00c00053a02025624204e04a01c01c00c00c00053686026c24204804402002000c00c00053a02026c24204804401e01c00c00c00053686024021604e04a02002000c00c00053a02024022c04e04a01e01e00c00c00033a1a024022c04e04a01c01c00c00c00053686022a21604e04a01e01e00c00c00033a1a022a21604e04a01c01c00c00c00053686024021604804402002000c00c00053a02024021604804401e01c00c00c00053686026c24204e04a02002000a00a00053a02026c25804e04a01e01c00a00a00053a22025624204e04a01e01e00a00a00053a02
theorem hd1_29:_GBX.all (receiptTest 1)=true:=by decide+kernel
def _GBZ:List ℕ:=decodeReceipts 16 0x26c26405205001801800a00a00053a3a026225805205201801800a00a0005411e026225805005001801800a00a00053686025624e05205201801800a00a00053f1e025624e05005001801800a00a00054106024c24205205001801800a00a00054106024021605c05801a01a00a00a00053a1a024021605c05801801800a00a0003411e024021605605001a01a00a00a0003411e024021605605001801800a00a00054106026c21606805e01601400a00a00033a1a026c24205c05801601400a00a0003411e026c24205605001601400a00a00053686024021605c05001601400a00a0005410602c421604e04402001c00e00e0003411a02c426e04e04402001c00c00a00053e22
theorem hd1_30:_GBZ.all (receiptTest 1)=true:=by decide+kernel
def _GCA:List ℕ:=decodeReceipts 16 0x26c24205c05801a01800c00c00053a1a026c24205605001a01800c00c00053686024021605c05801a01800c00c00053a1a024021605605001a01800c00c00053686026c24205c05801a01800a00a00053a1a026c25805605401a01a00a00a00053a1a025624e05605401a01a00a00a00053a1a024c24205605601a01a00a00a00053a1a024c24205405401a01a00a00a0003411e026c26405205001a01a00a00a00053a3a026225e05205201a01a00a00a00053a3a025c25c05205201a01a00a00a00053a3a025a25805205201a01a00a00a0003411e026225805005001a01a00a00a0003411e025624205205001a01a00a00a0003411e026c24205605401801800a00a0003411e
theorem hd1_31:_GCA.all (receiptTest 1)=true:=by decide+kernel
def _GCB:List ℕ:=decodeReceipts 8 0x2c426e06805002001c00e00e00054102026c21606805002001c00e00e0003411a02c426e06805002001c00c00a00054102026c21606805002001c00c00a00053f1a02c426e06805e01a01800c00a00053a0202c426e05c05001a01800c00a0005413a02c426e06805001601400a00a0005413a026c21606805e01a01800c00a00033a1a
theorem hd1_32:_GCB.all (receiptTest 1)=true:=by decide+kernel
def codes1:List ℕ:=d1_0++d1_1++d1_2++d1_3++d1_4++d1_5++d1_6++d1_7++d1_8++d1_9++_GAM++_GAX++_GBF++_GBG++_GBH++_GBI++_GBJ++_GBK++_GBL++_GBM++_GBO++_GBP++_GBQ++_GBR++_GBS++_GBT++_GBU++_GBV++_GBW++_GBX++_GBZ++_GCA++_GCB
def boxes1:List Box:=codes1.map receiptBox
theorem boxesvalid1: ∀a∈boxes1,valid 1 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes1.all (receiptTest 1)=true:=by
  simp only [codes1,List.all_append,hd1_0,hd1_1,hd1_2,hd1_3,hd1_4,hd1_5,hd1_6,hd1_7,hd1_8,hd1_9,hd1_10,hd1_11,hd1_12,hd1_13,hd1_14,hd1_15,hd1_16,hd1_17,hd1_18,hd1_19,hd1_20,hd1_21,hd1_22,hd1_23,hd1_24,hd1_25,hd1_26,hd1_27,hd1_28,hd1_29,hd1_30,hd1_31,hd1_32,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d2_0:List ℕ:=decodeReceipts 16 0x5c03205c03201401000600400073a0a005c04805c04800e00800600400053a0a005c03204603200e00800600400000000005c03203001c02001600e00400053a0a005c03203001c01400800a00400000000005c03201a01002001600e00400053a0a005c03201a01001400800a00400000000005c03200e00401c00800e00400000000003001c03001c02001600e00400053a0a003001c03001c01400800a00400000000003001c01a01002001600e00400053a0a003001c01a01001400800a00400000000003001c00e00401c00800e00400000000001a01001a01002001600e00400053a0a001a01001a01001400800a00400000000001a00400e00401c00800e00400000000
theorem hd2_0:d2_0.all (receiptTest 2)=true:=by decide+kernel
def d2_1:List ℕ:=decodeReceipts 16 0x1640b603601e02001600e00400053a0601640b603601e01400800a0040000000001640b601c01202001600e00400053e0a01640b601c01201400800a0040000000001640b601000c01e01400e0040005368e01640b601000c0120080080040000000001640b600a00401400800a0040000000000b405e06803802001600e00400053a0600b405e06803801400800a004000736c600b405e03601e02001600e00400053a0600b405e03601e01400800a0040000000000b405e01c01202001600e00400053a0a00b405e01c01201400800a0040000000000b405e01000401e00800e00400000000005c03205c03202001600e00400053a06005c03205c03201401000a00800000000
theorem hd2_1:d2_1.all (receiptTest 2)=true:=by decide+kernel
def d2_2:List ℕ:=decodeReceipts 16 0x1e81be05c05202001c0040040005414e02141be06805201a0160040040005368601bc16606805202001600400400053e4e02141660500380200160060040005368602c416606803801400800a004000736c202c416603601e02001600e0040005368602c416603601e01400800a0040000000002c416601c01202001600e0040005368602c416601c01201400800a0040000000002c416601000c01e01400e0040005368a02c416601000c0120080080040000000002c416600a00401400800a0040000000001640b606803802001600e0040005412601640b606803801401000a0080005368a01640b60680380140100060040005368a01640b606803800e008006004000536ae
theorem hd2_2:d2_2.all (receiptTest 2)=true:=by decide+kernel
def d2_3:List ℕ:=decodeReceipts 16 0x24021605605201e01c0040040005368602c426e06805201a0160040040005413a026c21606805e01a01600400400033a1a026c21605c05201a0160040040005368602c42160500380200160060060005368602c426e05004602001c0040040005413a026c21605004602001c0040040005368602c421604403802001c0040040005368602c421605003801a0160040040005368602141be06805e02001c00600600033a1a02141be05c05202001c0060060005368602141be06805201a0160060060005368601bc16606805202001600600600053f4e02141be06805e02001c00400400033a1a02141ea05c05202002000400400033a1602141ea05c05201e01c00400400053686
theorem hd2_3:d2_3.all (receiptTest 2)=true:=by decide+kernel
def d2_4:List ℕ:=decodeReceipts 16 0x2c42160500380200160080080005368602141660680380200160080080005368602c426e06805e02001c0060060005410202c426e05c05202001c0060060003369e026c21606805e02001c00600600033e1a026c21605c05202001c0060060005368602c421606805201a0160060060005368602c426e06805e02001c00400400053f0202c426e05c05202002000400400053e0202c426e05c05201e01c004004000536ba026c21606805e02001c00400400033e1a026c24205c05202002000400400053a02026c24205c05801e01c00400400053a1a026c24205605201e01c00400400053686024021605c05202002000400400053a02024021605c05801e01c00400400053a1a
theorem hd2_4:d2_4.all (receiptTest 2)=true:=by decide+kernel
def d2_5:List ℕ:=decodeReceipts 3 0x2c416606803802001600e00a0005368602c421606805202001c0080080003369e02c421606805201a01600800800053686
theorem hd2_5:d2_5.all (receiptTest 2)=true:=by decide+kernel
def codes2:List ℕ:=d2_0++d2_1++d2_2++d2_3++d2_4++d2_5
def boxes2:List Box:=codes2.map receiptBox
theorem boxesvalid2: ∀a∈boxes2,valid 2 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes2.all (receiptTest 2)=true:=by
  simp only [codes2,List.all_append,hd2_0,hd2_1,hd2_2,hd2_3,hd2_4,hd2_5,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d3_0:List ℕ:=decodeReceipts 10 0x2c416606803802001800e0060005368602c416606803801600c00a0060000000002c416603600602000c00e0060000000001640b606803802001800e0060005368601640b606803801600c00a0060000000001640b603600602000c00e0060000000000b405e06803802001800e00600053a0600b405e06803801600c00a0060000000000b405e03600602000c00e00600000000005c00605c00602000c00e00600000000
theorem hd3_0:d3_0.all (receiptTest 3)=true:=by decide+kernel
def codes3:List ℕ:=d3_0
def boxes3:List Box:=codes3.map receiptBox
theorem boxesvalid3: ∀a∈boxes3,valid 3 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes3.all (receiptTest 3)=true:=by
  simp only [codes3,List.all_append,hd3_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d4_0:List ℕ:=decodeReceipts 1 0x2c400806800802001000e00800000000
theorem hd4_0:d4_0.all (receiptTest 4)=true:=by decide+kernel
def codes4:List ℕ:=d4_0
def boxes4:List Box:=codes4.map receiptBox
theorem boxesvalid4: ∀a∈boxes4,valid 4 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes4.all (receiptTest 4)=true:=by
  simp only [codes4,List.all_append,hd4_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d5_0:List ℕ:=decodeReceipts 1 0x2c400a06800a02001400e00a00000000
theorem hd5_0:d5_0.all (receiptTest 5)=true:=by decide+kernel
def codes5:List ℕ:=d5_0
def boxes5:List Box:=codes5.map receiptBox
theorem boxesvalid5: ∀a∈boxes5,valid 5 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes5.all (receiptTest 5)=true:=by
  simp only [codes5,List.all_append,hd5_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d6_0:List ℕ:=decodeReceipts 1 0x2c400c06800c02001800e00c00000000
theorem hd6_0:d6_0.all (receiptTest 6)=true:=by decide+kernel
def codes6:List ℕ:=d6_0
def boxes6:List Box:=codes6.map receiptBox
theorem boxesvalid6: ∀a∈boxes6,valid 6 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes6.all (receiptTest 6)=true:=by
  simp only [codes6,List.all_append,hd6_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d7_0:List ℕ:=decodeReceipts 1 0x2c400e06800e02001c00e00e00000000
theorem hd7_0:d7_0.all (receiptTest 7)=true:=by decide+kernel
def codes7:List ℕ:=d7_0
def boxes7:List Box:=codes7.map receiptBox
theorem boxesvalid7: ∀a∈boxes7,valid 7 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes7.all (receiptTest 7)=true:=by
  simp only [codes7,List.all_append,hd7_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def root (m:ℕ):Box:=⟨max 1 m,7,2*max 1 m,16,0,52,0,354⟩
def tree1:Tree:=(CP.decode 21 0x207008180136d0205008100136d00061020300808002e902010002d4080001ff007f8002b901fd007f0002b90120d01fb007e801f9007e001f7000aa4049b404af407d801f5007d001f3004b7404bb407c8002890131d01f1004af400a6407c001ef007b801ed000a2404c7407b001eb000a2407a80126d012bd00299000c5002b901e9007a0000c501e700798000c5002b90120d00051002e901e50079001e3000ae407880120d002e9000b50136d000d501e10078001df0077801dd00770000e5012bd000f501db00768000f50024901d90076001d7000394075801d500039404574003d4075001d30003d40092404834074801d10074001cf0073801cd00096407300126d00269000e5012bd000f501cb0072801c9007200131d01c70008e400394071801c500039404af4003d400924071001c300708000e501c100700000e50115d000f501bf006f801bd00039406f00115d000f5002490120d000510136d0006101bb006e801b9006e001b7006d8000e501b5004af4003d406d001b30003d4048340014406c801b1006c0000f501af00483400144007a404db4001840086406b801ad006b001ab00031406a80024901a90048340014406a0000b50136d01a700086400354009e4069801a50069001a30068801a100680000e500299019f006780029900ffd000f5002b9019d00670002b900f4d019b00668019900660019700039400a64065800ffd000f5002b9019500650002b900f4d00051002e90006101930037b406480191000ba40640000b5018f0037b4003540638018d00630018b000394062800ffd000f5018900620000f5002490187003d34061801850003d4061001830003d400924060800f4d00051000610181006000006100219017f0037b405f8000d500279010ad017d005f00136d017b005e80136d000310179005e0002e901770002d405d80175005d00173005c80126d012bd0171005c00131d016f004af400a6405b8016d005b0016b000a2404c7405a8012bd00299000c5002b90169005a0000c5016700598000c5002b90120d002e90165005900163000ae405880120d002e9000b50136d016100580015f00578015d004af4057000299015b005680159004c740560012bd00299000c5002b9015700558000c5015500550000c5002b90120d002e90153005480151000ae405400120d002e9000b50136d00031000d5014f00538014d00530014b0052800269000e5012bd000f501490052001470003940518014500039404af4003d4009240510014300508000e5014100500000e50115d000f5013f004f8000f5002490120d0136d013d004f0013b004e8013900039404af4003d404e00137004d8000e50135004d0000e5012bd000f5002490133004c8013100039404c00115d000f5012f004b8000f5002490120d0136d00031012d004b0012b004a8000e50129004af4003d404a001270003d404834049801250003d404900120d001e90136d01230048801210003d404800120d011f00478000f5011d004834007a404db4000c4008640470011b00468000c5011900460000c50024901170048340458000b50136d011500450011300031404480024901110048340440000b50136d00031010f004380136d010d004300136d0003100219000d500279010b00428010900420010700418000e5002990105003ff4003d400ae4041000f4d002e901030040801010040000ff000a6403f800ffd000f5002b900fd003d3400ba4000c403f000ded00fb003e8002e900f90002d403e000f7000ba403d8000b50003100f50037b40035403d000f30003d403c80024900f1003d3403c000ef0003d403b80024900ed003d34000c403b00021900eb0037b403a8000d500279010ad00e9003a00136d00e70039800e50039000e30038800299000c5002b900e100380002b90120d002e900df0037800dd000ae403700120d002e9000b50136d000d500db0036800d90036000d700039404af4003d4035800d500350000e500d3004af4003d400924034800d100340000e500cf004574003d4033800cd0003d4009240483404db4033000cb00328000f500c90048340320001e90136d0021900c70031800c500031403100024900c30048340308000b50136d00c1003000136d00219000d50027900bf002f800bd002f0000f5002b900bb003d3400ba402e800ded00b900035402e000b70003d402d80024900b5003d3402d00021900b30037b402c8000d500279010ad00b1002c000af002b800ad000ae402b000ab000ae40483400ba402a800a9000ba4002d404db40035402a000a700298000f500a5000924029000a30003d40288002490120d0136d00a10008640280000d500279009f00278009d00270000f5002b9009b003d3400ba4026800ded0099000354026000279010ad0001100021000410097002580095000ba404db402500093004db4000c402480091004db4001d4024000279008f0042b40238008d004db40230008b004db4001d402280027900890042b40220000110002100870001540025402180085002100136d00061008300035402080014900810042b40200007f004db401f8007d004db4000c401f0007b001e80136d00031000d50079001e0000d50014900770042b401d80075004db401d0000d50073001c8000d50014900710042b401c0000110002100041006f001b8006d0000d4001540025401b0006b001a8000d500690002a401a0010ad00670000840010401980065001900001100630000d40015400254018800610018000065005f0017800021000490004100079000d9001a9005d0017000095005b00168005900160000110002100570015800149005500150001490085d00530000440148000350005500095005100140004f001380001100021004d000154002540130004b001280006500490012000021000490004100079000d9001a90047001180009500450011000430010800149004100100001490043d003f00004400f8000350005500095003d000f0003b0001540025400e80039000e0000650037000d800021000490004100079000d9001a90035000d000330001540025400c80031000c0002f00004400b8000350005500095002d000b0002b000a8000110002100290001540025400a000270009800250000440008400900005500230000e4000c4001a4003240088002100080001f000044000840078001d0000440070000350005500095001b000680019000600001100021001700015400254005800150005000130000440008400480005500110000e4000c4001a40040000f00038000d0000440008400300005500095000b00028000900020000110002100070001540018000390003100050001000030000800011000210001000154000000039000310006d00069000cd000c90017d00179002dd0059d00b1d).1
theorem cv1:Covered 1 (valid 1) (root 1):=by
 apply CP.sound (listBox boxes1) boxes1.length 1 (valid 1) (tree:=tree1)
 · exact listBox_valid boxes1 (valid 1) boxesvalid1
 · decide+kernel
def tree2:Tree:=(CP.decode 15 0x148005100140000d5004f000a240138010ad004d00130002e9004b00128002e90136d00490003540120004700118000f5002e9004500110004300108002b9000f5004100100003f000ae4003d40483400ba404db400f8003d000f0002e90136d000d500021003b000e80039004db400e00022900370003540008400a2400d80035000ba400d0000d500330037b400c80031000c0000f5002f003d3400ba400b8000d5002d0037b40008400b000289010ad0003100041002b00029400a8002900029400a000270002940098002500025400900005900089000e9001b90023000880021000800007500031000a5001f00078000a5001d00070000a5001b0006800095001900016400224003a4006e4006000170002940058001500029400500013000294004800089000e9001b9001100040000f00038000d0008e4001d4000c4002940030000b00029400280009000294002000079000d9000700018000a5000500010000a500030001e400080001000294000000079000dd000d90018d00189002ed005ad00b2d).1
theorem cv2:Covered 2 (valid 2) (root 2):=by
 apply CP.sound (listBox boxes2) boxes2.length 2 (valid 2) (tree:=tree2)
 · exact listBox_valid boxes2 (valid 2) boxesvalid2
 · decide+kernel
def tree3:Tree:=(CP.decode 6 0x900020000b500070006e4001800050002d40010001b9000300008000b500010006e40000002ed005ad00b2d).1
theorem cv3:Covered 3 (valid 3) (root 3):=by
 apply CP.sound (listBox boxes3) boxes3.length 3 (valid 3) (tree:=tree3)
 · exact listBox_valid boxes3 (valid 3) boxesvalid3
 · decide+kernel
def tree4:Tree:=(CP.decode 1 0x0).1
theorem cv4:Covered 4 (valid 4) (root 4):=by
 apply CP.sound (listBox boxes4) boxes4.length 4 (valid 4) (tree:=tree4)
 · exact listBox_valid boxes4 (valid 4) boxesvalid4
 · decide+kernel
def tree5:Tree:=(CP.decode 1 0x0).1
theorem cv5:Covered 5 (valid 5) (root 5):=by
 apply CP.sound (listBox boxes5) boxes5.length 5 (valid 5) (tree:=tree5)
 · exact listBox_valid boxes5 (valid 5) boxesvalid5
 · decide+kernel
def tree6:Tree:=(CP.decode 1 0x0).1
theorem cv6:Covered 6 (valid 6) (root 6):=by
 apply CP.sound (listBox boxes6) boxes6.length 6 (valid 6) (tree:=tree6)
 · exact listBox_valid boxes6 (valid 6) boxesvalid6
 · decide+kernel
def tree7:Tree:=(CP.decode 1 0x0).1
theorem cv7:Covered 7 (valid 7) (root 7):=by
 apply CP.sound (listBox boxes7) boxes7.length 7 (valid 7) (tree:=tree7)
 · exact listBox_valid boxes7 (valid 7) boxesvalid7
 · decide+kernel
theorem covered (m:ℕ) (hm:0<m) (hh:m≤7):Covered m (valid m) (root m):=by
 interval_cases m
 · exact cv1
 · exact cv2
 · exact cv3
 · exact cv4
 · exact cv5
 · exact cv6
 · exact cv7

end AGH

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BIL
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF NX
open GZ ME LK
open HI LV BH DR
open FF ZGL ON YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {t y r cap low:ℕ}
theorem from_sources (hLow:2985<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 [Fact (Irreducible P.F)] (hFT:low≤wt AT P.F)
 (S:Source P.F) (hS:Profile S 16 52 354 7 0 1)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤7→PA.Covered m
   (ACU.Valid m low t y r cap) (AGH.root m)):
 P.seeds.card≤cap:=by
 classical
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hST:S.T=354:=hS.2.2.1
 have hs:=ADG P.F S (by rw [hST];omega) P.rdegree hchar
   (by rw [hS.2.2.2.2.1];decide)
 have hpow:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣QC (carrierMap P.F) S.P:=by
   change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS S.P).map (carrierMap P.F)
   simpa only [Source.d,hS.2.2.2.2.1,Nat.zero_add] using hs.2
 have hroot:NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0:=by
   exact Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
 obtain ⟨J,hJ,hJS,hJroot,_⟩:=ADQ
   (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
 obtain ⟨hJne,hm,hms,hJb,hJu,hJt,hJs⟩:=AVL P.F S (by rw [hST];omega) J hJ hJS hJroot
 rw [hS.1] at hJb
 rw [hS.2.1] at hJu
 rw [hS.2.2.1] at hJt
 rw [hS.2.2.2.1] at hJs
 let m:=multiplicity P.F J
 have hn:=_Q15 J
 have horder:1≤order J:=Nat.succ_le_of_lt (hm.trans_le hms)
 have hadm:PA.Admissible m (point J):=
   ⟨hms,horder,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
 have hx:Contains (AGH.root m) (point J):=by
   dsimp only [Contains,AGH.root,point]
   refine ⟨max_le horder hms,hJs,?_,hJb,Nat.zero_le _,hJu,Nat.zero_le _,hJt⟩
   have hh:=hn.2.2.1
   omega
 obtain ⟨a,hvalid,ha⟩:=hcov m hm (hms.trans hJs) (point J) hadm hx
 exact ACU.BLH nodes hI P hFT hLow hcap hid J hJ horder a ha rfl hJne hJroot hvalid

theorem packet_count (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) 3924 60 13) (hFT:3895≤wt AT P.F):
 P.seeds.card≤274040000000000000:=by
 classical
 letI:Fact (Irreducible P.F):=⟨P.irreducible⟩
 rcases VT MJ.p0 MJ.shape0 97989970 (by decide)
     MJ.dimension0 nodes P.u0 P.u1 hI P.F P.irreducible (by change 354<_;omega)
     13 60 3924 (by decide) (by decide) (by decide) ⟨P.r_weight,P.y_weight,P.total_weight⟩
     with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · exact (KY.helper_count MJ.p0 nodes P
     (by decide) (by decide) (by decide) (by decide) Q hQ).le.trans (by decide)
 exact from_sources (by decide) nodes hI P hFT S hS (by decide) (by decide+kernel) AGH.covered

end
end BIL

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BW
open MvPolynomial CW DJ
open BX DP DC
open BD DU EF
open CB HI DR LV
open UU ADB
open RCN095 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def fallback:Fin 321:=⟨310,by decide⟩
def Valid (m low t y r cap:ℕ) (a:DR.Box):Prop:=
 BH.check .native (degrees fallback) a m low t y r cap=true∨
 LinearValid a low t y r cap∨
 ∃(i:Fin 21) (useOwner:Bool) (j:Fin 321) (N:ℕ),
   (CN.profile j).L<low∧
   BandValid (degrees j) a m low t y r cap i useOwner N

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem BLH {m low t y r cap:ℕ}
 (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt AT P.F) (hLow:2985<low)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (J:DX.Poly (K:=K)) (hJ:Irreducible J) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (hJroot:((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
 (hc:Valid m low t y r cap a):P.seeds.card≤cap:=by
 rcases hc with hc | hc | ⟨i,useOwner,j,N,hL,hc⟩
 · have hL:(CN.profile fallback).L<low:=by
     have hh:(CN.profile fallback).L=2436:=by decide+kernel
     omega
   rcases AGF fallback nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact (BH.BLQ nodes hI P SZ (degrees fallback) hZ .native a m low cap
     hFT (by omega) (by omega) J hJ ha hroot hJne hc).trans (max_le hid le_rfl)
 · exact CUP P hFT hid J hJ.ne_zero horder a ha hJroot hc
 · rcases AGF j nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact CPT nodes hI P SZ (degrees j) hZ hFT hcap J hJ a ha hroot hJne i useOwner N hc
end
end BW

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ABK
open DR (Box Contains lower upper)
open HI PA UU ADB
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
abbrev valid (m:ℕ):=BW.Valid m 3681 4000 58 13 271000000000000000

set_option autoImplicit false
open CP

def receiptBox (code:ℕ):Box:=
 let x:=code/8589934592
 ⟨x%4096,x/4096%4096,x/4096^2%4096,x/4096^3%4096,
  x/4096^4%4096,x/4096^5%4096,x/4096^6%4096,x/4096^7%4096⟩
def receiptTest (m code:ℕ):Bool:=
 let a:=receiptBox code
 if code%4=0 then BH.check .native (degrees BW.fallback) a m 3681 4000 58 13 271000000000000000
 else if code%4=1 then decide (LinearValid a 3681 4000 58 13 271000000000000000)
 else if h:code/4%32<21∧code/256%512<321 then
  decide ((CN.profile ⟨code/256%512,h.2⟩).L<3681∧
   BandValid (degrees ⟨code/256%512,h.2⟩) a m 3681 4000 58 13 271000000000000000
     ⟨code/4%32,h.1⟩ (code/128%2=1) (code/131072%65536))
 else false

theorem receipt_sound (m code:ℕ) (h:receiptTest m code=true):valid m (receiptBox code):=by
 unfold receiptTest at h
 split_ifs at h with h0 h1 h2
 · exact Or.inl h
 · exact Or.inr (Or.inl (of_decide_eq_true h))
 · have hh:=of_decide_eq_true h
   exact Or.inr (Or.inr ⟨⟨code/4%32,h2.1⟩,decide (code/128%2=1),⟨code/256%512,h2.2⟩,code/131072%65536,hh.1,hh.2⟩)

def decodeReceipts:ℕ→ℕ→List ℕ
 | 0,_=>[]
 | n+1,c=>c%2^132::decodeReceipts n (c/2^132)
def d1_0:List ℕ:=decodeReceipts 16 0x1800e01800e01200c00800600000000001800e01800e01200c004004000736b6001800e01800e01200c00200200000001001800e01800e00a00400400200000000001800e00c00801801000c00800000000001800e00c00801200c00600600000000001800e00c00801000c00400400000000001800e00c00a00e00c00200200000000001800e00c00800a00400400200000000001800e00600200c00400600200000000000c00800c00801801000c00800000000000c00800c00801200c00600600000000000c00800c00801000c00400400000000000c00a00c00a00e00c00200200000000000c00800c00800a00400400200000000000c00200600200c00400600200000000
theorem hd1_0:d1_0.all (receiptTest 1)=true:=by decide+kernel
def d1_1:List ℕ:=decodeReceipts 16 0x2e01a02e01a01200c00200200000001002e01a02e01a00a00800400400000000002e01a02e01a00a00800200200000001002e01a02e01a00600400200200000000002e01a01800e02001400e00200053606002e01a01800e01200c00800600000000002e01a01800e01200c004004000736b6002e01a01800e01200c00200200000001002e01a01800e00a00400400200000000002e01a00c00801801000c00800000000002e01a00c00801200c00600600000000002e01a00c00801000c00400400000000002e01a00c00a00e00c00200200000000002e01a00c00800a00400400200000000002e01a00600200c00400600200000000001800e01800e02001400e00200053606
theorem hd1_1:d1_1.all (receiptTest 1)=true:=by decide+kernel
def d1_2:List ℕ:=decodeReceipts 16 0x5a03002e01a00a00800200200000001005a03002e01a00600400200200000000005a03001800e02001400e00200053606005a03001800e01200c00800600000000005a03001800e01200c004004000736b6005a03001800e01200c00200200000001005a03001800e00a00400400200000000005a03000c00801801000c00800000000005a03000c00801200c00600600000000005a03000c00801000c00400400000000005a03000c00a00e00c00200200000000005a03000c00800a00400400200000000005a03000600200c00400600200000000002e01a02e01a02001400e00200053606002e01a02e01a01200c00800600073692002e01a02e01a01200c004004000936ca
theorem hd1_2:d1_2.all (receiptTest 1)=true:=by decide+kernel
def d1_3:List ℕ:=decodeReceipts 16 0xb205c03401c00a0080020020000000100b205c03401c0060040020020000000100b205c01a01002001400e00200053a0600b205c01a01001200c008002000736b200b205c01a01000a0040040020000000000b205c00e00a01c01400e00a0000000000b205c00e00a01600e00800200073a0e00b205c00e00a00c0040060020000000000b205c00800601000c0080060000000000b205c00800200c00400400200000000005a03005a03002001400e00200053a06005a03005a03001200c00800200073a0a005a03005a03000a00400400200073a0e005a03002e01a02001400e00200053606005a03002e01a01200c00800200073a2e005a03002e01a00a00800400400000000
theorem hd1_3:d1_3.all (receiptTest 1)=true:=by decide+kernel
def d1_4:List ℕ:=decodeReceipts 16 0x1620b401a01002001400e00200053a0601620b401a01001200c008002000736b201620b401a01000a0040040020000000001620b400e00a01c01400e00a0000000001620b400e00a01600e00800200073a0e01620b400e00a00c0040060020000000001620b400800601000c0080060000000001620b400800200c0040040020000000000b205c06803602001400e00200053a0600b205c06803601200400800200053a0a00b205c03401c02001400e00200053a0600b205c03401c01200c00800200073a0e00b208803402a00a00800400400073a0e00b208802801c00a00800400400000000008605c03402a00a00800400400073a0e008605c02801c00a00800400400000000
theorem hd1_4:d1_4.all (receiptTest 1)=true:=by decide+kernel
def d1_5:List ℕ:=decodeReceipts 16 0x2c416400e00a01600e00800200073a0a02c416400e00a00c0040060020000000002c416400800601000c0080060000000002c416400800200c0040040020000000001620b406803602001400e00200053f0601620b406803601200400800200073e2a01620b403401c02001400e00200053a0601620b403401c01200c0080060007368e01620b403401c01200c0040040007368e01620b403401c01200c00200200000001016210c03402a00a00800400400073a0e016210c02801c00a00800400400000000010a0b403402a00a00800400400073a0e010a0b402801c00a0080040040000000001620b403401c00a0080020020000000101620b403401c00600400200200000001
theorem hd1_5:d1_5.all (receiptTest 1)=true:=by decide+kernel
def d1_6:List ℕ:=decodeReceipts 16 0x26c21603402a02001c00400400053f0602c421603402a01a01400400400053e0602c421602801c02001c00400400033a1e02c421602801c01a01400400400053a06021416403401c02001400400400053a0602c416403401c0200140020020000000102c416403401c01200c00800200073e3e02c416403401c00a00800400200073a5202c416403401c0060040020020000000102c416401a01002001400e00a0005368602c416401a01002001400800200053f0602c416401a01001200c008002000736ae02c416401a01000a0080040040000000002c416401a01000a0080020020000000102c416401a0100060040020020000000002c416400e00a01c01400e00a00053a06
theorem hd1_6:d1_6.all (receiptTest 1)=true:=by decide+kernel
def d1_7:List ℕ:=decodeReceipts 16 0x2c421603402a02001c00e00e0005368602c426e03402a02001c00c00a00053a22026c21603402a02001c00c00a0005368602c421603402a01a01400c00a0005368602c421602801c02001400e00a00053686021416403401c02001400e00a00053a0602c426e03402a02001c00800800053a22026c21603402a02001c00800800033e1e02c426e03402a02001c00600600053a22026c21603402a02001c00600600033a1e02c421603402a01a0140080080005368602c421603402a01a01400600600053f0602c421602801c02001c00800600033e1e02c421602801c01a01400800600053a06021416403401c02001400800600053a0602c426e03402a02001c00400400053a22
theorem hd1_7:d1_7.all (receiptTest 1)=true:=by decide+kernel
def d1_8:List ℕ:=decodeReceipts 16 0x26c21606805e01201000800800033a1a026c21605c05001201000800800053a0602c426e06805001201000600600053a3a026c21606805001201000600600053f0602c426e06805000e00c00600600053a3a026c21606805000e00c00600600053a0602c421604e03601200c00800600053e06021416406803601200c00800600053a0602c426e06805001201000400400053a3a026c21606805001201000400400053e0602c426e06805000e00c00400400053a3a026c21606805000e00c00400400053a0602c421604e03601200c00400400053e06021416406803601200c00400400053a0602c416406803601200c0020020000000102c416406803600a00400400200053a06
theorem hd1_8:d1_8.all (receiptTest 1)=true:=by decide+kernel
def d1_9:List ℕ:=decodeReceipts 16 0x25624204e04a01c01c00200200000001026c24204804402001c00200200000001024021604e04a02002000200200053a02024021604e04a01e01c00200200033e1e024021604804402001c0020020000000102c421604203602001c0020020000000102c421604e03601a0140020020000000102141be06805e02001c00200200033a1a02141ea05c05802001c00200200053a1a02141ea05605002002000200200053a0202141ea05605001e01c00200200033e1e01e81be05c05002001c00200200053a4e01bc16406805002001c00200200053a4e021416406805001a01400200200053e4e021416404e03602001400200200053f2602c426e06805001201000800800053a3a
theorem hd1_9:d1_9.all (receiptTest 1)=true:=by decide+kernel
def _GAM:List ℕ:=decodeReceipts 16 0x1bc16406805002001c00400400053a4e021416406805001a01400400400053f4e021416404e03602001400400400073f4e02c421606805002001c00200200053f1a02c426e06805001a01400200200053e3a026c21606805e01a01800200200033a1a026c24205c05801a01800200200053a1a026c24205605001a01800200200000001024021605c05801a01800200200033e1e024021605605001a01800200200000001026c21606805e01601400200200033a1a026c21605c0500160140020020000000102c426e04e04402001c00200200053a22026c24204e04a02002000200200053a02026c25804e04a01e01c00200200053a22025624204e04a01e01e00200200053a02
theorem hd1_10:_GAM.all (receiptTest 1)=true:=by decide+kernel
def _GAX:List ℕ:=decodeReceipts 16 0x26c24204203e01e01c00400400033e1e024021604203e02001c00400400033e1e026c21603c03602001c00400400033e1e02c426e04e04401a01400400400053a3a026c24204e04a01a01a00400400033a1e026c24204e04a01801800400400053e06026c24204804401a01800400400053e06024021604e04401a01800400400053a06026c21604e04401601400400400053a0602c426e04203601a01400400400053a3a026c21604203601a01400400400053a0602141be06805e02001c00400400033a1a02141ea05c05802001c00400400053a1a02141ea05605002002000400400053a0202141ea05605001e01c00400400033f1e01e81be05c05002001c00400400053e4e
theorem hd1_11:_GAX.all (receiptTest 1)=true:=by decide+kernel
def _GBF:List ℕ:=decodeReceipts 16 0x26c21605c05001601400400400053f0602c426e04e04402001c00400400053a22026c24204e04a02002000400400053a02026c25804e04a01e01c00400400053a22025624204e04a01e01e00400400053a02025624204e04a01c01c00400400033e1e026c24204804402002000400400053a02026c25804804401e01e00400400053a02026c25804804401c01c00400400033e1e025624204804401e01c00400400033e1e024021604e04a02002000400400053a02024021604e04a01e01c00400400033f1e024021604804402002000400400053a02024021604804401e01c00400400033e1e02c426e04203602001c00400400053a22026c24204203e02002000400400053a02
theorem hd1_12:_GBF.all (receiptTest 1)=true:=by decide+kernel
def _GBG:List ℕ:=decodeReceipts 16 0x2141ea04804402001c00600600033e1e01e81be04e04402001c00600600053e0602141be04203602001c00800600053e0601bc16404e03602001c00800600053a06021416404e03601a01400800600053a0602c426e06805002001c00400400053a02026c21606805002001c00400400053a1a02c426e06805001a01400400400053e3a026c21606805e01a01800400400033a1a026c24205c05801a01800400400053a1a026c24205605001a01a00400400033f1e026c24205605401801800400400033a1e026c24205205001801800400400053f06024021605c05801a01800400400033e1e024021605605001a01800400400053f06026c21606805e01601400400400033a1a
theorem hd1_13:_GBG.all (receiptTest 1)=true:=by decide+kernel
def _GBH:List ℕ:=decodeReceipts 16 0x1fe1ea05605001e01c00600600033f1e01e81be05c05002001c00600600053e4e01bc16406805002001c00800600053a4e02141be06805e01a01800800800033a1a02141be05c05001a01800800800053f0602141be06805001601400800800053e0602141be06805e01a01800600600033a1a02141be05c05001a01800600600053e0602141be06805001601400600600053e0601bc16406805001a01400800600053a0602141ea04e04a02002000800800053a0202141ea04e04a01e01c00800800033e1e02141ea04804402001c00800800033f1e01e81be04e04402001c00800800053f0602141ea04e04a02002000600600053a0202141ea04e04a01e01c00600600053f06
theorem hd1_14:_GBH.all (receiptTest 1)=true:=by decide+kernel
def _GBI:List ℕ:=decodeReceipts 16 0x2c426e04203601a01400800800053a3a026c21604203601a01400800800053e0602c426e04203601a01400600600053a3a026c21604203601a01400600600053e0602141be06805e02001c00800800033a1a02141ea05c05802001c00800800053a1a02141ea05605002002000800800053a02021420005605401e01c00800800053a1a021420005205001e01c00800800053f4e01fe1ea05605001e01c00800800053e4e01e81be05c05002001c00800800053e4e02141be06805e02001c00600600033a1a02141ea05c05802001c00600600053a1a02141ea05605002002000600600053a02021420005605401e01c00600600053a1a021420005205001e01c00600600033f1e
theorem hd1_15:_GBI.all (receiptTest 1)=true:=by decide+kernel
def _GBJ:List ℕ:=decodeReceipts 16 0x26c24204203e01e01c00600600033e1e024021604203e02001c00600600033e1e026c21603c03602001c00600600033f1e02c426e04e04401a01400800800053a3a026c24204e04a01a01a00800800033e1e026c24204e04a01801800800800053f06026c24204804401a01a00800800033a1e026c24204804401801800800800053e06024021604e04401a01800800800053e06026c21604e04401601400800800053a0602c426e04e04401a01400600600053a3a026c24204e04a01a01a00600600033e1e026c24204e04a01801800600600053e06026c24204804401a01800600600053f06024021604e04401a01800600600053e06026c21604e04401601400600600053a06
theorem hd1_16:_GBJ.all (receiptTest 1)=true:=by decide+kernel
def _GBK:List ℕ:=decodeReceipts 16 0x25624204804401e01c00600600033f1e024021604e04a02002000600600053a02024022c04e04a01e01e00600600033a1a024022c04e04a01c01c00600600033e1e022a21604e04a01e01c00600600033e1e024021604804402002000600600053a02024021604804401e01c00600600033e1e02c426e04203602001c00800800053a22026c24204203e02002000800800053a02026c24204203e01e01c00800800033f1e024021604203e02001c00800800033f1e026c24203c03602002000800800053a02026c24203c03601e01c00800800033e1e024021603c03602001c00800800033e1e02c426e04203602001c00600600053a22026c24204203e02002000600600053a02
theorem hd1_17:_GBK.all (receiptTest 1)=true:=by decide+kernel
def _GBL:List ℕ:=decodeReceipts 16 0x25624204804401e01e00800800033a1a025624204804401c01c00800800033e1e024021604e04a02002000800800053a02024022c04e04a01e01e00800800033a1a024022c04e04a01c01c00800800033e1e022a21604e04a01e01c00800800033f1e024021604804402002000800800053a02024021604804401e01c00800800033e1e02c426e04e04402001c00600600053a22026c24204e04a02002000600600053a02026c25804e04a01e01c00600600053a22025624204e04a01e01e00600600053a02025624204e04a01c01c00600600033e1e026c24204804402002000600600053a02026c25804804401e01e00600600053a02026c25804804401c01c00600600033e1e
theorem hd1_18:_GBL.all (receiptTest 1)=true:=by decide+kernel
def _GBM:List ℕ:=decodeReceipts 16 0x25624205205001801800600600053e06024021605c05801a01800600600033f1e024021605605001a01a00600600033e1e024021605605001801800600600053e06026c21606805e01601400600600033a1a026c24205c05801601400600600033a1e026c24205605001601400600600053e06024021605c05001601400600600053e0602c426e04e04402001c00800800053a22026c24204e04a02002000800800053a02026c25804e04a01e01c00800800053a22025624204e04a01e01e00800800053a02025624204e04a01c01c00800800033f1e026c24204804402002000800800053a02026c25804804401e01e00800800053a02026c25804804401c01c00800800033e1e
theorem hd1_19:_GBM.all (receiptTest 1)=true:=by decide+kernel
def _GBO:List ℕ:=decodeReceipts 16 0x24021605c05801801800800800033e1e024021605605001a01a00800800033e1e024021605605001801800800800053e06026c21606805e01601400800800033a1a026c24205c05801601400800800033e1e026c24205605001601400800800053f06024021605c05001601400800800053e0602c426e06805001a01400600600053f3a026c21606805e01a01800600600033a1a026c24205c05801a01800600600053a1a026c25805605401a01a00600600053a1a025624205605401a01a00600600033e1e026c24205205001a01a00600600033e1e026c24205605401801800600600033e1e026c26405205001801800600600053a3a026225805205001801800600600053f06
theorem hd1_20:_GBO.all (receiptTest 1)=true:=by decide+kernel
def _GBP:List ℕ:=decodeReceipts 16 0x2c426e06805002001c00800800053e02026c21606805002001c00800800053a1a02c426e06805002001c00600600053e02026c21606805002001c00600600053a1a02c426e06805001a01400800800053f3a026c21606805e01a01800800800033a1a026c24205c05801a01800800800053a1a026c25805605401a01a00800800053a1a025624205605401a01a00800800033f1e026c24205205001a01a00800800033f1e026c24205605401801800800800033e1e026c26405205001801800800800053a3a026225805205201801800800800053a1e026225805005001801800800800053f06025624205205001801800800800053e06024021605c05801a01a00800800053a1a
theorem hd1_21:_GBP.all (receiptTest 1)=true:=by decide+kernel
def _GBQ:List ℕ:=decodeReceipts 16 0x2141be04e04402001c00e00e0005368602141ea04e04a02002000c00c00053a02021420004e04a01e01e00c00c00033a1a021420004e04a01c01c00c00c00053f0601fe1ea04e04a01e01c00c00c00033e1e02141ea04804402002000c00c00053a0202141ea04804401e01c00c00c00053f0601e81be04e04402001c00c00c00053e4e02141ea04e04a02002000a00a00053a0202141ea04e04a01e01c00a00a00033f1e02141ea04804402002000a00a00053a0202141ea04804401e01c00a00a00053e0601e81be04e04402001c00a00a00033f1e02141be04203602001c00e00a00033f1e01bc16404e03602001c00e00a00053e06021416404e03601a01400c00a00053a06
theorem hd1_22:_GBQ.all (receiptTest 1)=true:=by decide+kernel
def _GBR:List ℕ:=decodeReceipts 16 0x21420005205001c01c00c00c0005368601fe1ea05605001e01c00c00c00053f4e01e81be05c05802001c00c00c00053a1a01e81be05605002001c00c00c00053e4e02141ea05c05802001c00a00a00053a1a02141ea05605002002000a00a00053a02021420005605401e01c00a00a00053a1a021420005205001e01e00a00a00033a1a021420005205001c01c00a00a00053f0601fe1ea05605001e01c00a00a00053e4e01e81be05c05002001c00a00a00053f4e01bc16406805002001c00e00a00053e4e02141be06805e01a01800c00a00033a1a02141be05c05001a01800c00a00053f4e02141be06805001601400a00a00053f0601bc16406805001a01400c00a00053e06
theorem hd1_23:_GBR.all (receiptTest 1)=true:=by decide+kernel
def _GBS:List ℕ:=decodeReceipts 16 0x26c24203c03601e01c00a00a00033e1e024021603c03602001c00a00a00033e1e02c426e04e04401a01400c00a00053a3a026c21604e04401a01800c00c00053686026c24204e04a01a01a00a00a00033f1e026c24204e04a01801800a00a00053686026c24204804401a01800a00a00053686024021604e04401a01800a00a00053f06026c21604e04401601400a00a00053e0602c421604203601a01400c00a0005368602141be06805002001c00e00e00033a1a02141be06805e02001c00c00a00033a1a02141ea05c05802001c00c00c00053a1a02141ea05605002002000c00c00053a02021420005605401e01c00c00c00053a1a021420005205001e01e00c00c00033a1a
theorem hd1_24:_GBS.all (receiptTest 1)=true:=by decide+kernel
def _GBT:List ℕ:=decodeReceipts 16 0x24022c04e04a01c01c00a00a00033f1e022a21604e04a01e01e00a00a00033a1a022a21604e04a01c01c00a00a00033e1e024021604804402002000a00a00053a02024021604804401e01c00a00a00033f1e02c421604203602001c00e00e0005368602c426e04203602001c00c00a00053a22026c21604203e02001c00c00c00053686026c24204203e02002000a00a00053a02026c25804203e01e01e00a00a00053a02026c25804203e01c01c00a00a00053686025624204203e01e01c00a00a00033e1e024021604203e02002000a00a00053a02024021604203e01e01c00a00a00033e1e026c21603c03602001c00c00c00053686026c24203c03602002000a00a00053a02
theorem hd1_25:_GBT.all (receiptTest 1)=true:=by decide+kernel
def _GBU:List ℕ:=decodeReceipts 16 0x22a21604e04a01e01e00c00c00033a1a022a21604e04a01c01c00c00c00053686024021604804402002000c00c00053a02024021604804401e01c00c00c00053686026c24204e04a02002000a00a00053a02026c25804e04a01e01c00a00a00053a22025624204e04a01e01e00a00a00053a02025624204e04e01c01c00a00a00053a1a025624204c04a01c01c00a00a00033f1e026c24204804402002000a00a00053a02026c25804804401e01e00a00a00053a02026c25804804401c01c00a00a00033f1e025624204804401e01e00a00a00033a1a025624204804401c01c00a00a00033e1e024021604e04a02002000a00a00053a02024022c04e04a01e01e00a00a00033a1a
theorem hd1_26:_GBU.all (receiptTest 1)=true:=by decide+kernel
def _GBV:List ℕ:=decodeReceipts 16 0x24021605605001801800a00a00053f06026c21606805e01601400a00a00033a1a026c24205c05801601400a00a00033e1e026c24205605001601400a00a00053686024021605c05001601400a00a00053e0602c421604e04402001c00e00e0005368602c426e04e04402001c00c00a00053a22026c24204e04a02002000c00c00053a02026c25804e04a01e01c00c00c00053a22025624204e04a01e01e00c00c00053a02025624204e04a01c01c00c00c00053686026c24204804402002000c00c00053a02026c24204804401e01c00c00c00053686024021604e04a02002000c00c00053a02024022c04e04a01e01e00c00c00033a1a024022c04e04a01c01c00c00c00053686
theorem hd1_27:_GBV.all (receiptTest 1)=true:=by decide+kernel
def _GBW:List ℕ:=decodeReceipts 16 0x25624e05605401a01a00a00a00053a1a024c24205605601a01a00a00a00053a1a024c24205405401a01a00a00a00033f1e026c26405205001a01a00a00a00053a3a026225e05205201a01a00a00a00053a3a025c25805205201a01a00a00a00033f1e026225805005001a01a00a00a00033f1e025624205205001a01a00a00a00033f1e026c24205605401801800a00a00033f1e026c26405205001801800a00a00053a3a026225805205201801800a00a00053e1e026225805005001801800a00a00053686025624205205001801800a00a00053f06024021605c05801a01a00a00a00053a1a024021605c05801801800a00a00033e1e024021605605001a01a00a00a00033f1e
theorem hd1_28:_GBW.all (receiptTest 1)=true:=by decide+kernel
def _GBX:List ℕ:=decodeReceipts 14 0x2c426e06805002001c00e00e00053f02026c21606805002001c00e00e00033e1a02c426e06805002001c00c00a00053e02026c21606805002001c00c00a00053a1a02c426e06805e01a01800c00a00053a0202c426e05c05001a01800c00a00053e3a02c426e06805001601400a00a00053e3a026c21606805e01a01800c00a00033a1a026c24205c05801a01800c00c00053a1a026c24205605001a01800c00c00053686024021605c05801a01800c00c00053a1a024021605605001a01800c00c00053686026c24205c05801a01800a00a00053a1a026c25805605401a01a00a00a00053a1a
theorem hd1_29:_GBX.all (receiptTest 1)=true:=by decide+kernel
def codes1:List ℕ:=d1_0++d1_1++d1_2++d1_3++d1_4++d1_5++d1_6++d1_7++d1_8++d1_9++_GAM++_GAX++_GBF++_GBG++_GBH++_GBI++_GBJ++_GBK++_GBL++_GBM++_GBO++_GBP++_GBQ++_GBR++_GBS++_GBT++_GBU++_GBV++_GBW++_GBX
def boxes1:List Box:=codes1.map receiptBox
theorem boxesvalid1: ∀a∈boxes1,valid 1 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes1.all (receiptTest 1)=true:=by
  simp only [codes1,List.all_append,hd1_0,hd1_1,hd1_2,hd1_3,hd1_4,hd1_5,hd1_6,hd1_7,hd1_8,hd1_9,hd1_10,hd1_11,hd1_12,hd1_13,hd1_14,hd1_15,hd1_16,hd1_17,hd1_18,hd1_19,hd1_20,hd1_21,hd1_22,hd1_23,hd1_24,hd1_25,hd1_26,hd1_27,hd1_28,hd1_29,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d2_0:List ℕ:=decodeReceipts 16 0x5c03205c03201401000600400073a0a005c04805c04800e00800600400053a0a005c03204603200e00800600400000000005c03203001c02001600e00400053a0a005c03203001c01400800a00400000000005c03201a01002001600e00400053a0a005c03201a01001400800a00400000000005c03200e00401c00800e00400000000003001c03001c02001600e00400053a0a003001c03001c01400800a00400000000003001c01a01002001600e00400053a0a003001c01a01001400800a00400000000003001c00e00401c00800e00400000000001a01001a01002001600e00400053a0a001a01001a01001400800a00400000000001a00400e00401c00800e00400000000
theorem hd2_0:d2_0.all (receiptTest 2)=true:=by decide+kernel
def d2_1:List ℕ:=decodeReceipts 16 0x1640b606803801401000a0080005368a01640b6068038014008006004000736c601640b603601e02001600e00400053a0601640b603601e01400800a0040000000001640b601c01202001600e00400053a0a01640b601c01201400800a0040000000001640b601000401e00800e0040000000000b405e06803802001600e00400053a0600b405e06803801400800a004000736c600b405e03601e02001600e00400053a0600b405e03601e01400800a0040000000000b405e01c01202001600e00400053a0a00b405e01c01201400800a0040000000000b405e01000401e00800e00400000000005c03205c03202001600e00400053a06005c03205c03201401000a00800000000
theorem hd2_1:d2_1.all (receiptTest 2)=true:=by decide+kernel
def d2_2:List ℕ:=decodeReceipts 16 0x2141be06805e02001c00400400033a1a02141ea05c05202002000400400033a1602141ea05c05201e01c0040040005368601e81be05c05202001c00400400053e4e02141be06805201a0160040040005368601bc16606805202001600400400053a4e02141660500380200160060040005368602c416606803801400800a004000736c202c416603601e02001600e0040005368602c416603601e01400800a0040000000002c416601c01202001600e0040005368602c416601c01201400800a0040000000002c416601000c01e01400e0040005368a02c416601000c0120080080040000000002c416600a00401400800a0040000000001640b606803802001600e00400053f06
theorem hd2_2:d2_2.all (receiptTest 2)=true:=by decide+kernel
def d2_3:List ℕ:=decodeReceipts 16 0x2c426e05c05202002000400400053a0202c426e05c05201e01c00400400053f3a026c21606805e02001c00400400033a1a026c24205c05202002000400400053a02026c24205c05201e01c0040040003369e024021605c05202002000400400053a02024021605c05201e01c0040040005368602c426e06805201a01600400400053e3a026c21606805201a0160040040005368602c42160500380200160060060005368602c421605003802001c0040040003369e02c421605003801a0160040040005368602141be06805e02001c00600600033a1a02141be05c05202001c0060060005368602141be06805201a0160060060005368601bc16606805202001600600600053686
theorem hd2_3:d2_3.all (receiptTest 2)=true:=by decide+kernel
def d2_4:List ℕ:=decodeReceipts 8 0x2c416606803802001600e00a0005368602c41660680380200160080080005368602c426e06805e02001c00600600053e0202c426e05c05202001c00600600053686026c21606805e02001c00600600033a1a026c21605c05202001c0060060005368602c421606805201a0160060060005368602c426e06805e02001c00400400053a02
theorem hd2_4:d2_4.all (receiptTest 2)=true:=by decide+kernel
def codes2:List ℕ:=d2_0++d2_1++d2_2++d2_3++d2_4
def boxes2:List Box:=codes2.map receiptBox
theorem boxesvalid2: ∀a∈boxes2,valid 2 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes2.all (receiptTest 2)=true:=by
  simp only [codes2,List.all_append,hd2_0,hd2_1,hd2_2,hd2_3,hd2_4,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d3_0:List ℕ:=decodeReceipts 10 0x2c416606803802001800e0060005368602c416606803801600c00a0060000000002c416603600602000c00e0060000000001640b606803802001800e00600053f0601640b606803801600c00a0060000000001640b603600602000c00e0060000000000b405e06803802001800e00600053a0600b405e06803801600c00a0060000000000b405e03600602000c00e00600000000005c00605c00602000c00e00600000000
theorem hd3_0:d3_0.all (receiptTest 3)=true:=by decide+kernel
def codes3:List ℕ:=d3_0
def boxes3:List Box:=codes3.map receiptBox
theorem boxesvalid3: ∀a∈boxes3,valid 3 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes3.all (receiptTest 3)=true:=by
  simp only [codes3,List.all_append,hd3_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d4_0:List ℕ:=decodeReceipts 1 0x2c400806800802001000e00800000000
theorem hd4_0:d4_0.all (receiptTest 4)=true:=by decide+kernel
def codes4:List ℕ:=d4_0
def boxes4:List Box:=codes4.map receiptBox
theorem boxesvalid4: ∀a∈boxes4,valid 4 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes4.all (receiptTest 4)=true:=by
  simp only [codes4,List.all_append,hd4_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d5_0:List ℕ:=decodeReceipts 1 0x2c400a06800a02001400e00a00000000
theorem hd5_0:d5_0.all (receiptTest 5)=true:=by decide+kernel
def codes5:List ℕ:=d5_0
def boxes5:List Box:=codes5.map receiptBox
theorem boxesvalid5: ∀a∈boxes5,valid 5 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes5.all (receiptTest 5)=true:=by
  simp only [codes5,List.all_append,hd5_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d6_0:List ℕ:=decodeReceipts 1 0x2c400c06800c02001800e00c00000000
theorem hd6_0:d6_0.all (receiptTest 6)=true:=by decide+kernel
def codes6:List ℕ:=d6_0
def boxes6:List Box:=codes6.map receiptBox
theorem boxesvalid6: ∀a∈boxes6,valid 6 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes6.all (receiptTest 6)=true:=by
  simp only [codes6,List.all_append,hd6_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d7_0:List ℕ:=decodeReceipts 1 0x2c400e06800e02001c00e00e00000000
theorem hd7_0:d7_0.all (receiptTest 7)=true:=by decide+kernel
def codes7:List ℕ:=d7_0
def boxes7:List Box:=codes7.map receiptBox
theorem boxesvalid7: ∀a∈boxes7,valid 7 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes7.all (receiptTest 7)=true:=by
  simp only [codes7,List.all_append,hd7_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def root (m:ℕ):Box:=⟨max 1 m,7,2*max 1 m,16,0,52,0,354⟩
def tree1:Tree:=(CP.decode 20 0x1dd007700136d01db007680136d0006101d900760002e901d70002d4075801d500750002b901d300748002b90120d01d10074001cf0073801cd000aa4049b404af4073001cb00728012ed01c9000a2404c740720012bd0029901c70071801c500710002890131d01c3004af400a640031400ae4070801c1000314070001bf00031400ae4048340014400ba406f801bd006f0002b901bb00483400ba4002d404db40035406e801b9006e001b7006d801b500039404af4003d406d001b30003d40092406c801b1006c0000e501af006b8000e50115d000f501ad006b0000f5002490120d01ab006a801a9006a001a70009a40039404af4003d4069801a500690000e501a300688000e5012bd000f50024901a100680019f0003940678019d00039404574003d40670019b0003d400924048340014404db400184066801990066001970065801950003940650012bd000f5019300648000f50120d00051019100640018f0003d406380120d00051001e90136d0006100219018d00630018b00628000c5018900092406200120d0005101870002d404db4061800219000d500279018500610018300608018100600017f00039400a6405f800ffd000f5002b9017d005f0002b900f4d017b005e80179005e0017700039400a6405d800ffd000f5002b90175003d340014400ba40018405d000ded0173005c8002e901710002d405c000ded000d5016f005b8016d005b0000e5016b003ff4003d405a801690003d40092405a000f4d016700598000f5016500590000f5002490163003d34001440018405880021901610037b40580000d500279010ad015f005780136d015d005700136d00031015b005680159005600157004af4055800299015500550015300548002890131d0151004af400a640031400ae40540014f0003140538014d00031400ae40483400ba40530014b00528002b9014900483400ba4002d404db40520014700518014500510012bd0143000a6405080141005000131d013f004af400a640031400ae404f8013d004f0000c5002b90120d002e9013b004e80139000ae404e00120d002e9000b50136d00031000d50137004d80135004d0013300039404af4003d404c80131004c0000e5012f004b8000e5012bd000f500249012d004b0012b00039404a80115d000f50129004a0000f5002490120d0136d012700498012500490012300039404af4003d40488012100480000e5011f004af4003d4009240478011d00470000e5011b004574003d4046801190003d4009240483404db4000c40460011700458000f50115004834045001130003d404480120d001e90136d011100440010f0003d404380120d010d0007a404db4000c4008640430010b00428000c5010900420000c50024901070048340418000b50136d010500410010300031404080024901010048340400000b50136d0003100ff003f80136d00fd003f00136d0003100219000d50027900fb003e800f9003e000f7000a6403d800ffd000f5002b900f5003d3400ba403d000f3003c800f1003c00029900ef003ff4003d400ae403b800f4d002e90003100ed0037b403b000eb000ba403a8000b500e9003a0002e900e70002d4000c4039800ded000d500e500390000f500e3000924038800f4d00e100380000f500df000924037800f4d0003100dd000864037000ded00db000354009e4042b4036800d9004db4036000d70035800d50035000d3000a640031400ae4034800d1000ae40483400ba4034000cf000ba4002d404db400354033800cd0033000cb00328000e5012bd000f500c90032000c70003940318012bd000f50024900c500310000f500c300308000f5002490120d0136d00c10030000bf0003d402f80120d00bd0007a404db40086402f000bb002e8000c500b900092402e00120d00b70002d404db402d800b5004db40086400354009e402d000b3002c800b10003d400ae402c000f4d002e900af0037b402b8000d500ad0009e4042b402b000ab002a800a9002a0002b900a700298002b90120d002e900a500290002e9000b50136d000d500a30028800a100280009f00039404af4003d4027800249009d00270000f5009b0009240483404db40268002190099000354009e4026000970025800950003d400ae4025000f4d002e900930037b40248000d500910009e4042b40004400084001040240008f00238002e90136d008d002300136d00031008b002280136d0007500890009e40220010ad0087002180136d0085002100136d0007500830009e40208010ad00810000440008402000005500095007f001f8007d004db40018401f0000d5007b00052401e8010ad0079001e00136d0077001d80136d000310075001d000031000d50073001c8000d50014900710042b401c0006f004db401b8000d5006d001b0000d500149006b0042b401a80001100021000410069001a000670000d400154002540198006500010401900063001880001100610000d400154002540180005f0017800065005d0017000021000490004100079000d9001a9005b0016800095005900160005700158000110002100550015000149005300148001490085d00510000440140000350005500095004f00138004d000154002540130004b001280006500490012000021000490004100079000d9001a90047001180009500450011000430010800149004100100001490043d003f00004400f8000350005500095003d000f0003b0001540025400e80039000e0000650037000d800021000490004100079000d9001a90035000d000330001540025400c80031000c0002f00004400b8000350005500095002d000b0002b000a8000110002100290001540025400a000270009800250000440008400900005500230000e4000c4001a4003240088002100080001f000044000840078001d0000440070000350005500095001b000680019000600001100021001700015400254005800150005000130000440008400480005500110000e4000c4001a40040000f00038000d0000440008400300005500095000b00028000900020000110002100070001540018000390003100050001000030000800011000210001000154000000039000310006d00069000cd000c90017d00179002dd0059d00b1d).1
theorem cv1:Covered 1 (valid 1) (root 1):=by
 apply CP.sound (listBox boxes1) boxes1.length 1 (valid 1) (tree:=tree1)
 · exact listBox_valid boxes1 (valid 1) boxesvalid1
 · decide+kernel
def tree2:Tree:=(CP.decode 14 0x4700118004500110002e9004300108002e90136d00410003540100003f000f8000f5002e9003d000f0003b0003d400e800390003d40483400ba404db400e00037004db4003540008400d80035000d0000d500021002890033000c8002e9003100035400c000ded002f000b8002d0003d400b000f4d002e9002b00035400a800ded000210029000a24042b4000c40010400a0000a5002700098000a5002500090000a500230008800095002100016400224003a4006e40080001f0007800031000a5001d00070000a5001b00068000a50019000224003a4006e4006000170002940058001500029400500013000294004800089000e9001b9001100040000f00038000d0008e4001d4000c4002940030000b00029400280009000294002000079000d9000700018000a5000500010000a500030001e400080001000294000000079000dd000d90018d00189002ed005ad00b2d).1
theorem cv2:Covered 2 (valid 2) (root 2):=by
 apply CP.sound (listBox boxes2) boxes2.length 2 (valid 2) (tree:=tree2)
 · exact listBox_valid boxes2 (valid 2) boxesvalid2
 · decide+kernel
def tree3:Tree:=(CP.decode 6 0x900020000b500070006e4001800050002d40010001b9000300008000b500010006e40000002ed005ad00b2d).1
theorem cv3:Covered 3 (valid 3) (root 3):=by
 apply CP.sound (listBox boxes3) boxes3.length 3 (valid 3) (tree:=tree3)
 · exact listBox_valid boxes3 (valid 3) boxesvalid3
 · decide+kernel
def tree4:Tree:=(CP.decode 1 0x0).1
theorem cv4:Covered 4 (valid 4) (root 4):=by
 apply CP.sound (listBox boxes4) boxes4.length 4 (valid 4) (tree:=tree4)
 · exact listBox_valid boxes4 (valid 4) boxesvalid4
 · decide+kernel
def tree5:Tree:=(CP.decode 1 0x0).1
theorem cv5:Covered 5 (valid 5) (root 5):=by
 apply CP.sound (listBox boxes5) boxes5.length 5 (valid 5) (tree:=tree5)
 · exact listBox_valid boxes5 (valid 5) boxesvalid5
 · decide+kernel
def tree6:Tree:=(CP.decode 1 0x0).1
theorem cv6:Covered 6 (valid 6) (root 6):=by
 apply CP.sound (listBox boxes6) boxes6.length 6 (valid 6) (tree:=tree6)
 · exact listBox_valid boxes6 (valid 6) boxesvalid6
 · decide+kernel
def tree7:Tree:=(CP.decode 1 0x0).1
theorem cv7:Covered 7 (valid 7) (root 7):=by
 apply CP.sound (listBox boxes7) boxes7.length 7 (valid 7) (tree:=tree7)
 · exact listBox_valid boxes7 (valid 7) boxesvalid7
 · decide+kernel
theorem covered (m:ℕ) (hm:0<m) (hh:m≤7):Covered m (valid m) (root m):=by
 interval_cases m
 · exact cv1
 · exact cv2
 · exact cv3
 · exact cv4
 · exact cv5
 · exact cv6
 · exact cv7

end ABK

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AXH
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF NX
open GZ ME LK
open HI LV BH DR
open FF ZGL ON YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {t y r cap low:ℕ}
theorem from_sources (hLow:2985<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 [Fact (Irreducible P.F)] (hFT:low≤wt AT P.F)
 (S:Source P.F) (hS:Profile S 16 52 354 7 0 1)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤7→PA.Covered m
   (BW.Valid m low t y r cap) (ABK.root m)):
 P.seeds.card≤cap:=by
 classical
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hST:S.T=354:=hS.2.2.1
 have hs:=ADG P.F S (by rw [hST];omega) P.rdegree hchar
   (by rw [hS.2.2.2.2.1];decide)
 have hpow:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣QC (carrierMap P.F) S.P:=by
   change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS S.P).map (carrierMap P.F)
   simpa only [Source.d,hS.2.2.2.2.1,Nat.zero_add] using hs.2
 have hroot:NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0:=by
   exact Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
 obtain ⟨J,hJ,hJS,hJroot,_⟩:=ADQ
   (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
 obtain ⟨hJne,hm,hms,hJb,hJu,hJt,hJs⟩:=AVL P.F S (by rw [hST];omega) J hJ hJS hJroot
 rw [hS.1] at hJb
 rw [hS.2.1] at hJu
 rw [hS.2.2.1] at hJt
 rw [hS.2.2.2.1] at hJs
 let m:=multiplicity P.F J
 have hn:=_Q15 J
 have horder:1≤order J:=Nat.succ_le_of_lt (hm.trans_le hms)
 have hadm:PA.Admissible m (point J):=
   ⟨hms,horder,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
 have hx:Contains (ABK.root m) (point J):=by
   dsimp only [Contains,ABK.root,point]
   refine ⟨max_le horder hms,hJs,?_,hJb,Nat.zero_le _,hJu,Nat.zero_le _,hJt⟩
   have hh:=hn.2.2.1
   omega
 obtain ⟨a,hvalid,ha⟩:=hcov m hm (hms.trans hJs) (point J) hadm hx
 exact BW.BLH nodes hI P hFT hLow hcap hid J hJ horder a ha rfl hJne hJroot hvalid

theorem packet_count (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) 4000 58 13) (hFT:3681≤wt AT P.F):
 P.seeds.card≤271000000000000000:=by
 classical
 letI:Fact (Irreducible P.F):=⟨P.irreducible⟩
 rcases VT MJ.p0 MJ.shape0 97989970 (by decide)
     MJ.dimension0 nodes P.u0 P.u1 hI P.F P.irreducible (by change 354<_;omega)
     13 58 4000 (by decide) (by decide) (by decide) ⟨P.r_weight,P.y_weight,P.total_weight⟩
     with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · exact (KY.helper_count MJ.p0 nodes P
     (by decide) (by decide) (by decide) (by decide) Q hQ).le.trans (by decide)
 exact from_sources (by decide) nodes hI P hFT S hS (by decide) (by decide+kernel) ABK.covered

end
end AXH

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace QE
open FF ZGL
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

def p0:Parameters:=⟨38,354,16,7,52,0,1⟩
theorem shape0:Shape p0:=by constructor<;>decide+kernel
theorem middle0 (h:ℕ) (hh:h≤7):52≤(p0.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem CPO:AM.AW p0.cutoff 131071 354 16 7 52=3564497745234:=by decide+kernel
theorem rank0:AR.rankBound 38 354 16 7 52=13597106:=by decide+kernel
theorem dimension0:Dimension p0 97989970:=by
 exact AZ p0 97989970 3564497745234 13597106 (by decide) (by decide) (by decide) (by decide) (by decide) middle0 CPO rank0 (by decide)

def p1:Parameters:=⟨38,531,16,7,52,0,1⟩
theorem shape1:Shape p1:=by constructor<;>decide+kernel
theorem middle1 (h:ℕ) (hh:h≤7):52≤(p1.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem COM:AM.AW p1.cutoff 131071 531 16 7 52=5459830538994:=by decide+kernel
theorem rank1:AR.rankBound 38 531 16 7 52=20748437:=by decide+kernel
theorem dimension1:Dimension p1 20752270066:=by
 exact AZ p1 20752270066 5459830538994 20748437 (by decide) (by decide) (by decide) (by decide) (by decide) middle1 COM rank1 (by decide)

def p2:Parameters:=⟨38,708,16,7,52,0,1⟩
theorem shape2:Shape p2:=by constructor<;>decide+kernel
theorem middle2 (h:ℕ) (hh:h≤7):52≤(p2.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem CNU:AM.AW p2.cutoff 131071 708 16 7 52=7355163332754:=by decide+kernel
theorem rank2:AR.rankBound 38 708 16 7 52=27899768:=by decide+kernel
theorem dimension2:Dimension p2 41406550162:=by
 exact AZ p2 41406550162 7355163332754 27899768 (by decide) (by decide) (by decide) (by decide) (by decide) middle2 CNU rank2 (by decide)

def p3:Parameters:=⟨38,1062,16,7,52,0,1⟩
theorem shape3:Shape p3:=by constructor<;>decide+kernel
theorem middle3 (h:ℕ) (hh:h≤7):52≤(p3.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem CNC:AM.AW p3.cutoff 131071 1062 16 7 52=11145828920274:=by decide+kernel
theorem rank3:AR.rankBound 38 1062 16 7 52=42202430:=by decide+kernel
theorem dimension3:Dimension p3 82715110354:=by
 exact AZ p3 82715110354 11145828920274 42202430 (by decide) (by decide) (by decide) (by decide) (by decide) middle3 CNC rank3 (by decide)

def p4:Parameters:=⟨38,1770,16,7,52,0,1⟩
theorem shape4:Shape p4:=by constructor<;>decide+kernel
theorem middle4 (h:ℕ) (hh:h≤7):52≤(p4.cutoff h+16-1)/131071:=by interval_cases h<;>decide+kernel
theorem COY:AM.AW p4.cutoff 131071 1770 16 7 52=18727160095314:=by decide+kernel
theorem rank4:AR.rankBound 38 1770 16 7 52=70807754:=by decide+kernel
theorem dimension4:Dimension p4 165332230738:=by
 exact AZ p4 165332230738 18727160095314 70807754 (by decide) (by decide) (by decide) (by decide) (by decide) middle4 COY rank4 (by decide)

def p5:Parameters:=⟨36,375,15,7,49,0,1⟩
theorem shape5:Shape p5:=by constructor<;>decide+kernel
theorem middle5 (h:ℕ) (hh:h≤7):49≤(p5.cutoff h+15-1)/131071:=by interval_cases h<;>decide+kernel
theorem CPF:AM.AW p5.cutoff 131071 375 15 7 49=3086119086726:=by decide+kernel
theorem rank5:AR.rankBound 36 375 15 7 49=11772598:=by decide+kernel
theorem dimension5:Dimension p5 3156614:=by
 exact AZ p5 3156614 3086119086726 11772598 (by decide) (by decide) (by decide) (by decide) (by decide) middle5 CPF rank5 (by decide)

def p6:Parameters:=⟨34,419,14,6,46,0,1⟩
theorem shape6:Shape p6:=by constructor<;>decide+kernel
theorem middle6 (h:ℕ) (hh:h≤6):46≤(p6.cutoff h+14-1)/131071:=by interval_cases h<;>decide+kernel
theorem CMZ:AM.AW p6.cutoff 131071 419 14 6 46=2730093701510:=by decide+kernel
theorem rank6:AR.rankBound 34 419 14 6 46=10414269:=by decide+kernel
theorem dimension6:Dimension p6 55568774:=by
 exact AZ p6 55568774 2730093701510 10414269 (by decide) (by decide) (by decide) (by decide) (by decide) middle6 CMZ rank6 (by decide)

def p7:Parameters:=⟨30,586,12,6,41,0,1⟩
theorem shape7:Shape p7:=by constructor<;>decide+kernel
theorem middle7 (h:ℕ) (hh:h≤6):41≤(p7.cutoff h+12-1)/131071:=by interval_cases h<;>decide+kernel
theorem CMX:AM.AW p7.cutoff 131071 586 12 6 41=2383595175192:=by decide+kernel
theorem rank7:AR.rankBound 30 586 12 6 41=9092636:=by decide+kernel
theorem dimension7:Dimension p7 15203608:=by
 exact AZ p7 15203608 2383595175192 9092636 (by decide) (by decide) (by decide) (by decide) (by decide) middle7 CMX rank7 (by decide)

def p8:Parameters:=⟨40,339,17,8,55,0,1⟩
theorem shape8:Shape p8:=by constructor<;>decide+kernel
theorem middle8 (h:ℕ) (hh:h≤8):55≤(p8.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem COE:AM.AW p8.cutoff 131071 339 17 8 55=4207825676994:=by decide+kernel
theorem rank8:AR.rankBound 40 339 17 8 55=16050976:=by decide+kernel
theorem dimension8:Dimension p8 158624450:=by
 exact AZ p8 158624450 4207825676994 16050976 (by decide) (by decide) (by decide) (by decide) (by decide) middle8 COE rank8 (by decide)

def p9:Parameters:=⟨40,508,17,8,55,0,1⟩
theorem shape9:Shape p9:=by constructor<;>decide+kernel
theorem middle9 (h:ℕ) (hh:h≤8):55≤(p9.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem COS:AM.AW p9.cutoff 131071 508 17 8 55=6453629857809:=by decide+kernel
theorem rank9:AR.rankBound 40 508 17 8 55=24515172:=by decide+kernel
theorem dimension9:Dimension p9 27124609041:=by
 exact AZ p9 27124609041 6453629857809 24515172 (by decide) (by decide) (by decide) (by decide) (by decide) middle9 COS rank9 (by decide)

def p10:Parameters:=⟨40,1017,17,8,55,0,1⟩
theorem shape10:Shape p10:=by constructor<;>decide+kernel
theorem middle10 (h:ℕ) (hh:h≤8):55≤(p10.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BVI:AM.AW p10.cutoff 131071 1017 17 8 55=13217619964524:=by decide+kernel
theorem rank10:AR.rankBound 40 1017 17 8 55=50007928:=by decide+kernel
theorem dimension10:Dimension p10 108341686892:=by
 exact AZ p10 108341686892 13217619964524 50007928 (by decide) (by decide) (by decide) (by decide) (by decide) middle10 BVI rank10 (by decide)

def p11:Parameters:=⟨40,1695,17,8,55,0,1⟩
theorem shape11:Shape p11:=by constructor<;>decide+kernel
theorem middle11 (h:ℕ) (hh:h≤8):55≤(p11.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BTL:AM.AW p11.cutoff 131071 1695 17 8 55=22227414252054:=by decide+kernel
theorem rank11:AR.rankBound 40 1695 17 8 55=83964880:=by decide+kernel
theorem dimension11:Dimension p11 216524749334:=by
 exact AZ p11 216524749334 22227414252054 83964880 (by decide) (by decide) (by decide) (by decide) (by decide) middle11 BTL rank11 (by decide)

def p12:Parameters:=⟨40,2712,17,8,55,0,1⟩
theorem shape12:Shape p12:=by constructor<;>decide+kernel
theorem middle12 (h:ℕ) (hh:h≤8):55≤(p12.cutoff h+17-1)/131071:=by interval_cases h<;>decide+kernel
theorem BSP:AM.AW p12.cutoff 131071 2712 17 8 55=35742105683349:=by decide+kernel
theorem rank12:AR.rankBound 40 2712 17 8 55=134900308:=by decide+kernel
theorem dimension12:Dimension p12 378799342997:=by
 exact AZ p12 378799342997 35742105683349 134900308 (by decide) (by decide) (by decide) (by decide) (by decide) middle12 BSP rank12 (by decide)

def p13:Parameters:=⟨45,319,20,9,62,0,1⟩
theorem shape13:Shape p13:=by constructor<;>decide+kernel
theorem middle13 (h:ℕ) (hh:h≤9):62≤(p13.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem BYL:AM.AW p13.cutoff 131071 319 20 9 62=6460774887929:=by decide+kernel
theorem rank13:AR.rankBound 45 319 20 9 62=24645458:=by decide+kernel
theorem dimension13:Dimension p13 115945977:=by
 exact AZ p13 115945977 6460774887929 24645458 (by decide) (by decide) (by decide) (by decide) (by decide) middle13 BYL rank13 (by decide)

def p14:Parameters:=⟨45,478,20,9,62,0,1⟩
theorem shape14:Shape p14:=by constructor<;>decide+kernel
theorem middle14 (h:ℕ) (hh:h≤9):62≤(p14.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem BUT:AM.AW p14.cutoff 131071 478 20 9 62=9961655618924:=by decide+kernel
theorem rank14:AR.rankBound 45 478 20 9 62=37810817:=by decide+kernel
theorem dimension14:Dimension p14 49776807276:=by
 exact AZ p14 49776807276 9961655618924 37810817 (by decide) (by decide) (by decide) (by decide) (by decide) middle14 BUT rank14 (by decide)

def p15:Parameters:=⟨45,638,20,9,62,0,1⟩
theorem shape15:Shape p15:=by constructor<;>decide+kernel
theorem middle15 (h:ℕ) (hh:h≤9):62≤(p15.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem BZD:AM.AW p15.cutoff 131071 638 20 9 62=13484554467724:=by decide+kernel
theorem rank15:AR.rankBound 45 638 20 9 62=51058977:=by decide+kernel
theorem dimension15:Dimension p15 99750001036:=by
 exact AZ p15 99750001036 13484554467724 51058977 (by decide) (by decide) (by decide) (by decide) (by decide) middle15 BZD rank15 (by decide)

def p16:Parameters:=⟨45,957,20,9,62,0,1⟩
theorem shape16:Shape p16:=by constructor<;>decide+kernel
theorem middle16 (h:ℕ) (hh:h≤9):62≤(p16.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem DKR:AM.AW p16.cutoff 131071 957 20 9 62=20508334047519:=by decide+kernel
theorem rank16:AR.rankBound 45 957 20 9 62=77472496:=by decide+kernel
theorem dimension16:Dimension p16 199384056095:=by
 exact AZ p16 199384056095 20508334047519 77472496 (by decide) (by decide) (by decide) (by decide) (by decide) middle16 DKR rank16 (by decide)

def p17:Parameters:=⟨45,1595,20,9,62,0,1⟩
theorem shape17:Shape p17:=by constructor<;>decide+kernel
theorem middle17 (h:ℕ) (hh:h≤9):62≤(p17.cutoff h+20-1)/131071:=by interval_cases h<;>decide+kernel
theorem DIR:AM.AW p17.cutoff 131071 1595 20 9 62=34555893207109:=by decide+kernel
theorem rank17:AR.rankBound 45 1595 20 9 62=130299534:=by decide+kernel
theorem dimension17:Dimension p17 398652166213:=by
 exact AZ p17 398652166213 34555893207109 130299534 (by decide) (by decide) (by decide) (by decide) (by decide) middle17 DIR rank17 (by decide)

def p18:Parameters:=⟨51,400,23,11,70,0,1⟩
theorem shape18:Shape p18:=by constructor<;>decide+kernel
theorem middle18 (h:ℕ) (hh:h≤11):70≤(p18.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem DIW:AM.AW p18.cutoff 131071 400 23 11 70=13525111441855:=by decide+kernel
theorem rank18:AR.rankBound 51 400 23 11 70=51397405:=by decide+kernel
theorem dimension18:Dimension p18 51590105535:=by
 exact AZ p18 51590105535 13525111441855 51397405 (by decide) (by decide) (by decide) (by decide) (by decide) middle18 DIW rank18 (by decide)

def p19:Parameters:=⟨51,471,23,11,70,0,1⟩
theorem shape19:Shape p19:=by constructor<;>decide+kernel
theorem middle19 (h:ℕ) (hh:h≤11):70≤(p19.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem DJR:AM.AW p19.cutoff 131071 471 23 11 70=16115332865619:=by decide+kernel
theorem rank19:AR.rankBound 51 471 23 11 70=61115885:=by decide+kernel
theorem dimension19:Dimension p19 94170308179:=by
 exact AZ p19 94170308179 16115332865619 61115885 (by decide) (by decide) (by decide) (by decide) (by decide) middle19 DJR rank19 (by decide)

def p20:Parameters:=⟨51,600,23,11,70,0,1⟩
theorem shape20:Shape p20:=by constructor<;>decide+kernel
theorem middle20 (h:ℕ) (hh:h≤11):70≤(p20.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem DLE:AM.AW p20.cutoff 131071 600 23 11 70=20821509818655:=by decide+kernel
theorem rank20:AR.rankBound 51 600 23 11 70=78773405:=by decide+kernel
theorem dimension20:Dimension p20 171534338335:=by
 exact AZ p20 171534338335 20821509818655 78773405 (by decide) (by decide) (by decide) (by decide) (by decide) middle20 DLE rank20 (by decide)

def p21:Parameters:=⟨51,942,23,11,70,0,1⟩
theorem shape21:Shape p21:=by constructor<;>decide+kernel
theorem middle21 (h:ℕ) (hh:h≤11):70≤(p21.cutoff h+23-1)/131071:=by interval_cases h<;>decide+kernel
theorem ETF:AM.AW p21.cutoff 131071 942 23 11 70=33298351042983:=by decide+kernel
theorem rank21:AR.rankBound 51 942 23 11 70=125586365:=by decide+kernel
theorem dimension21:Dimension p21 376638976423:=by
 exact AZ p21 376638976423 33298351042983 125586365 (by decide) (by decide) (by decide) (by decide) (by decide) middle21 ETF rank21 (by decide)
def profile:Fin 22→Parameters:= ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,p14,p15,p16,p17,p18,p19,p20,p21]
def kernel:Fin 22→ℕ:= ![97989970,20752270066,41406550162,82715110354,165332230738,3156614,55568774,15203608,158624450,27124609041,108341686892,216524749334,378799342997,115945977,49776807276,99750001036,199384056095,398652166213,51590105535,94170308179,171534338335,376638976423]
theorem shape (i:Fin 22):Shape (profile i):=by
 fin_cases i
 · exact shape0
 · exact shape1
 · exact shape2
 · exact shape3
 · exact shape4
 · exact shape5
 · exact shape6
 · exact shape7
 · exact shape8
 · exact shape9
 · exact shape10
 · exact shape11
 · exact shape12
 · exact shape13
 · exact shape14
 · exact shape15
 · exact shape16
 · exact shape17
 · exact shape18
 · exact shape19
 · exact shape20
 · exact shape21
theorem dimension (i:Fin 22):Dimension (profile i) (kernel i):=by
 fin_cases i
 · exact dimension0
 · exact dimension1
 · exact dimension2
 · exact dimension3
 · exact dimension4
 · exact dimension5
 · exact dimension6
 · exact dimension7
 · exact dimension8
 · exact dimension9
 · exact dimension10
 · exact dimension11
 · exact dimension12
 · exact dimension13
 · exact dimension14
 · exact dimension15
 · exact dimension16
 · exact dimension17
 · exact dimension18
 · exact dimension19
 · exact dimension20
 · exact dimension21
theorem small (i:Fin 22):(profile i).B≤256∧(profile i).U≤512∧(profile i).L≤4096∧(profile i).s≤64:=by fin_cases i<;>decide
end QE

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AED
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF
open HI LV BH DR
open FF ZGL QE
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
instance (p:DA.SourceCaps) (a:DA.OwnerBox):
 Decidable (DA.Impossible p a):=by unfold DA.Impossible;infer_instance

def pricing (fixed:Degrees) (a:DR.Box) (m:ℕ) (useOwner:Bool):=if useOwner then ownerZ a m else fixed

def BandValid (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 22) (useOwner:Bool) (N:ℕ):Prop:=
 let p:=profile i
 let z:=pricing fixed a m useOwner
 0<m∧m≤a.slo∧2*a.slo≤a.bhi∧
 a.shi≤64∧a.bhi≤256∧a.uhi≤512∧a.thi≤4096∧a.thi<low∧p.L<low∧
 SN.Common z low t y r∧MG t y r≤cap∧
 DA.Impossible (caps p) {powerBox p a m with q:=N}∧
 (∑ e∈Finset.range N,ZZ.bandCount (caps p) (powerBox p a m) m e)<kernel i∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitZFlag<2130706433∧
 flagMixed (ownerFlag a) (flag p.B p.U p.L p.s) unitYZFlag<2130706433∧
 pairCost z 1 (ownerFlag a) (flag p.B p.U p.L p.s) t y r+leading z t y r≤cap
instance (fixed:Degrees) (a:DR.Box) (m low t y r cap:ℕ)
 (i:Fin 22) (useOwner:Bool) (N:ℕ):Decidable (BandValid fixed a m low t y r cap i useOwner N):=by
 unfold BandValid SN.Common Gates;infer_instance



variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem CPT {t y r low cap m:ℕ}
 (nodes:I ↪ K) (hN:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (SZ:Source P.F) (fixed:Degrees) (hFixed:Fits SZ fixed)
 (hFT:low≤wt AT P.F) (hcap:4000000000000000≤cap)
 (J:DX.Poly (K:=K)) (hJ:Irreducible J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (i:Fin 22) (useOwner:Bool) (N:ℕ) (hc:BandValid fixed a m low t y r cap i useOwner N):
 P.seeds.card≤cap:=by
 classical
 obtain ⟨hm,hms,h2,hs,hb,hu,ht,haf,hpf,hcommon,hid,hstop,hband,hz,huy,hgeo⟩:=hc
 have hsmall:AMK.Small J:=by
   refine ⟨ha.2.1.trans hs,?_⟩
   intro d hd
   have hB:=(le_weightedTotalDegree slopeWeights hd).trans (ha.2.2.2.1.trans hb)
   have hU:=(le_weightedTotalDegree HA hd).trans (ha.2.2.2.2.2.1.trans hu)
   have hT:=(le_weightedTotalDegree totalWeights hd).trans (ha.2.2.2.2.2.2.2.trans ht)
   simp only [JW,slopeWeights,HA,totalWeights] at hB hU hT
   norm_num at hB hU hT
   exact ⟨by omega,by omega,by omega⟩
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hpower:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS J).map (carrierMap P.F):=
   (Polynomial.le_rootMultiplicity_iff hJne).mp (by rw [hroot];omega)
 obtain ⟨SJ,hSJ,hSJd⟩:=ZD.UN P.F a.thi
   (haf.trans_le hFT) P.rdegree hchar J hJ.ne_zero ha.2.2.2.2.2.2.2 1 (by decide) hpower
 have hpricing: ∃S:Source P.F,Fits S (pricing fixed a m useOwner):=by
   cases useOwner with
   | false=>exact ⟨SZ,hFixed⟩
   | true=>exact owner_source P J a m hm ha hms h2 hroot
 obtain ⟨S,hS⟩:=hpricing
 have hpSmall:=QE.small i
 exact XU.packet_count nodes hN P (profile i) (shape i) (kernel i) (dimension i)
   hpSmall (hpf.trans_le hFT) J hJ a ha m (hms.trans ha.1) hsmall hJne hroot SJ S hSJ hSJd
   (pricing fixed a m useOwner) hS (hcommon.1.trans_le hFT) hcommon.2.1 hcommon.2.2
   cap hcap hid ⟨hz,huy,hgeo⟩ N hstop hband


def linearU (a:DR.Box):=max a.bhi a.uhi
def linearT (a:DR.Box):=max (linearU a) a.thi
def LinearValid (a:DR.Box) (low t y r cap:ℕ):Prop:=
 a.shi≤1∧2≤a.bhi∧linearT a<low∧
 AYU.LinearChecks a.bhi (linearU a) (linearT a) t y r cap
instance (a:DR.Box) (low t y r cap:ℕ):Decidable (LinearValid a low t y r cap):=by unfold LinearValid;infer_instance

theorem CUP {t y r low cap:ℕ} {x:I→K}
 (P:Packet x t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt AT P.F) (hid:MG t y r≤cap)
 (J:DX.Poly (K:=K)) (hJ:J≠0) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
 (hc:LinearValid a low t y r cap):P.seeds.card≤cap:=by
 obtain ⟨hs,hB,hL,hchecks⟩:=hc
 have hS:J.degreeOf 1=1:=by have hh:=ha.2.1;change order J≤a.shi at hh;change order J=1;omega
 have hshape: ∀e∈J.support,2*e 1+e 3≤a.bhi∧e 1+e 2+e 3≤linearU a∧e 1+e 2+e 3+e 4≤linearT a:=by
   intro e he
   have hb:=(le_weightedTotalDegree slopeWeights he).trans ha.2.2.2.1
   have hu:Finsupp.weight HA e≤linearU a:=(le_weightedTotalDegree HA he).trans (ha.2.2.2.2.2.1.trans (le_max_right a.bhi a.uhi))
   have ht:Finsupp.weight totalWeights e≤linearT a:=(le_weightedTotalDegree totalWeights he).trans (ha.2.2.2.2.2.2.2.trans (le_max_right (linearU a) a.thi))
   simp only [JW,slopeWeights,HA,totalWeights] at hb hu ht
   norm_num at hb hu ht
   exact ⟨by omega,by omega,by omega⟩
 have hh:=AOR.BNL P J hJ hS a.bhi (linearU a) (linearT a)
   hB (le_max_left _ _) (le_max_left _ _) hshape (hL.trans_le hFT) hroot hchecks.1 hchecks.2.1
 exact hh.trans (max_le hid hchecks.2.2)

end
end AED

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace OZ
open MvPolynomial CW DJ
open BX DP DC
open BD DU EF
open CB HI DR LV
open AED ADB
open RCN095 RCN234 RCN156
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def fallback:Fin 321:=⟨310,by decide⟩
def Valid (m low t y r cap:ℕ) (a:DR.Box):Prop:=
 BH.check .native (degrees fallback) a m low t y r cap=true∨
 LinearValid a low t y r cap∨
 ∃(i:Fin 22) (useOwner:Bool) (j:Fin 321) (N:ℕ),
   (CN.profile j).L<low∧
   BandValid (degrees j) a m low t y r cap i useOwner N

variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem BLH {m low t y r cap:ℕ}
 (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r) [Fact (Irreducible P.F)]
 (hFT:low≤wt AT P.F) (hLow:2985<low)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (J:DX.Poly (K:=K)) (hJ:Irreducible J) (horder:1≤order J)
 (a:DR.Box) (ha:Contains a (point J))
 (hroot:((asS J).map (carrierMap P.F)).rootMultiplicity (ratio (carrierMap P.F) P.F)=m)
 (hJne:(asS J).map (carrierMap P.F)≠0)
 (hJroot:((asS J).map (carrierMap P.F)).eval (ratio (carrierMap P.F) P.F)=0)
 (hc:Valid m low t y r cap a):P.seeds.card≤cap:=by
 rcases hc with hc | hc | ⟨i,useOwner,j,N,hL,hc⟩
 · have hL:(CN.profile fallback).L<low:=by
     have hh:(CN.profile fallback).L=2436:=by decide+kernel
     omega
   rcases AGF fallback nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact (BH.BLQ nodes hI P SZ (degrees fallback) hZ .native a m low cap
     hFT (by omega) (by omega) J hJ ha hroot hJne hc).trans (max_le hid le_rfl)
 · exact CUP P hFT hid J hJ.ne_zero horder a ha hJroot hc
 · rcases AGF j nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
   · exact hs.le.trans (by omega)
   exact CPT nodes hI P SZ (degrees j) hZ hFT hcap J hJ a ha hroot hJne i useOwner N hc
end
end OZ

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ADD
open DR (Box Contains lower upper)
open HI PA AED ADB
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
abbrev valid (m:ℕ):=OZ.Valid m 3681 4000 57 13 267000000000000000

set_option autoImplicit false
open CP

def receiptBox (code:ℕ):Box:=
 let x:=code/8589934592
 ⟨x%4096,x/4096%4096,x/4096^2%4096,x/4096^3%4096,
  x/4096^4%4096,x/4096^5%4096,x/4096^6%4096,x/4096^7%4096⟩
def receiptTest (m code:ℕ):Bool:=
 let a:=receiptBox code
 if code%4=0 then BH.check .native (degrees OZ.fallback) a m 3681 4000 57 13 267000000000000000
 else if code%4=1 then decide (LinearValid a 3681 4000 57 13 267000000000000000)
 else if h:code/4%32<22∧code/256%512<321 then
  decide ((CN.profile ⟨code/256%512,h.2⟩).L<3681∧
   BandValid (degrees ⟨code/256%512,h.2⟩) a m 3681 4000 57 13 267000000000000000
     ⟨code/4%32,h.1⟩ (code/128%2=1) (code/131072%65536))
 else false

theorem receipt_sound (m code:ℕ) (h:receiptTest m code=true):valid m (receiptBox code):=by
 unfold receiptTest at h
 split_ifs at h with h0 h1 h2
 · exact Or.inl h
 · exact Or.inr (Or.inl (of_decide_eq_true h))
 · have hh:=of_decide_eq_true h
   exact Or.inr (Or.inr ⟨⟨code/4%32,h2.1⟩,decide (code/128%2=1),⟨code/256%512,h2.2⟩,code/131072%65536,hh.1,hh.2⟩)

def decodeReceipts:ℕ→ℕ→List ℕ
 | 0,_=>[]
 | n+1,c=>c%2^132::decodeReceipts n (c/2^132)
def d1_0:List ℕ:=decodeReceipts 16 0x1800e01800e01200c00800600000000001800e01800e01200c004004000736b2001800e01800e01200c00200200000001001800e01800e00a00400400200000000001800e00c00801801000c00800000000001800e00c00801200c00600600000000001800e00c00801000c00400400000000001800e00c00a00e00c00200200000000001800e00c00800a00400400200000000001800e00600200c00400600200000000000c00800c00801801000c00800000000000c00800c00801200c00600600000000000c00800c00801000c00400400000000000c00a00c00a00e00c00200200000000000c00800c00800a00400400200000000000c00200600200c00400600200000000
theorem hd1_0:d1_0.all (receiptTest 1)=true:=by decide+kernel
def d1_1:List ℕ:=decodeReceipts 16 0x2e01a02e01a01200c00200200000001002e01a02e01a00a00800400400000000002e01a02e01a00a00800200200000001002e01a02e01a00600400200200000000002e01a01800e02001400e00200053606002e01a01800e01200c00800600000000002e01a01800e01200c004004000736b2002e01a01800e01200c00200200000001002e01a01800e00a00400400200000000002e01a00c00801801000c00800000000002e01a00c00801200c00600600000000002e01a00c00801000c00400400000000002e01a00c00a00e00c00200200000000002e01a00c00800a00400400200000000002e01a00600200c00400600200000000001800e01800e02001400e00200053606
theorem hd1_1:d1_1.all (receiptTest 1)=true:=by decide+kernel
def d1_2:List ℕ:=decodeReceipts 16 0x5a03002e01a00a00800200200000001005a03002e01a00600400200200000000005a03001800e02001400e00200053606005a03001800e01200c00800600000000005a03001800e01200c004004000736b2005a03001800e01200c00200200000001005a03001800e00a00400400200000000005a03000c00801801000c00800000000005a03000c00801200c00600600000000005a03000c00801000c00400400000000005a03000c00a00e00c00200200000000005a03000c00800a00400400200000000005a03000600200c00400600200000000002e01a02e01a02001400e00200053606002e01a02e01a01200c00800600073692002e01a02e01a01200c004004000936c6
theorem hd1_2:d1_2.all (receiptTest 1)=true:=by decide+kernel
def d1_3:List ℕ:=decodeReceipts 16 0x8605c02801c00a0080040040000000000b205c03401c00a0080020020000000100b205c03401c0060040020020000000100b205c01a01002001400e0020005360600b205c01a01001200c008002000736ae00b205c01a01000a0040040020000000000b205c00e00a01c01400e00a0000000000b205c00e00a01600e00800200073a0e00b205c00e00a00c0040060020000000000b205c00800601000c0080060000000000b205c00800200c00400400200000000005a03005a03002001400e00200053a06005a03005a03001200400800200073f56005a03002e01a02001400e00200053606005a03002e01a01200c00800200073a2a005a03002e01a00a00800400400000000
theorem hd1_3:d1_3.all (receiptTest 1)=true:=by decide+kernel
def d1_4:List ℕ:=decodeReceipts 16 0x1620b403401c00a0080020020000000101620b403401c0060040020020000000101620b401a01002001400e00200053a0601620b401a01001200c008002000736ae01620b401a01000a0040040020000000001620b400e00a01c01400e00a0000000001620b400e00a01600e00800200073a0e01620b400e00a00c0040060020000000001620b400800601000c0080060000000001620b400800200c0040040020000000000b205c06803602000400e00200073f5200b205c03401c02001400e00200053a0600b205c03401c01200c00800200073a0e00b208803402a00a00800400400073a0e00b208802801c00a00800400400000000008605c03402a00a00800400400073a0e
theorem hd1_4:d1_4.all (receiptTest 1)=true:=by decide+kernel
def d1_5:List ℕ:=decodeReceipts 16 0x2c416401a01000a0040040020000000002c416400e00a01c01400e00a00053a0602c416400e00a01600e00800200073a0a02c416400e00a00c0040060020000000002c416400800601000c0080060000000002c416400800200c0040040020000000001620b406803602001400e00200053e0601620b406803601200400800200053f0a01620b403401c02001400e00200053a0601620b403401c01200c0080060007368e01620b403401c01200c0040040007368e01620b403401c01200c00200200000001016210c03402a00a00800400400073a0e016210c02801c00a00800400400000000010a0b403402a00a00800400400073a0e010a0b402801c00a00800400400000000
theorem hd1_5:d1_5.all (receiptTest 1)=true:=by decide+kernel
def d1_6:List ℕ:=decodeReceipts 16 0x2c421603402a01a01400800600053f0602c421602801c02001c00800600033a1e02c421602801c01a01400800600053a06021416403401c02001400800600053a0602c421603402a02001c00400400033f1e02c421603402a01a01400400400053e0602c421602801c02001c00400400033a1e02c421602801c01a01400400400053a06021416403401c02001400400400053a0602c416403401c0200140020020000000102c416403401c01200c00800200073a3a02c416403401c00a00800400200073a4e02c416403401c0060040020020000000102c416401a01002001400e00a0005368602c416401a01002001400800200053e0602c416401a01001200c008002000736aa
theorem hd1_6:d1_6.all (receiptTest 1)=true:=by decide+kernel
def d1_7:List ℕ:=decodeReceipts 16 0x21416406803601200c00800600053a0602c426e06805001201000400400053a36026c21606805001201000400400053e0602c421606805000e00c00400400053f0602c421604e03601200c00400400053a06021416406803601200c00400400053a0602c416406803601200c0020020000000102c416406803600a00400400200053a0602c421603402a02001c00e00a0003369e02c421603402a01a01400c00a0005368602c421602801c02001400e00a00053686021416403401c02001400e00a00053a0602c426e03402a02001c00800800053a22026c21603402a02001c00800800053f0602c426e03402a02001c00600600053a22026c21603402a02001c00600600053e06
theorem hd1_7:d1_7.all (receiptTest 1)=true:=by decide+kernel
def d1_8:List ℕ:=decodeReceipts 16 0x2c421604203602001c0020020000000102c421604e03601a0140020020000000102141be06805e02001c00200200033a1a02141ea05c05802001c00200200053a1a02141ea05605002001c00200200053f4a01e81be05c05002001c00200200053e2601bc16406805002001c00200200053e26021416406805001a01400200200053f06021416404e03602001400200200053e0602c426e06805001201000800800053a36026c21606805001201000800800053f0602c426e06805001201000600600053a36026c21606805001201000600600053e0602c426e06805000e00c00600600053a36026c21606805000e00c00600600053a0602c421604e03601200c00800600053e06
theorem hd1_8:d1_8.all (receiptTest 1)=true:=by decide+kernel
def d1_9:List ℕ:=decodeReceipts 16 0x2c426e06805001a01400200200053a36026c21606805e01a01800200200033a1a026c24205c05801a01800200200053a1a026c24205605001a01a00200200033e1e026c24205605001801800200200000001024021605c05001a01800200200053f06026c21606805e01601400200200033a1a026c21605c0500160140020020000000102c426e04e04402001c00200200053a22026c24204e04a02002000200200053a02026c25804e04a01e01c00200200053a22025624204e04a01e01c00200200033e1e026c24204804402001c00200200000001024021604e04a02002000200200053a02024021604e04a01e01c00200200053f06024021604804402001c00200200000001
theorem hd1_9:d1_9.all (receiptTest 1)=true:=by decide+kernel
def _GAM:List ℕ:=decodeReceipts 16 0x24021604e04a01e01c00400400033e1e024021604804402001c00400400033e1e02c426e04203602001c00400400053a22026c21604203602001c00400400033f1e02c426e04e04401a01400400400053a36026c21604e04401a01400400400053e0602c426e04203601a01400400400053a36026c21604203601a01400400400053a0602141be06805e02001c00400400033a1a02141ea05c05802001c00400400053a1a02141ea05605002001c00400400053f4a01e81be05c05002001c00400400053f2601bc16406805002001c00400400053f26021416406805001a01400400400053e4a021416404e03602001400400400053f0602c421606805002001c00200200053e1a
theorem hd1_10:_GAM.all (receiptTest 1)=true:=by decide+kernel
def _GAX:List ℕ:=decodeReceipts 16 0x2c426e06805001a01400400400053e36026c21606805e01a01800400400033a1a026c24205c05801a01800400400053a1a026c24205605001a01a00400400033e1e026c24205605001801800400400053f06024021605c05801a01800400400033e1e024021605605001a01800400400053e06026c21606805e01601400400400033a1a026c21605c05001601400400400053e0602c426e04e04402001c00400400053a22026c24204e04a02002000400400053a02026c25804e04a01e01c00400400053a22025624204e04a01e01c00400400033f1e026c24204804402002000400400053a02026c24204804401e01c00400400033e1e024021604e04a02002000400400053a02
theorem hd1_11:_GAX.all (receiptTest 1)=true:=by decide+kernel
def _GBF:List ℕ:=decodeReceipts 16 0x2c426e04203601a01400600600053a36026c21604203601a01400600600053a0602141be06805e02001c00800800033a1a02141ea05c05802001c00800800053a1a02141ea05605002002000800800053a0202141ea05605001e01c00800800053f4a01e81be05c05002001c00800800053e4a02141be06805e02001c00600600033a1a02141ea05c05802001c00600600053a1a02141ea05605002002000600600053a0202141ea05605001e01c00600600033f1e01e81be05c05002001c00600600053a4a01bc16406805002001c00800600053a4a021416406805001a01400800600053f4a021416404e03602001400800600073f4a02c421606805002001c00400400053e1a
theorem hd1_12:_GBF.all (receiptTest 1)=true:=by decide+kernel
def _GBG:List ℕ:=decodeReceipts 16 0x26c21603c03602001c00800800033e1e02c426e04203602001c00600600053a22026c24204203e02002000600600053a02026c24204203e01e01c00600600033e1e024021604203e02001c00600600033e1e026c21603c03602001c00600600033e1e02c426e04e04401a01400800800053a36026c24204e04a01a01a00800800033a1e026c24204e04a01801800800800053e06026c24204804401a01800800800053e06024021604e04401a01800800800053e06026c21604e04401601400800800053a0602c426e04e04401a01400600600053a36026c21604e04401a01400600600053f0602c426e04203601a01400800800053a36026c21604203601a01400800800053a06
theorem hd1_13:_GBG.all (receiptTest 1)=true:=by decide+kernel
def _GBH:List ℕ:=decodeReceipts 16 0x24021604804402002000800800053a02024021604804401e01c00800800033e1e02c426e04e04402001c00600600053a22026c24204e04a02002000600600053a02026c25804e04a01e01c00600600053a22025624204e04a01e01e00600600053a02025624204e04a01c01c00600600033e1e026c24204804402002000600600053a02026c24204804401e01c00600600033f1e024021604e04a02002000600600053a02024021604e04a01e01c00600600033e1e024021604804402001c00600600033f1e02c426e04203602001c00800800053a22026c24204203e02002000800800053a02026c24204203e01e01c00800800033e1e024021604203e02001c00800800033e1e
theorem hd1_14:_GBH.all (receiptTest 1)=true:=by decide+kernel
def _GBI:List ℕ:=decodeReceipts 16 0x26c24205205001801800600600053e06024021605c05801a01800600600033e1e024021605605001a01800600600053e06026c21606805e01601400600600033a1a026c21605c05001601400600600053f0602c426e04e04402001c00800800053a22026c24204e04a02002000800800053a02026c25804e04a01e01c00800800053a22025624204e04a01e01e00800800053a02025624204e04a01c01c00800800033e1e026c24204804402002000800800053a02026c25804804401e01e00800800053a02026c25804804401c01c00800800033e1e025624204804401e01c00800800033e1e024021604e04a02002000800800053a02024021604e04a01e01c00800800033f1e
theorem hd1_15:_GBI.all (receiptTest 1)=true:=by decide+kernel
def _GBJ:List ℕ:=decodeReceipts 16 0x26c25805605401a01a00800800053a1a025624205605401a01a00800800033e1e026c24205205001a01a00800800033e1e026c24205605401801800800800033e1e026c24205205001801800800800053f06024021605c05801a01800800800033f1e024021605605001a01800800800053f06026c21606805e01601400800800033a1a026c24205c05801601400800800033a1e026c24205605001601400800800053e06024021605c05001601400800800053a0602c426e06805001a01400600600053e36026c21606805e01a01800600600033a1a026c24205c05801a01800600600053a1a026c24205605001a01a00600600033f1e026c24205605401801800600600033a1e
theorem hd1_16:_GBJ.all (receiptTest 1)=true:=by decide+kernel
def _GBK:List ℕ:=decodeReceipts 16 0x2141ea04e04a01e01c00c00c00033e1e02141ea04804402001c00c00c00033f1e01e81be04e04402001c00c00c00053f0602141ea04e04a02002000a00a00053a0202141ea04e04a01e01c00a00a00053f0602141ea04804402001c00a00a00033e1e01e81be04e04402001c00a00a00053e0602141be04203602001c00e00a00053f0601bc16404e03602001c00e00a00053a06021416404e03601a01400c00a00053a0602c426e06805002001c00800800053a02026c21606805002001c00800800053a1a02c421606805002001c00600600053f1a02c426e06805001a01400800800053e36026c21606805e01a01800800800033a1a026c24205c05801a01800800800053a1a
theorem hd1_17:_GBK.all (receiptTest 1)=true:=by decide+kernel
def _GBL:List ℕ:=decodeReceipts 16 0x21420005205001e01c00c00c00053f4a01fe1ea05605001e01c00c00c00053e4a01e81be05c05002001c00c00c00053e4a02141ea05c05802001c00a00a00053a1a02141ea05605002002000a00a00053a02021420005605401e01c00a00a00053a1a021420005205001e01c00a00a00033f1e01fe1ea05605001e01c00a00a00033f1e01e81be05c05002001c00a00a00053e4a01bc16406805002001c00e00a00053e4a02141be06805e01a01800c00a00033a1a02141be05c05001a01800c00a00053f2602141be06805001601400a00a00053e0601bc16406805001a01400c00a00053a0602141be04e04402001c00e00e0005368602141ea04e04a02002000c00c00053a02
theorem hd1_18:_GBL.all (receiptTest 1)=true:=by decide+kernel
def _GBM:List ℕ:=decodeReceipts 16 0x24021604203e02001c00a00a00033e1e026c21603c03602001c00c00c00053686026c21603c03602001c00a00a00033f1e02c426e04e04401a01400c00a00053a36026c21604e04401a01800c00c00053686026c24204e04a01a01a00a00a00033e1e026c24204e04a01801800a00a00053e06026c24204804401a01800a00a00053f06024021604e04401a01800a00a00053e06026c21604e04401601400a00a00053a0602c421604203601a01400c00a0005368602141be06805002001c00e00e00033a1a02141be06805e02001c00c00a00033a1a02141ea05c05802001c00c00c00053a1a02141ea05605002002000c00c00053a02021420005605401e01c00c00c00053a1a
theorem hd1_19:_GBM.all (receiptTest 1)=true:=by decide+kernel
def _GBO:List ℕ:=decodeReceipts 16 0x25624204e04a01c01c00a00a00033f1e026c24204804402002000a00a00053a02026c25804804401e01e00a00a00053a02026c25804804401c01c00a00a00033e1e025624204804401e01c00a00a00033f1e024021604e04a02002000a00a00053a02024022c04e04a01e01e00a00a00033a1a024022c04e04a01c01c00a00a00033e1e022a21604e04a01e01c00a00a00033f1e024021604804402002000a00a00053a02024021604804401e01c00a00a00033e1e02c421604203602001c00e00e0005368602c426e04203602001c00c00a00053a22026c21604203e02001c00c00c00053686026c24204203e02002000a00a00053a02026c24204203e01e01c00a00a00033e1e
theorem hd1_20:_GBO.all (receiptTest 1)=true:=by decide+kernel
def _GBP:List ℕ:=decodeReceipts 16 0x26c24204e04a02002000c00c00053a02026c25804e04a01e01c00c00c00053a22025624204e04a01e01e00c00c00053a02025624204e04a01c01c00c00c00053686026c24204804402002000c00c00053a02026c24204804401e01c00c00c00053686024021604e04a02002000c00c00053a02024022c04e04a01e01e00c00c00033a1a024022c04e04a01c01c00c00c00053686022a21604e04a01e01e00c00c00033a1a022a21604e04a01c01c00c00c00053f06024021604804402002000c00c00053a02024021604804401e01c00c00c00053686026c24204e04a02002000a00a00053a02026c25804e04a01e01c00a00a00053a22025624204e04a01e01e00a00a00053a02
theorem hd1_21:_GBP.all (receiptTest 1)=true:=by decide+kernel
def _GBQ:List ℕ:=decodeReceipts 16 0x25624205605401a01a00a00a00033f1e026c24205205001a01a00a00a00033f1e026c24205605401801800a00a00033e1e026c26405205001801800a00a00053a36026225805205001801800a00a00053f06025624205205001801800a00a00053e06024021605c05801a01a00a00a00053a1a024021605c05801801800a00a00033e1e024021605605001a01a00a00a00033e1e024021605605001801800a00a00053e06026c21606805e01601400a00a00033a1a026c24205c05801601400a00a00033e1e026c24205605001601400a00a00053e06024021605c05001601400a00a00053e0602c421604e04402001c00e00e0005368602c426e04e04402001c00c00a00053a22
theorem hd1_22:_GBQ.all (receiptTest 1)=true:=by decide+kernel
def _GBR:List ℕ:=decodeReceipts 12 0x2c426e06805002001c00e00e00053e02026c21606805002001c00e00e00033a1a02c426e06805002001c00c00a00053e02026c21606805002001c00c00a00053a1a02c426e06805001a01400c00a00053f36026c21606805e01a01800c00a00033a1a026c24205c05801a01800c00c00053a1a026c24205605001a01800c00c00053686024021605c05801a01800c00c00053a1a024021605605001a01800c00c00053686026c24205c05801a01800a00a00053a1a026c25805605401a01a00a00a00053a1a
theorem hd1_23:_GBR.all (receiptTest 1)=true:=by decide+kernel
def codes1:List ℕ:=d1_0++d1_1++d1_2++d1_3++d1_4++d1_5++d1_6++d1_7++d1_8++d1_9++_GAM++_GAX++_GBF++_GBG++_GBH++_GBI++_GBJ++_GBK++_GBL++_GBM++_GBO++_GBP++_GBQ++_GBR
def boxes1:List Box:=codes1.map receiptBox
theorem boxesvalid1: ∀a∈boxes1,valid 1 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes1.all (receiptTest 1)=true:=by
  simp only [codes1,List.all_append,hd1_0,hd1_1,hd1_2,hd1_3,hd1_4,hd1_5,hd1_6,hd1_7,hd1_8,hd1_9,hd1_10,hd1_11,hd1_12,hd1_13,hd1_14,hd1_15,hd1_16,hd1_17,hd1_18,hd1_19,hd1_20,hd1_21,hd1_22,hd1_23,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d2_0:List ℕ:=decodeReceipts 16 0x5c03205c03201401000600400073a0a005c04805c04800e00800600400053a0a005c03204603200e00800600400000000005c03203001c02001600e00400053a0a005c03203001c01400800a00400000000005c03201a01002001600e00400053a0a005c03201a01001400800a00400000000005c03200e00401c00800e00400000000003001c03001c02001600e00400053a0a003001c03001c01400800a00400000000003001c01a01002001600e00400053a0a003001c01a01001400800a00400000000003001c00e00401c00800e00400000000001a01001a01002001600e00400053a0a001a01001a01001400800a00400000000001a00400e00401c00800e00400000000
theorem hd2_0:d2_0.all (receiptTest 2)=true:=by decide+kernel
def d2_1:List ℕ:=decodeReceipts 16 0x1640b606803801401000a0080005368a01640b6068038014008006004000736c201640b603601e02001600e00400053a0601640b603601e01400800a0040000000001640b601c01202001600e00400053a0a01640b601c01201400800a0040000000001640b601000401e00800e0040000000000b405e06803802001600e00400053a0600b405e06803801400800a004000736c200b405e03601e02001600e00400053a0600b405e03601e01400800a0040000000000b405e01c01202001600e00400053a0a00b405e01c01201400800a0040000000000b405e01000401e00800e00400000000005c03205c03202001600e00400053a06005c03205c03201401000a00800000000
theorem hd2_1:d2_1.all (receiptTest 2)=true:=by decide+kernel
def d2_2:List ℕ:=decodeReceipts 16 0x2141be06805e02001c00400400033a1a02141ea05c05202002000400400033a1602141ea05c05201e01c0040040005368601e81be05c05202001c00400400053f2602141be06805201a0160040040005368601bc16606805202001600400400053f2602141660500380200160060040005368602c416606803801400800a004000736be02c416603601e02001600e0040005368602c416603601e01400800a0040000000002c416601c01202001600e0040005368602c416601c01201400800a0040000000002c416601000c01e01400e0040005368a02c416601000c0120080080040000000002c416600a00401400800a0040000000001640b606803802001600e00400053e06
theorem hd2_2:d2_2.all (receiptTest 2)=true:=by decide+kernel
def d2_3:List ℕ:=decodeReceipts 16 0x26c21605c05202001c0060060005368602c421606805201a0160060060005368602c426e06805e02001c00400400053a0202c426e05c05202001c00400400053f36026c21606805e02001c00400400033a1a026c24205c05202002000400400053a02026c24205c05201e01c0040040003369e024021605c05202002000400400053a02024021605c05201e01c0040040005368602c426e06805201a01600400400053e36026c21606805201a0160040040005368602c42160500380200160060040005368602141be06805e02001c00600600033a1a02141be05c05202001c0060060005368602141be06805201a0160060060005368601bc16606805202001600600600053686
theorem hd2_3:d2_3.all (receiptTest 2)=true:=by decide+kernel
def d2_4:List ℕ:=decodeReceipts 4 0x2c416606803802001600e00a0005368602c41660680380200160080080005368602c426e06805202001c006006000536b6026c21606805e02001c00600600033a1a
theorem hd2_4:d2_4.all (receiptTest 2)=true:=by decide+kernel
def codes2:List ℕ:=d2_0++d2_1++d2_2++d2_3++d2_4
def boxes2:List Box:=codes2.map receiptBox
theorem boxesvalid2: ∀a∈boxes2,valid 2 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes2.all (receiptTest 2)=true:=by
  simp only [codes2,List.all_append,hd2_0,hd2_1,hd2_2,hd2_3,hd2_4,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d3_0:List ℕ:=decodeReceipts 10 0x2c416606803802001800e0060005368602c416606803801600c00a0060000000002c416603600602000c00e0060000000001640b606803802001800e00600053e0601640b606803801600c00a0060000000001640b603600602000c00e0060000000000b405e06803802001800e00600053a0600b405e06803801600c00a0060000000000b405e03600602000c00e00600000000005c00605c00602000c00e00600000000
theorem hd3_0:d3_0.all (receiptTest 3)=true:=by decide+kernel
def codes3:List ℕ:=d3_0
def boxes3:List Box:=codes3.map receiptBox
theorem boxesvalid3: ∀a∈boxes3,valid 3 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes3.all (receiptTest 3)=true:=by
  simp only [codes3,List.all_append,hd3_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d4_0:List ℕ:=decodeReceipts 1 0x2c400806800802001000e00800000000
theorem hd4_0:d4_0.all (receiptTest 4)=true:=by decide+kernel
def codes4:List ℕ:=d4_0
def boxes4:List Box:=codes4.map receiptBox
theorem boxesvalid4: ∀a∈boxes4,valid 4 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes4.all (receiptTest 4)=true:=by
  simp only [codes4,List.all_append,hd4_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d5_0:List ℕ:=decodeReceipts 1 0x2c400a06800a02001400e00a00000000
theorem hd5_0:d5_0.all (receiptTest 5)=true:=by decide+kernel
def codes5:List ℕ:=d5_0
def boxes5:List Box:=codes5.map receiptBox
theorem boxesvalid5: ∀a∈boxes5,valid 5 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes5.all (receiptTest 5)=true:=by
  simp only [codes5,List.all_append,hd5_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d6_0:List ℕ:=decodeReceipts 1 0x2c400c06800c02001800e00c00000000
theorem hd6_0:d6_0.all (receiptTest 6)=true:=by decide+kernel
def codes6:List ℕ:=d6_0
def boxes6:List Box:=codes6.map receiptBox
theorem boxesvalid6: ∀a∈boxes6,valid 6 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes6.all (receiptTest 6)=true:=by
  simp only [codes6,List.all_append,hd6_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d7_0:List ℕ:=decodeReceipts 1 0x2c400e06800e02001c00e00e00000000
theorem hd7_0:d7_0.all (receiptTest 7)=true:=by decide+kernel
def codes7:List ℕ:=d7_0
def boxes7:List Box:=codes7.map receiptBox
theorem boxesvalid7: ∀a∈boxes7,valid 7 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes7.all (receiptTest 7)=true:=by
  simp only [codes7,List.all_append,hd7_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def root (m:ℕ):Box:=⟨max 1 m,7,2*max 1 m,16,0,52,0,354⟩
def tree1:Tree:=(CP.decode 18 0x17b005e80136d0179005e00136d000610177005d80175005d0002b90173005c8002b90120d0171005c0016f004af405b800299016d005b0016b004c7405a8012bd00299000c5002b90169005a0000c5016700598000c5002b90120d00051002e90165005900163000ae405880120d002e9000b50136d000d5016100580015f00578015d00570000e5012bd000f5015b00568000f50024901590056001570003940558015500039404574003d4055001530003d400924048340548015100540014f00039404af4003d40538014d00530000e5014b004af4003d4009240528014900520000e50147004574003d4051801450003d400924048340014404db4001840510014300508014100500000f5013f0048340014404f8013d000144007a404db4001840086404f0013b004e8013900031404e00024901370048340014404d8000b50136d013500086400354009e404d00133004c80131004c0012f000a6404b800ffd000f5002b9012d003d3404b0012b004a80129000a6404a000ffd000f5002b90127003d340014400ba400184049800ded012500490002e901230002d4048800ded000d5012100480011f0003d4047800249011d003d340470011b0003d40468002490119003d34001440018404600021901170037b40458000d500279010ad0115004500136d01130000c40448011100440010f00438012bd010d000a640430010b000a640031400ae404280109000ae40483400ba40420010700418002b9010500483400ba4002d404db4041001030040801010040000ff000a640031400ae403f800fd000ae40483400ba403f000fb000ba4002d404db4000c40035403e800f9003e000f7003d8000e5012bd000f500f5003d000f300039403c8012bd000f50024900f1003c0000f500ef003b8000f5002490120d0136d00ed003b000eb003a800e900039404af4003d403a000e70003d400924039800e50003d40390002490120d0136d0003100e30038800e10003d403800120d00df0007a404db4037800dd00370000f500db0048340368001e90136d000310021900d90036000d700031403580024900d50048340350000b50136d00d3003480136d0003100d1003400136d00cf003380136d0003100219000d50027900cd0033000cb00328000f5002b900c9003d3400ba4032000c70031800c50003d400ae4031000f4d002e90003100c30037b40308000d500c10009e4042b4030000bf002f800bd002f000bb00031400ae402e800b9000ae40483400ba402e000b7000ba4002d404db40035402d800b5002d000b3004af4003d402c800b10003d40092402c000af0003d402b8002490120d0136d00ad002b00136d0021900ab002a80136d00a9002a00136d00219000d50027900a70029800a5000ae4029000f4d002e900a30037b40288000d500a10009e4042b40280009f00278009d00270009b00031400ae402680120d002e9009900260002e9000b50136d000d5009700258009500250012bd000f50093000924024800910003d40240002490120d0136d008f0008640238000d500279008d00230008b000ae4022800f4d002e900890037b40220000d500870009e4042b400044000840010402180085004db402100083004db4000c402080081004db4001d4020000279007f0042b401f8007d004db401f000075007b0009e401e8010ad00790000440008401e000055000950077001d8000d5007500052401d0010ad0073001c80136d0071001c00136d00031006f00035401b8006d0003540052401b0010ad006b001a8000d50069001a0000d50014900670042b4019800011000210004100650019000630000d40015400254018800610001040180005f000154002540178005d0017000065005b0016800021000490004100079000d9001a900590016000095005700158005500150000110002100530014800149005100140001490085d004f0000440138000350005500095004d00130004b0001540025401280049001200006500470011800021000490004100079000d9001a900450011000430010800410005240100003f000524010f400f800011003d0000d4001540025400f0003b000e800055000950039000e0003700019400d800350000840012400104001e400364006a400d0003300025400c80031000c0002f00004400b8000350005500095002d000b0002b000a8000110002100290001540025400a000270009800250000440008400900005500230000e4000c4001a4003240088002100080001f000044000840078001d0000440070000350005500095001b000680019000600001100021001700015400254005800150005000130000440008400480005500110000e4000c4001a40040000f00038000d0000440008400300005500095000b00028000900020000110002100070001540018000390003100050001000030000800011000210001000154000000039000310006d00069000cd000c90017d00179002dd0059d00b1d).1
theorem cv1:Covered 1 (valid 1) (root 1):=by
 apply CP.sound (listBox boxes1) boxes1.length 1 (valid 1) (tree:=tree1)
 · exact listBox_valid boxes1 (valid 1) boxesvalid1
 · decide+kernel
def tree2:Tree:=(CP.decode 14 0x4300108004100100003f000ba404db400f8000d5003d000f0002e9003b000e800390003d400e000370003d40483400ba404db400d80035004db4003540008400d0002890033000c8002e9003100035400c000ded002f000b8002d0003d400b000f4d002e9002b00035400a800ded000210029000a24042b4000c40010400a0000a5002700098000a5002500090000a500230008800095002100016400224003a4006e40080001f0007800031000a5001d00070000a5001b00068000a50019000224003a4006e4006000170002940058001500029400500013000294004800089000e9001b9001100040000f00038000d0008e4001d4000c4002940030000b00029400280009000294002000079000d9000700018000a5000500010000a500030001e400080001000294000000079000dd000d90018d00189002ed005ad00b2d).1
theorem cv2:Covered 2 (valid 2) (root 2):=by
 apply CP.sound (listBox boxes2) boxes2.length 2 (valid 2) (tree:=tree2)
 · exact listBox_valid boxes2 (valid 2) boxesvalid2
 · decide+kernel
def tree3:Tree:=(CP.decode 6 0x900020000b500070006e4001800050002d40010001b9000300008000b500010006e40000002ed005ad00b2d).1
theorem cv3:Covered 3 (valid 3) (root 3):=by
 apply CP.sound (listBox boxes3) boxes3.length 3 (valid 3) (tree:=tree3)
 · exact listBox_valid boxes3 (valid 3) boxesvalid3
 · decide+kernel
def tree4:Tree:=(CP.decode 1 0x0).1
theorem cv4:Covered 4 (valid 4) (root 4):=by
 apply CP.sound (listBox boxes4) boxes4.length 4 (valid 4) (tree:=tree4)
 · exact listBox_valid boxes4 (valid 4) boxesvalid4
 · decide+kernel
def tree5:Tree:=(CP.decode 1 0x0).1
theorem cv5:Covered 5 (valid 5) (root 5):=by
 apply CP.sound (listBox boxes5) boxes5.length 5 (valid 5) (tree:=tree5)
 · exact listBox_valid boxes5 (valid 5) boxesvalid5
 · decide+kernel
def tree6:Tree:=(CP.decode 1 0x0).1
theorem cv6:Covered 6 (valid 6) (root 6):=by
 apply CP.sound (listBox boxes6) boxes6.length 6 (valid 6) (tree:=tree6)
 · exact listBox_valid boxes6 (valid 6) boxesvalid6
 · decide+kernel
def tree7:Tree:=(CP.decode 1 0x0).1
theorem cv7:Covered 7 (valid 7) (root 7):=by
 apply CP.sound (listBox boxes7) boxes7.length 7 (valid 7) (tree:=tree7)
 · exact listBox_valid boxes7 (valid 7) boxesvalid7
 · decide+kernel
theorem covered (m:ℕ) (hm:0<m) (hh:m≤7):Covered m (valid m) (root m):=by
 interval_cases m
 · exact cv1
 · exact cv2
 · exact cv3
 · exact cv4
 · exact cv5
 · exact cv6
 · exact cv7

end ADD

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BAG
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF NX
open GZ ME LK
open HI LV BH DR
open FF ZGL ON YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {t y r cap low:ℕ}
theorem from_sources (hLow:2985<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 [Fact (Irreducible P.F)] (hFT:low≤wt AT P.F)
 (S:Source P.F) (hS:Profile S 16 52 354 7 0 1)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤7→PA.Covered m
   (OZ.Valid m low t y r cap) (ADD.root m)):
 P.seeds.card≤cap:=by
 classical
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hST:S.T=354:=hS.2.2.1
 have hs:=ADG P.F S (by rw [hST];omega) P.rdegree hchar
   (by rw [hS.2.2.2.2.1];decide)
 have hpow:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣QC (carrierMap P.F) S.P:=by
   change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS S.P).map (carrierMap P.F)
   simpa only [Source.d,hS.2.2.2.2.1,Nat.zero_add] using hs.2
 have hroot:NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0:=by
   exact Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
 obtain ⟨J,hJ,hJS,hJroot,_⟩:=ADQ
   (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
 obtain ⟨hJne,hm,hms,hJb,hJu,hJt,hJs⟩:=AVL P.F S (by rw [hST];omega) J hJ hJS hJroot
 rw [hS.1] at hJb
 rw [hS.2.1] at hJu
 rw [hS.2.2.1] at hJt
 rw [hS.2.2.2.1] at hJs
 let m:=multiplicity P.F J
 have hn:=_Q15 J
 have horder:1≤order J:=Nat.succ_le_of_lt (hm.trans_le hms)
 have hadm:PA.Admissible m (point J):=
   ⟨hms,horder,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
 have hx:Contains (ADD.root m) (point J):=by
   dsimp only [Contains,ADD.root,point]
   refine ⟨max_le horder hms,hJs,?_,hJb,Nat.zero_le _,hJu,Nat.zero_le _,hJt⟩
   have hh:=hn.2.2.1
   omega
 obtain ⟨a,hvalid,ha⟩:=hcov m hm (hms.trans hJs) (point J) hadm hx
 exact OZ.BLH nodes hI P hFT hLow hcap hid J hJ horder a ha rfl hJne hJroot hvalid

theorem packet_count (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) 4000 57 13) (hFT:3681≤wt AT P.F):
 P.seeds.card≤267000000000000000:=by
 classical
 letI:Fact (Irreducible P.F):=⟨P.irreducible⟩
 rcases VT QE.p0 QE.shape0 97989970 (by decide)
     QE.dimension0 nodes P.u0 P.u1 hI P.F P.irreducible (by change 354<_;omega)
     13 57 4000 (by decide) (by decide) (by decide) ⟨P.r_weight,P.y_weight,P.total_weight⟩
     with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · exact (KY.helper_count QE.p0 nodes P
     (by decide) (by decide) (by decide) (by decide) Q hQ).le.trans (by decide)
 exact from_sources (by decide) nodes hI P hFT S hS (by decide) (by decide+kernel) ADD.covered

end
end BAG

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace ADC
open DR (Box Contains lower upper)
open HI PA AED ADB
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
abbrev valid (m:ℕ):=OZ.Valid m 3681 3924 59 13 271000000000000000

set_option autoImplicit false
open CP

def receiptBox (code:ℕ):Box:=
 let x:=code/8589934592
 ⟨x%4096,x/4096%4096,x/4096^2%4096,x/4096^3%4096,
  x/4096^4%4096,x/4096^5%4096,x/4096^6%4096,x/4096^7%4096⟩
def receiptTest (m code:ℕ):Bool:=
 let a:=receiptBox code
 if code%4=0 then BH.check .native (degrees OZ.fallback) a m 3681 3924 59 13 271000000000000000
 else if code%4=1 then decide (LinearValid a 3681 3924 59 13 271000000000000000)
 else if h:code/4%32<22∧code/256%512<321 then
  decide ((CN.profile ⟨code/256%512,h.2⟩).L<3681∧
   BandValid (degrees ⟨code/256%512,h.2⟩) a m 3681 3924 59 13 271000000000000000
     ⟨code/4%32,h.1⟩ (code/128%2=1) (code/131072%65536))
 else false

theorem receipt_sound (m code:ℕ) (h:receiptTest m code=true):valid m (receiptBox code):=by
 unfold receiptTest at h
 split_ifs at h with h0 h1 h2
 · exact Or.inl h
 · exact Or.inr (Or.inl (of_decide_eq_true h))
 · have hh:=of_decide_eq_true h
   exact Or.inr (Or.inr ⟨⟨code/4%32,h2.1⟩,decide (code/128%2=1),⟨code/256%512,h2.2⟩,code/131072%65536,hh.1,hh.2⟩)

def decodeReceipts:ℕ→ℕ→List ℕ
 | 0,_=>[]
 | n+1,c=>c%2^132::decodeReceipts n (c/2^132)
def d1_0:List ℕ:=decodeReceipts 16 0x1800e01800e01200c00800600000000001800e01800e01200c004004000736b2001800e01800e01200c00200200000001001800e01800e00a00400400200000000001800e00c00801801000c00800000000001800e00c00801200c00600600000000001800e00c00801000c00400400000000001800e00c00a00e00c00200200000000001800e00c00800a00400400200000000001800e00600200c00400600200000000000c00800c00801801000c00800000000000c00800c00801200c00600600000000000c00800c00801000c00400400000000000c00a00c00a00e00c00200200000000000c00800c00800a00400400200000000000c00200600200c00400600200000000
theorem hd1_0:d1_0.all (receiptTest 1)=true:=by decide+kernel
def d1_1:List ℕ:=decodeReceipts 16 0x2e01a02e01a01200c00200200000001002e01a02e01a00a00800400400000000002e01a02e01a00a00800200200000001002e01a02e01a00600400200200000000002e01a01800e02001400e00200053606002e01a01800e01200c00800600000000002e01a01800e01200c004004000736b2002e01a01800e01200c00200200000001002e01a01800e00a00400400200000000002e01a00c00801801000c00800000000002e01a00c00801200c00600600000000002e01a00c00801000c00400400000000002e01a00c00a00e00c00200200000000002e01a00c00800a00400400200000000002e01a00600200c00400600200000000001800e01800e02001400e00200053606
theorem hd1_1:d1_1.all (receiptTest 1)=true:=by decide+kernel
def d1_2:List ℕ:=decodeReceipts 16 0x5a03002e01a00a00800200200000001005a03002e01a00600400200200000000005a03001800e02001400e00200053606005a03001800e01200c00800600000000005a03001800e01200c004004000736b2005a03001800e01200c00200200000001005a03001800e00a00400400200000000005a03000c00801801000c00800000000005a03000c00801200c00600600000000005a03000c00801000c00400400000000005a03000c00a00e00c00200200000000005a03000c00800a00400400200000000005a03000600200c00400600200000000002e01a02e01a02001400e00200053606002e01a02e01a01200c00800600073692002e01a02e01a01200c004004000936c6
theorem hd1_2:d1_2.all (receiptTest 1)=true:=by decide+kernel
def d1_3:List ℕ:=decodeReceipts 16 0x8605c02801c00a0080040040000000000b205c03401c00a0080020020000000100b205c03401c0060040020020000000100b205c01a01002001400e0020005360600b205c01a01001200c008002000736ae00b205c01a01000a0040040020000000000b205c00e00a01c01400e00a0000000000b205c00e00a01600e00800200073a0e00b205c00e00a00c0040060020000000000b205c00800601000c0080060000000000b205c00800200c00400400200000000005a03005a03002001400e00200053a06005a03005a03001200400800200073f56005a03002e01a02001400e00200053606005a03002e01a01200c00800200073a2a005a03002e01a00a00800400400000000
theorem hd1_3:d1_3.all (receiptTest 1)=true:=by decide+kernel
def d1_4:List ℕ:=decodeReceipts 16 0x1620b403401c00a0080020020000000101620b403401c0060040020020000000101620b401a01002001400e00200053a0601620b401a01001200c008002000736ae01620b401a01000a0040040020000000001620b400e00a01c01400e00a0000000001620b400e00a01600e00800200073a0e01620b400e00a00c0040060020000000001620b400800601000c0080060000000001620b400800200c0040040020000000000b205c06803602000400e00200073f5200b205c03401c02001400e00200053a0600b205c03401c01200c00800200073a0e00b208803402a00a00800400400073a0e00b208802801c00a00800400400000000008605c03402a00a00800400400073a0e
theorem hd1_4:d1_4.all (receiptTest 1)=true:=by decide+kernel
def d1_5:List ℕ:=decodeReceipts 16 0x2c416401a01000a0040040020000000002c416400e00a01c01400e00a00053a0602c416400e00a01600e00800200073a0a02c416400e00a00c0040060020000000002c416400800601000c0080060000000002c416400800200c0040040020000000001620b406803602001400e00200053e0601620b406803601200400800200053e0a01620b403401c02001400e00200053a0601620b403401c01200c0080060007368e01620b403401c01200c0040040007368e01620b403401c01200c00200200000001016210c03402a00a00800400400073a0e016210c02801c00a00800400400000000010a0b403402a00a00800400400073a0e010a0b402801c00a00800400400000000
theorem hd1_5:d1_5.all (receiptTest 1)=true:=by decide+kernel
def d1_6:List ℕ:=decodeReceipts 16 0x2c421602801c02001c00800600033e1e02c421602801c01a01400800600053a06021416403401c02001400800600053a0602c426e03402a02001c00400400053a22026c21603402a02001c00400400053e0602c421603402a01a01400400400053e0602c421602801c02001c00400400033a1e02c421602801c01a01400400400053a06021416403401c02001400400400053a0602c416403401c0200140020020000000102c416403401c01200c00800200073a3a02c416403401c00a00800400200073a4e02c416403401c0060040020020000000102c416401a01002001400e00a0005368602c416401a01002001400800200053e0602c416401a01001200c008002000736aa
theorem hd1_6:d1_6.all (receiptTest 1)=true:=by decide+kernel
def d1_7:List ℕ:=decodeReceipts 16 0x26c21606805001201000400400053e0602c421606805000e00c00400400053e0602c421604e03601200c00400400053a06021416406803601200c00400400053a0602c416406803601200c0020020000000102c416406803600a00400400200053a0602c421603402a02001c00e00e0005368602c421603402a02001c00c00a0003369e02c421603402a01a01400c00a0005368602c421602801c02001400e00a00053686021416403401c02001400e00a00053a0602c426e03402a02001c00800800053a22026c21603402a02001c00800800033a1e02c426e03402a02001c00600600053a22026c21603402a02001c00600600053f0602c421603402a01a01400800600053f06
theorem hd1_7:d1_7.all (receiptTest 1)=true:=by decide+kernel
def d1_8:List ℕ:=decodeReceipts 16 0x2c421604e03601a0140020020000000102141be06805e02001c00200200033a1a02141ea05c05802001c00200200053a1a02141ea05605002001c00200200053f4a01e81be05c05002001c00200200053f2601bc16406805002001c00200200053f26021416406805001a01400200200053f06021416404e03602001400200200053f0602c426e06805001201000800800053a36026c21606805001201000800800053e0602c426e06805001201000600600053a36026c21606805001201000600600053e0602c421606805000e00c00600600053f0602c421604e03601200c00800600053e06021416406803601200c00800600053a0602c426e06805001201000400400053a36
theorem hd1_8:d1_8.all (receiptTest 1)=true:=by decide+kernel
def d1_9:List ℕ:=decodeReceipts 16 0x2c421606805002001c00200200053e1a02c426e06805001a01400200200053a36026c21606805e01a01800200200033a1a026c24205c05801a01800200200053a1a026c24205605001a01800200200000001024021605c05001a01800200200053f06026c21606805e01601400200200033a1a026c21605c0500160140020020000000102c426e04e04402001c00200200053a22026c24204e04a02002000200200053a02026c24204e04a01e01c00200200000001026c24204804402001c00200200000001024021604e04a02002000200200053a02024021604e04a01e01c00200200000001024021604804402001c0020020000000102c421604203602001c00200200000001
theorem hd1_9:d1_9.all (receiptTest 1)=true:=by decide+kernel
def _GAM:List ℕ:=decodeReceipts 16 0x24021604e04a01e01c00400400033e1e024021604804402001c00400400033f1e02c426e04203602001c00400400053a22026c21604203602001c00400400033f1e02c426e04e04401a01400400400053a36026c21604e04401a01400400400053f0602c426e04203601a01400400400053a36026c21604203601a01400400400053a0602141be06805e02001c00400400033a1a02141ea05c05802001c00400400053a1a02141ea05605002002000400400053a0202141ea05605001e01c00400400033e1e01e81be05c05002001c00400400053a4a01bc16406805002001c00400400053a4a021416406805001a01400400400053e4a021416404e03602001400400400053f26
theorem hd1_10:_GAM.all (receiptTest 1)=true:=by decide+kernel
def _GAX:List ℕ:=decodeReceipts 16 0x2c426e06805001a01400400400053e36026c21606805e01a01800400400033a1a026c24205c05801a01800400400053a1a026c24205605001a01a00400400033e1e026c24205605001801800400400053f06024021605c05801a01800400400033e1e024021605605001a01800400400053e06026c21606805e01601400400400033a1a026c21605c05001601400400400053e0602c426e04e04402001c00400400053a22026c24204e04a02002000400400053a02026c25804e04a01e01c00400400053a22025624204e04a01e01c00400400033f1e026c24204804402002000400400053a02026c24204804401e01c00400400033e1e024021604e04a02002000400400053a02
theorem hd1_11:_GAX.all (receiptTest 1)=true:=by decide+kernel
def _GBF:List ℕ:=decodeReceipts 16 0x2c426e04203601a01400600600053a36026c21604203601a01400600600053a0602141be06805e02001c00800800033a1a02141ea05c05802001c00800800053a1a02141ea05605002002000800800053a0202141ea05605001e01c00800800053f4a01e81be05c05002001c00800800053e4a02141be06805e02001c00600600033a1a02141ea05c05802001c00600600053a1a02141ea05605002002000600600053a0202141ea05605001e01c00600600033f1e01e81be05c05002001c00600600053e4a01bc16406805002001c00800600053a4a021416406805001a01400800600053f4a021416404e03602001400800600073f4a02c421606805002001c00400400053e1a
theorem hd1_12:_GBF.all (receiptTest 1)=true:=by decide+kernel
def _GBG:List ℕ:=decodeReceipts 16 0x24021604203e02001c00600600033e1e026c21603c03602001c00600600033e1e02c426e04e04401a01400800800053a36026c24204e04a01a01a00800800033e1e026c24204e04a01801800800800053e06026c24204804401a01800800800053e06024021604e04401a01800800800053e06026c21604e04401601400800800053a0602c426e04e04401a01400600600053a36026c24204e04a01a01a00600600033a1e026c24204e04a01801800600600053e06026c24204804401a01800600600053e06024021604e04401a01800600600053a06026c21604e04401601400600600053a0602c426e04203601a01400800800053a36026c21604203601a01400800800053a06
theorem hd1_13:_GBG.all (receiptTest 1)=true:=by decide+kernel
def _GBH:List ℕ:=decodeReceipts 16 0x25624204e04a01e01e00600600053a02025624204e04a01c01c00600600033e1e026c24204804402002000600600053a02026c24204804401e01c00600600033f1e024021604e04a02002000600600053a02024021604e04a01e01c00600600033f1e024021604804402002000600600053a02024021604804401e01c00600600053f0602c426e04203602001c00800800053a22026c24204203e02002000800800053a02026c24204203e01e01c00800800033e1e024021604203e02001c00800800033e1e026c21603c03602001c00800800033f1e02c426e04203602001c00600600053a22026c24204203e02002000600600053a02026c24204203e01e01c00600600033e1e
theorem hd1_14:_GBH.all (receiptTest 1)=true:=by decide+kernel
def _GBI:List ℕ:=decodeReceipts 16 0x26c25804e04a01e01c00800800053a22025624204e04a01e01e00800800053a02025624204e04a01c01c00800800033e1e026c24204804402002000800800053a02026c25804804401e01e00800800053a02026c25804804401c01c00800800033e1e025624204804401e01c00800800033f1e024021604e04a02002000800800053a02024022c04e04a01e01e00800800033a1a024022c04e04a01c01c00800800033e1e022a21604e04a01e01c00800800033e1e024021604804402002000800800053a02024021604804401e01c00800800033e1e02c426e04e04402001c00600600053a22026c24204e04a02002000600600053a02026c25804e04a01e01c00600600053a22
theorem hd1_15:_GBI.all (receiptTest 1)=true:=by decide+kernel
def _GBJ:List ℕ:=decodeReceipts 16 0x26c21606805e01601400800800033a1a026c24205c05801601400800800033a1e026c24205605001601400800800053e06024021605c05001601400800800053a0602c426e06805001a01400600600053e36026c21606805e01a01800600600033a1a026c24205c05801a01800600600053a1a026c24205605001a01a00600600033f1e026c24205605401801800600600033a1e026c24205205001801800600600053e06024021605c05801a01800600600033e1e024021605605001a01800600600053f06026c21606805e01601400600600033a1a026c21605c05001601400600600053f0602c426e04e04402001c00800800053a22026c24204e04a02002000800800053a02
theorem hd1_16:_GBJ.all (receiptTest 1)=true:=by decide+kernel
def _GBK:List ℕ:=decodeReceipts 16 0x2141be04203602001c00e00a00033e1e01bc16404e03602001c00e00a00053a06021416404e03601a01400c00a00053a0602c426e06805002001c00800800053a02026c21606805002001c00800800053a1a02c421606805002001c00600600053f1a02c426e06805001a01400800800053e36026c21606805e01a01800800800033a1a026c24205c05801a01800800800053a1a026c25805605401a01a00800800053a1a025624205605401a01a00800800033e1e026c24205205001a01a00800800033e1e026c24205605401801800800800033e1e026c24205205001801800800800053f06024021605c05801a01800800800033f1e024021605605001a01800800800053f26
theorem hd1_17:_GBK.all (receiptTest 1)=true:=by decide+kernel
def _GBL:List ℕ:=decodeReceipts 16 0x1fe1ea05605001e01c00a00a00053e4a01e81be05c05002001c00a00a00053e4a01bc16406805002001c00e00a00053e4a02141be06805e01a01800c00a00033a1a02141be05c05001a01800c00a00053f2602141be06805001601400a00a00053e0601bc16406805001a01400c00a00053a0602141be04e04402001c00e00e0005368602141ea04e04a02002000c00c00053a0202141ea04e04a01e01c00c00c00033f1e02141ea04804402001c00c00c00033f1e01e81be04e04402001c00c00c00053f0602141ea04e04a02002000a00a00053a0202141ea04e04a01e01c00a00a00053f0602141ea04804402001c00a00a00033e1e01e81be04e04402001c00a00a00053e06
theorem hd1_18:_GBL.all (receiptTest 1)=true:=by decide+kernel
def _GBM:List ℕ:=decodeReceipts 16 0x24021604e04401a01800a00a00053e06026c21604e04401601400a00a00053a0602c421604203601a01400c00a0005368602141be06805002001c00e00e00033a1a02141be06805e02001c00c00a00033a1a02141ea05c05802001c00c00c00053a1a02141ea05605002002000c00c00053a02021420005605401e01c00c00c00053a1a021420005205001e01e00c00c00033a1a021420005205001c01c00c00c00053f0601fe1ea05605001e01c00c00c00053e4a01e81be05c05002001c00c00c00053f4a02141ea05c05802001c00a00a00053a1a02141ea05605002002000a00a00053a02021420005605401e01c00a00a00053a1a021420005205001e01c00a00a00033f1e
theorem hd1_19:_GBM.all (receiptTest 1)=true:=by decide+kernel
def _GBO:List ℕ:=decodeReceipts 16 0x24021604804401e01c00a00a00033e1e02c421604203602001c00e00e0005368602c426e04203602001c00c00a00053a22026c21604203e02001c00c00c00053686026c24204203e02002000a00a00053a02026c24204203e01e01c00a00a00033f1e024021604203e02001c00a00a00033f1e026c21603c03602001c00c00c00053686026c24203c03602002000a00a00053a02026c24203c03601e01c00a00a00033e1e024021603c03602001c00a00a00033e1e02c426e04e04401a01400c00a00053a36026c21604e04401a01800c00c00053686026c24204e04a01a01a00a00a00033e1e026c24204e04a01801800a00a00053e06026c24204804401a01800a00a00053f06
theorem hd1_20:_GBO.all (receiptTest 1)=true:=by decide+kernel
def _GBP:List ℕ:=decodeReceipts 16 0x24021604804402002000c00c00053a02024021604804401e01c00c00c00053686026c24204e04a02002000a00a00053a02026c25804e04a01e01c00a00a00053a22025624204e04a01e01e00a00a00053a02025624204e04a01c01c00a00a00033f1e026c24204804402002000a00a00053a02026c25804804401e01e00a00a00053a02026c25804804401c01c00a00a00033e1e025624204804401e01e00a00a00033a1a025624204804401c01c00a00a00033e1e024021604e04a02002000a00a00053a02024022c04e04a01e01e00a00a00033a1a024022c04e04a01c01c00a00a00033e1e022a21604e04a01e01c00a00a00033f1e024021604804402002000a00a00053a02
theorem hd1_21:_GBP.all (receiptTest 1)=true:=by decide+kernel
def _GBQ:List ℕ:=decodeReceipts 16 0x26c24205c05801601400a00a00033e1e026c24205605001601400a00a00053e06024021605c05001601400a00a00053e0602c421604e04402001c00e00e0005368602c426e04e04402001c00c00a00053a22026c24204e04a02002000c00c00053a02026c25804e04a01e01c00c00c00053a22025624204e04a01e01e00c00c00053a02025624204e04a01c01c00c00c00053686026c24204804402002000c00c00053a02026c24204804401e01c00c00c00053686024021604e04a02002000c00c00053a02024022c04e04a01e01e00c00c00033a1a024022c04e04a01c01c00c00c00053686022a21604e04a01e01e00c00c00033a1a022a21604e04a01c01c00c00c00053f06
theorem hd1_22:_GBQ.all (receiptTest 1)=true:=by decide+kernel
def _GBR:List ℕ:=decodeReceipts 16 0x26c24205605001a01800c00c00053686024021605c05801a01800c00c00053a1a024021605605001a01800c00c00053686026c24205c05801a01800a00a00053a1a026c25805605401a01a00a00a00053a1a025624205605401a01a00a00a00033f1e026c24205205001a01a00a00a00033f1e026c24205605401801800a00a00033e1e026c26405205001801800a00a00053a36026225805205001801800a00a00053f06025624205205001801800a00a00053e06024021605c05801a01a00a00a00053a1a024021605c05801801800a00a00033e1e024021605605001a01a00a00a00033e1e024021605605001801800a00a00053e06026c21606805e01601400a00a00033a1a
theorem hd1_23:_GBR.all (receiptTest 1)=true:=by decide+kernel
def _GBS:List ℕ:=decodeReceipts 7 0x2c426e06805002001c00e00e00053e02026c21606805002001c00e00e00033a1a02c426e06805002001c00c00a00053e02026c21606805002001c00c00a00053a1a02c426e06805001a01400c00a00053f36026c21606805e01a01800c00a00033a1a026c24205c05801a01800c00c00053a1a
theorem hd1_24:_GBS.all (receiptTest 1)=true:=by decide+kernel
def codes1:List ℕ:=d1_0++d1_1++d1_2++d1_3++d1_4++d1_5++d1_6++d1_7++d1_8++d1_9++_GAM++_GAX++_GBF++_GBG++_GBH++_GBI++_GBJ++_GBK++_GBL++_GBM++_GBO++_GBP++_GBQ++_GBR++_GBS
def boxes1:List Box:=codes1.map receiptBox
theorem boxesvalid1: ∀a∈boxes1,valid 1 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes1.all (receiptTest 1)=true:=by
  simp only [codes1,List.all_append,hd1_0,hd1_1,hd1_2,hd1_3,hd1_4,hd1_5,hd1_6,hd1_7,hd1_8,hd1_9,hd1_10,hd1_11,hd1_12,hd1_13,hd1_14,hd1_15,hd1_16,hd1_17,hd1_18,hd1_19,hd1_20,hd1_21,hd1_22,hd1_23,hd1_24,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d2_0:List ℕ:=decodeReceipts 16 0x5c03205c03201401000600400073a0a005c04805c04800e00800600400053a0a005c03204603200e00800600400000000005c03203001c02001600e00400053a0a005c03203001c01400800a00400000000005c03201a01002001600e00400053a0a005c03201a01001400800a00400000000005c03200e00401c00800e00400000000003001c03001c02001600e00400053a0a003001c03001c01400800a00400000000003001c01a01002001600e00400053a0a003001c01a01001400800a00400000000003001c00e00401c00800e00400000000001a01001a01002001600e00400053a0a001a01001a01001400800a00400000000001a00400e00401c00800e00400000000
theorem hd2_0:d2_0.all (receiptTest 2)=true:=by decide+kernel
def d2_1:List ℕ:=decodeReceipts 16 0x1640b606803801401000a0080005368a01640b6068038014008006004000736c201640b603601e02001600e00400053a0601640b603601e01400800a0040000000001640b601c01202001600e00400053a0a01640b601c01201400800a0040000000001640b601000401e00800e0040000000000b405e06803802001600e00400053a0600b405e06803801400800a004000736c200b405e03601e02001600e00400053a0600b405e03601e01400800a0040000000000b405e01c01202001600e00400053a0a00b405e01c01201400800a0040000000000b405e01000401e00800e00400000000005c03205c03202001600e00400053a06005c03205c03201401000a00800000000
theorem hd2_1:d2_1.all (receiptTest 2)=true:=by decide+kernel
def d2_2:List ℕ:=decodeReceipts 16 0x2141be06805e02001c00400400033a1a02141ea05c05202002000400400033a1602141ea05c05201e01c0040040005368601e81be05c05202001c00400400053a4a02141be06805201a0160040040005368601bc16606805202001600400400053a4a02141660500380200160060040005368602c416606803801400800a004000736be02c416603601e02001600e0040005368602c416603601e01400800a0040000000002c416601c01202001600e0040005368602c416601c01201400800a0040000000002c416601000c01e01400e0040005368a02c416601000c0120080080040000000002c416600a00401400800a0040000000001640b606803802001600e00400053e06
theorem hd2_2:d2_2.all (receiptTest 2)=true:=by decide+kernel
def d2_3:List ℕ:=decodeReceipts 16 0x2c426e05c05202002000400400053a0202c426e05c05201e01c00400400053e36026c21606805e02001c00400400033a1a026c24205c05202002000400400053a02026c24205c05201e01c0040040003369e024021605c05202002000400400053a02024021605c05201e01c0040040005368602c426e06805201a01600400400053e36026c21606805201a0160040040005368602c42160500380200160060060005368602c421605003802001c0040040003369e02c421605003801a0160040040005368602141be06805e02001c00600600033a1a02141be05c05202001c0060060005368602141be06805201a0160060060005368601bc16606805202001600600600053686
theorem hd2_3:d2_3.all (receiptTest 2)=true:=by decide+kernel
def d2_4:List ℕ:=decodeReceipts 7 0x2c416606803802001600e00a0005368602c41660680380200160080080005368602c426e06805202001c006006000536b6026c21606805e02001c00600600033a1a026c21605c05202001c0060060005368602c421606805201a0160060060005368602c426e06805e02001c00400400053a02
theorem hd2_4:d2_4.all (receiptTest 2)=true:=by decide+kernel
def codes2:List ℕ:=d2_0++d2_1++d2_2++d2_3++d2_4
def boxes2:List Box:=codes2.map receiptBox
theorem boxesvalid2: ∀a∈boxes2,valid 2 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes2.all (receiptTest 2)=true:=by
  simp only [codes2,List.all_append,hd2_0,hd2_1,hd2_2,hd2_3,hd2_4,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d3_0:List ℕ:=decodeReceipts 10 0x2c416606803802001800e0060005368602c416606803801600c00a0060000000002c416603600602000c00e0060000000001640b606803802001800e00600053e0601640b606803801600c00a0060000000001640b603600602000c00e0060000000000b405e06803802001800e00600053a0600b405e06803801600c00a0060000000000b405e03600602000c00e00600000000005c00605c00602000c00e00600000000
theorem hd3_0:d3_0.all (receiptTest 3)=true:=by decide+kernel
def codes3:List ℕ:=d3_0
def boxes3:List Box:=codes3.map receiptBox
theorem boxesvalid3: ∀a∈boxes3,valid 3 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes3.all (receiptTest 3)=true:=by
  simp only [codes3,List.all_append,hd3_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d4_0:List ℕ:=decodeReceipts 1 0x2c400806800802001000e00800000000
theorem hd4_0:d4_0.all (receiptTest 4)=true:=by decide+kernel
def codes4:List ℕ:=d4_0
def boxes4:List Box:=codes4.map receiptBox
theorem boxesvalid4: ∀a∈boxes4,valid 4 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes4.all (receiptTest 4)=true:=by
  simp only [codes4,List.all_append,hd4_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d5_0:List ℕ:=decodeReceipts 1 0x2c400a06800a02001400e00a00000000
theorem hd5_0:d5_0.all (receiptTest 5)=true:=by decide+kernel
def codes5:List ℕ:=d5_0
def boxes5:List Box:=codes5.map receiptBox
theorem boxesvalid5: ∀a∈boxes5,valid 5 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes5.all (receiptTest 5)=true:=by
  simp only [codes5,List.all_append,hd5_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d6_0:List ℕ:=decodeReceipts 1 0x2c400c06800c02001800e00c00000000
theorem hd6_0:d6_0.all (receiptTest 6)=true:=by decide+kernel
def codes6:List ℕ:=d6_0
def boxes6:List Box:=codes6.map receiptBox
theorem boxesvalid6: ∀a∈boxes6,valid 6 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes6.all (receiptTest 6)=true:=by
  simp only [codes6,List.all_append,hd6_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d7_0:List ℕ:=decodeReceipts 1 0x2c400e06800e02001c00e00e00000000
theorem hd7_0:d7_0.all (receiptTest 7)=true:=by decide+kernel
def codes7:List ℕ:=d7_0
def boxes7:List Box:=codes7.map receiptBox
theorem boxesvalid7: ∀a∈boxes7,valid 7 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes7.all (receiptTest 7)=true:=by
  simp only [codes7,List.all_append,hd7_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def root (m:ℕ):Box:=⟨max 1 m,7,2*max 1 m,16,0,52,0,354⟩
def tree1:Tree:=(CP.decode 18 0x6180185004db406100183004db4001840608018100600017f000ae405f8017d000ae40483405f0017b005e8012bd0179000a6405e00177005d80131d0175004af400a640031400ae405d0017300031405c8017100031400ae4048340014400ba405c0016f005b8002b9016d00483400ba4002d404db40035405b0016b005a80169005a0016700039404af4003d4059801650003d4009240590016300588000e5016100580000e50115d000f5015f00578000f5002490120d015d00570015b00568000e5012bd000f501590056001570003940558015500039404af4003d4009240550015300548000e50151004574003d40540014f0003d400924048340014404db4001840538014d00530014b00528000f50149004834001440520014700518000f5014500483400144007a404db4001840086405100143005080141000314050000249013f0048340014404f8000b50136d013d00086400354009e404f0013b004e80139004e00137004d8000e5002990135003ff4003d400ae404d000f4d0133004c80131004c000299012f003ff4003d400ae404b800f4d00051002e900061012d0037b404b0012b000ba404a8000b501290037b40035404a0012700498000f50125000924049000f4d012300488000f50121000924048000f4d0005100061011f000864047800ded011d000354009e4042b40470011b004db40468000310119004600117004580115004af404500029901130044800299000c5002b9011100440002b90120d002e9010f00438010d000ae404300120d002e9000b50136d010b0042801090042001070041800299000c5002b9010500410002b90120d002e9010300408002e9000b50136d00031000d501010040000ff003f800fd00039404af4003d403f000fb003e8000e500f9004af4003d40092403e000f7003d8000e500f5004574003d403d000f30003d4009240483404db403c800f1003c000ef003b8000e5012bd000f500ed003b0000f50024900eb003a8000f500e9003a0000f5002490120d0136d0003100e70039800e50003d403900120d00e30007a404db4038800e100380000f500df0048340378001e90136d000310021900dd0037000db00031403680024900d90048340360000b50136d00d70035800d500031403500024900d30048340348000b50136d0003100d1003400136d00cf003380136d0003100219000d50027900cd0033000cb00328000f5002b900c9003d3400ba4032000c70031800c50003d400ae4031000f4d002e90003100c30037b40308000d500c10009e4042b4030000bf002f800bd002f000bb00031400ae402e800b9000ae40483400ba402e000b7000ba4002d404db40035402d800b5002d000b3004af4003d402c800b10003d40092402c000af0003d402b8002490120d0136d00ad002b00136d0021900ab002a80136d00a9002a00136d00219000d50027900a70029800a500290000f5002b900a3003d3400ba4028800ded00a1000354028000279010ad009f00278009d00270009b000ae402680120d002e9009900260002e9000b50136d000d500970025800950003d4025000249009300248000f500910009240483404db4024000219008f000354009e40238008d00230002b9008b003d3400ba4022800ded0089000354022000279010ad0001100021000410087002180136d0085002100136d0003100830001d402080027900810042b40200007f004db401f800075007d0009e401f0010ad007b0000440008401e800055000950079001e000061007700035401d80014900750042b401d00073004db401c80071004db4000c401c0000d5006f001b8000d500149006d0042b401b0006b004db401a8000d50069001a0000d50014900670042b4019800011000210004100650019000630000d40015400254018800610001040180005f000154002540178005d0017000065005b0016800021000490004100079000d9001a900590016000095005700158005500150000110002100530014800149005100140001490085d004f0000440138000350005500095004d00130004b0001540025401280049001200006500470011800021000490004100079000d9001a900450011000430010800410005240100003f000524010f400f800011003d0000d4001540025400f0003b000e800055000950039000e0003700019400d800350000840012400104001e400364006a400d0003300025400c80031000c0002f00004400b8000350005500095002d000b0002b000a8000110002100290001540025400a000270009800250000440008400900005500230000e4000c4001a4003240088002100080001f000044000840078001d0000440070000350005500095001b000680019000600001100021001700015400254005800150005000130000440008400480005500110000e4000c4001a40040000f00038000d0000440008400300005500095000b00028000900020000110002100070001540018000390003100050001000030000800011000210001000154000000039000310006d00069000cd000c90017d00179002dd0059d00b1d).1
theorem cv1:Covered 1 (valid 1) (root 1):=by
 apply CP.sound (listBox boxes1) boxes1.length 1 (valid 1) (tree:=tree1)
 · exact listBox_valid boxes1 (valid 1) boxesvalid1
 · decide+kernel
def tree2:Tree:=(CP.decode 14 0x118004500110004300108002e90136d00410003540100003f000f8000f5002e9003d000f0003b0003d400e800390003d40483400ba404db400e00037004db4003540008400d80035000d0000d500021002890033000c8002e9003100035400c000ded002f000b8002d0003d400b000f4d002e9002b00035400a800ded000210029000a24042b4000c40010400a0000a5002700098000a5002500090000a500230008800095002100016400224003a4006e40080001f0007800031000a5001d00070000a5001b00068000a50019000224003a4006e4006000170002940058001500029400500013000294004800089000e9001b9001100040000f00038000d0008e4001d4000c4002940030000b00029400280009000294002000079000d9000700018000a5000500010000a500030001e400080001000294000000079000dd000d90018d00189002ed005ad00b2d).1
theorem cv2:Covered 2 (valid 2) (root 2):=by
 apply CP.sound (listBox boxes2) boxes2.length 2 (valid 2) (tree:=tree2)
 · exact listBox_valid boxes2 (valid 2) boxesvalid2
 · decide+kernel
def tree3:Tree:=(CP.decode 6 0x900020000b500070006e4001800050002d40010001b9000300008000b500010006e40000002ed005ad00b2d).1
theorem cv3:Covered 3 (valid 3) (root 3):=by
 apply CP.sound (listBox boxes3) boxes3.length 3 (valid 3) (tree:=tree3)
 · exact listBox_valid boxes3 (valid 3) boxesvalid3
 · decide+kernel
def tree4:Tree:=(CP.decode 1 0x0).1
theorem cv4:Covered 4 (valid 4) (root 4):=by
 apply CP.sound (listBox boxes4) boxes4.length 4 (valid 4) (tree:=tree4)
 · exact listBox_valid boxes4 (valid 4) boxesvalid4
 · decide+kernel
def tree5:Tree:=(CP.decode 1 0x0).1
theorem cv5:Covered 5 (valid 5) (root 5):=by
 apply CP.sound (listBox boxes5) boxes5.length 5 (valid 5) (tree:=tree5)
 · exact listBox_valid boxes5 (valid 5) boxesvalid5
 · decide+kernel
def tree6:Tree:=(CP.decode 1 0x0).1
theorem cv6:Covered 6 (valid 6) (root 6):=by
 apply CP.sound (listBox boxes6) boxes6.length 6 (valid 6) (tree:=tree6)
 · exact listBox_valid boxes6 (valid 6) boxesvalid6
 · decide+kernel
def tree7:Tree:=(CP.decode 1 0x0).1
theorem cv7:Covered 7 (valid 7) (root 7):=by
 apply CP.sound (listBox boxes7) boxes7.length 7 (valid 7) (tree:=tree7)
 · exact listBox_valid boxes7 (valid 7) boxesvalid7
 · decide+kernel
theorem covered (m:ℕ) (hm:0<m) (hh:m≤7):Covered m (valid m) (root m):=by
 interval_cases m
 · exact cv1
 · exact cv2
 · exact cv3
 · exact cv4
 · exact cv5
 · exact cv6
 · exact cv7

end ADC

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AZW
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF NX
open GZ ME LK
open HI LV BH DR
open FF ZGL ON YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {t y r cap low:ℕ}
theorem from_sources (hLow:2985<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 [Fact (Irreducible P.F)] (hFT:low≤wt AT P.F)
 (S:Source P.F) (hS:Profile S 16 52 354 7 0 1)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤7→PA.Covered m
   (OZ.Valid m low t y r cap) (ADC.root m)):
 P.seeds.card≤cap:=by
 classical
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hST:S.T=354:=hS.2.2.1
 have hs:=ADG P.F S (by rw [hST];omega) P.rdegree hchar
   (by rw [hS.2.2.2.2.1];decide)
 have hpow:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣QC (carrierMap P.F) S.P:=by
   change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS S.P).map (carrierMap P.F)
   simpa only [Source.d,hS.2.2.2.2.1,Nat.zero_add] using hs.2
 have hroot:NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0:=by
   exact Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
 obtain ⟨J,hJ,hJS,hJroot,_⟩:=ADQ
   (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
 obtain ⟨hJne,hm,hms,hJb,hJu,hJt,hJs⟩:=AVL P.F S (by rw [hST];omega) J hJ hJS hJroot
 rw [hS.1] at hJb
 rw [hS.2.1] at hJu
 rw [hS.2.2.1] at hJt
 rw [hS.2.2.2.1] at hJs
 let m:=multiplicity P.F J
 have hn:=_Q15 J
 have horder:1≤order J:=Nat.succ_le_of_lt (hm.trans_le hms)
 have hadm:PA.Admissible m (point J):=
   ⟨hms,horder,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
 have hx:Contains (ADC.root m) (point J):=by
   dsimp only [Contains,ADC.root,point]
   refine ⟨max_le horder hms,hJs,?_,hJb,Nat.zero_le _,hJu,Nat.zero_le _,hJt⟩
   have hh:=hn.2.2.1
   omega
 obtain ⟨a,hvalid,ha⟩:=hcov m hm (hms.trans hJs) (point J) hadm hx
 exact OZ.BLH nodes hI P hFT hLow hcap hid J hJ horder a ha rfl hJne hJroot hvalid

theorem packet_count (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) 3924 59 13) (hFT:3681≤wt AT P.F):
 P.seeds.card≤271000000000000000:=by
 classical
 letI:Fact (Irreducible P.F):=⟨P.irreducible⟩
 rcases VT QE.p0 QE.shape0 97989970 (by decide)
     QE.dimension0 nodes P.u0 P.u1 hI P.F P.irreducible (by change 354<_;omega)
     13 59 3924 (by decide) (by decide) (by decide) ⟨P.r_weight,P.y_weight,P.total_weight⟩
     with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · exact (KY.helper_count QE.p0 nodes P
     (by decide) (by decide) (by decide) (by decide) Q hQ).le.trans (by decide)
 exact from_sources (by decide) nodes hI P hFT S hS (by decide) (by decide+kernel) ADC.covered

end
end AZW

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AWK
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF GZ
open HI FF ZGL
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

open GI AP
def offer:Fin 3→Band:= ![⟨11,70,2307,3276,261994000000000000⟩,⟨12,68,2307,3217,266635000000000000⟩,⟨13,66,2307,3102,265894000000000000⟩]
def sourceIndex:Fin 3→Fin 321:= ![⟨57,by decide⟩,⟨57,by decide⟩,⟨57,by decide⟩]
theorem geometry0:JG.AllGeometry (degrees (sourceIndex ⟨0,by decide⟩)) (offer ⟨0,by decide⟩).T0 (offer ⟨0,by decide⟩).T1 (offer ⟨0,by decide⟩).B (offer ⟨0,by decide⟩).R (offer ⟨0,by decide⟩).count:=by decide+kernel
theorem geometry1:JG.AllGeometry (degrees (sourceIndex ⟨1,by decide⟩)) (offer ⟨1,by decide⟩).T0 (offer ⟨1,by decide⟩).T1 (offer ⟨1,by decide⟩).B (offer ⟨1,by decide⟩).R (offer ⟨1,by decide⟩).count:=by decide+kernel
theorem geometry2:JG.AllGeometry (degrees (sourceIndex ⟨2,by decide⟩)) (offer ⟨2,by decide⟩).T0 (offer ⟨2,by decide⟩).T1 (offer ⟨2,by decide⟩).B (offer ⟨2,by decide⟩).R (offer ⟨2,by decide⟩).count:=by decide+kernel
theorem geometry (i:Fin 3):JG.AllGeometry (degrees (sourceIndex i)) (offer i).T0 (offer i).T1 (offer i).B (offer i).R (offer i).count:=by
 fin_cases i
 · exact geometry0
 · exact geometry1
 · exact geometry2
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
theorem packet_count (i:Fin 3) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) (offer i).T1 (offer i).B (offer i).R)
 (hFT:(offer i).T0≤wt AT P.F):P.seeds.card≤(offer i).count:=by
 have hL:(CN.profile (sourceIndex i)).L<(offer i).T0:=by fin_cases i<;>decide+kernel
 rcases AGF (sourceIndex i) nodes hI P (hL.trans_le hFT) with hs | ⟨SZ,hZ⟩
 · exact hs.le.trans (by fin_cases i<;>decide)
 exact ATV.AKJ (degrees (sourceIndex i))
   (by fin_cases i<;>decide) nodes hI P hFT SZ hZ (by fin_cases i<;>decide)
   (by fin_cases i<;>decide+kernel) (JG.covered _ _ _ _ _ _ (geometry i))

end
end AWK

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace AJP
open DR (Box Contains lower upper)
open HI PA UU ADB
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
abbrev valid (m:ℕ):=BW.Valid m 3681 3910 60 13 274000000000000000

set_option autoImplicit false
open CP

def receiptBox (code:ℕ):Box:=
 let x:=code/8589934592
 ⟨x%4096,x/4096%4096,x/4096^2%4096,x/4096^3%4096,
  x/4096^4%4096,x/4096^5%4096,x/4096^6%4096,x/4096^7%4096⟩
def receiptTest (m code:ℕ):Bool:=
 let a:=receiptBox code
 if code%4=0 then BH.check .native (degrees BW.fallback) a m 3681 3910 60 13 274000000000000000
 else if code%4=1 then decide (LinearValid a 3681 3910 60 13 274000000000000000)
 else if h:code/4%32<21∧code/256%512<321 then
  decide ((CN.profile ⟨code/256%512,h.2⟩).L<3681∧
   BandValid (degrees ⟨code/256%512,h.2⟩) a m 3681 3910 60 13 274000000000000000
     ⟨code/4%32,h.1⟩ (code/128%2=1) (code/131072%65536))
 else false

theorem receipt_sound (m code:ℕ) (h:receiptTest m code=true):valid m (receiptBox code):=by
 unfold receiptTest at h
 split_ifs at h with h0 h1 h2
 · exact Or.inl h
 · exact Or.inr (Or.inl (of_decide_eq_true h))
 · have hh:=of_decide_eq_true h
   exact Or.inr (Or.inr ⟨⟨code/4%32,h2.1⟩,decide (code/128%2=1),⟨code/256%512,h2.2⟩,code/131072%65536,hh.1,hh.2⟩)

def decodeReceipts:ℕ→ℕ→List ℕ
 | 0,_=>[]
 | n+1,c=>c%2^132::decodeReceipts n (c/2^132)
def d1_0:List ℕ:=decodeReceipts 16 0x1800e01800e01200c00800600000000001800e01800e01200c004004000736b6001800e01800e01200c00200200000001001800e01800e00a00400400200000000001800e00c00801801000c00800000000001800e00c00801200c00600600000000001800e00c00801000c00400400000000001800e00c00a00e00c00200200000000001800e00c00800a00400400200000000001800e00600200c00400600200000000000c00800c00801801000c00800000000000c00800c00801200c00600600000000000c00800c00801000c00400400000000000c00a00c00a00e00c00200200000000000c00800c00800a00400400200000000000c00200600200c00400600200000000
theorem hd1_0:d1_0.all (receiptTest 1)=true:=by decide+kernel
def d1_1:List ℕ:=decodeReceipts 16 0x2e01a02e01a01200c00200200000001002e01a02e01a00a00800400400000000002e01a02e01a00a00800200200000001002e01a02e01a00600400200200000000002e01a01800e02001400e00200053606002e01a01800e01200c00800600000000002e01a01800e01200c004004000736b6002e01a01800e01200c00200200000001002e01a01800e00a00400400200000000002e01a00c00801801000c00800000000002e01a00c00801200c00600600000000002e01a00c00801000c00400400000000002e01a00c00a00e00c00200200000000002e01a00c00800a00400400200000000002e01a00600200c00400600200000000001800e01800e02001400e00200053606
theorem hd1_1:d1_1.all (receiptTest 1)=true:=by decide+kernel
def d1_2:List ℕ:=decodeReceipts 16 0x5a03002e01a00a00800200200000001005a03002e01a00600400200200000000005a03001800e02001400e00200053606005a03001800e01200c00800600000000005a03001800e01200c004004000736b6005a03001800e01200c00200200000001005a03001800e00a00400400200000000005a03000c00801801000c00800000000005a03000c00801200c00600600000000005a03000c00801000c00400400000000005a03000c00a00e00c00200200000000005a03000c00800a00400400200000000005a03000600200c00400600200000000002e01a02e01a02001400e00200053606002e01a02e01a01200c00800600073692002e01a02e01a01200c004004000936ca
theorem hd1_2:d1_2.all (receiptTest 1)=true:=by decide+kernel
def d1_3:List ℕ:=decodeReceipts 16 0xb205c03401c00a0080020020000000100b205c03401c0060040020020000000100b205c01a01002001400e00200053a0600b205c01a01001200c008002000736b200b205c01a01000a0040040020000000000b205c00e00a01c01400e00a0000000000b205c00e00a01600e00800200073a0e00b205c00e00a00c0040060020000000000b205c00800601000c0080060000000000b205c00800200c00400400200000000005a03005a03002001400e00200053a06005a03005a03001200c00800200073a0a005a03005a03000a00400400200073a0e005a03002e01a02001400e00200053606005a03002e01a01200c00800200073a2e005a03002e01a00a00800400400000000
theorem hd1_3:d1_3.all (receiptTest 1)=true:=by decide+kernel
def d1_4:List ℕ:=decodeReceipts 16 0x1620b401a01001200c0080060000000001620b401a01001200c004002000736b201620b401a01000a0040040020000000001620b400e00a01c01400e00a0000000001620b400e00a01600e00800200073a0e01620b400e00a00c0040060020000000001620b400800601000c0080060000000001620b400800200c0040040020000000000b205c06803602001400e00200053a0600b205c06803601200400800200053a0a00b205c03401c02001400e00200053a0600b205c03401c01200c00800200073a0e00b208803402a00a00800400400073a0e00b208802801c00a00800400400000000008605c03402a00a00800400400073a0e008605c02801c00a00800400400000000
theorem hd1_4:d1_4.all (receiptTest 1)=true:=by decide+kernel
def d1_5:List ℕ:=decodeReceipts 16 0x2c416400e00a00c0040060020000000002c416400800601000c0080060000000002c416400800200c0040040020000000001620b406803602001400e00200053f0601620b406803601200400800200073e2a01620b403401c02001400e00200053a0601620b403401c01200c0080060007368e01620b403401c01200c0040040007368e01620b403401c01200c00200200000001016210c03402a00a00800400400073a0e016210c02801c00a00800400400000000010a0b403402a00a00800400400073a0e010a0b402801c00a0080040040000000001620b403401c00a0080020020000000101620b403401c0060040020020000000101620b401a01002001400e00200053a06
theorem hd1_5:d1_5.all (receiptTest 1)=true:=by decide+kernel
def d1_6:List ℕ:=decodeReceipts 16 0x2c416403401c0200140020020000000102c416403401c01200c00800200073e3e02c416403401c00a00800400200073a5202c416403401c0060040020020000000102c416401a01002001400e00a0005368602c421601a01602001c00800600033a1e02c421601a01601a01400800600053a0602c421601401001c01400800600053a06021416401a01002001400800600053a0602c416401a01001e01400400200053a0602c416401a01001200c008002000736ae02c416401a01000a0080040040000000002c416401a01000a0080020020000000102c416401a0100060040020020000000002c416400e00a01c01400e00a00053a0602c416400e00a01600e00800200073a0a
theorem hd1_6:d1_6.all (receiptTest 1)=true:=by decide+kernel
def d1_7:List ℕ:=decodeReceipts 16 0x2c426e03402a02001c00800800053a22026c21603402a02001c00800800033e1e02c426e03402a02001c00600600053a22026c21603402a02001c00600600033a1e02c421603402a01a0140080080005368602c426e03402a01a01400600600053a3a026c21603402a01a01400600600053a0602c421602801c02001c00800600033e1e02c421602801c01a01400800600053e06021416403401c02001400800600053a0602c426e03402a02001c00400400053a22026c21603402a02001c00400400033a1e02c421603402a01a01400400400053f0602c421602801c02001c00400400033e1e02c421602801c01a01400400400053a06021416403401c02001400400400053a06
theorem hd1_7:d1_7.all (receiptTest 1)=true:=by decide+kernel
def d1_8:List ℕ:=decodeReceipts 16 0x2c421604e03601200c00800600053e06021416406803601200c00800600053a0602c426e06805001201000400400053a3a026c21606805001201000400400053e0602c426e06805000e00c00400400053a3a026c21606805000e00c00400400053a0602c421604e03601200c00400400053e06021416406803601200c00400400053a0602c416406803601200c0020020000000102c416406803600a00400400200053a0602c421603402a02001c00e00e0005368602c426e03402a02001c00c00a00053a22026c21603402a02001c00c00a00033f1e02c421603402a01a01400c00a0005368602c421602801c02001400e00a00053686021416403401c02001400e00a00053e06
theorem hd1_8:d1_8.all (receiptTest 1)=true:=by decide+kernel
def d1_9:List ℕ:=decodeReceipts 16 0x2c421604e03601a0140020020000000102141be06805e02001c00200200033a1a02141ea05c05802001c00200200053a1a02141ea05605002002000200200053a0202141ea05605001e01c00200200033f1e01e81be05c05002001c00200200053e4e01bc16406805002001c00200200053a4e021416406805001a01400200200053f4e021416404e03602001400200200073f4e02c426e06805001201000800800053a3a026c21606805e01201000800800033a1a026c21605c05001201000800800053a0602c426e06805001201000600600053a3a026c21606805001201000600600053f0602c426e06805000e00c00600600053a3a026c21606805000e00c00600600053a06
theorem hd1_9:d1_9.all (receiptTest 1)=true:=by decide+kernel
def _GAM:List ℕ:=decodeReceipts 16 0x2c426e06805001a01400200200053e3a026c21606805e01a01800200200033a1a026c24205c05801a01800200200053a1a026c24205605001a01800200200000001024021605c05801a01800200200033e1e024021605605001a01800200200000001026c21606805e01601400200200033a1a026c21605c0500160140020020000000102c426e04e04402001c00200200053a22026c24204e04a02002000200200053a02026c24204e04a01e01c00200200000001026c24204804402001c00200200000001024021604e04a02002000200200053a02024021604e04a01e01c00200200000001024021604804402001c0020020000000102c421604203602001c00200200000001
theorem hd1_10:_GAM.all (receiptTest 1)=true:=by decide+kernel
def _GAX:List ℕ:=decodeReceipts 16 0x26c21604203601a01400400400053a0602141be06805e02001c00400400033a1a02141ea05c05802001c00400400053a1a02141ea05605002002000400400053a0202141ea05605001e01c00400400053f4e01e81be05c05002001c00400400053e4e01bc16406805002001c00400400053a4e021416406805001a01400400400053f4e02141ea04e04a02002000400400053a0202141ea04e04a01e01c00400400053e0602141ea04804402001c00400400053f0601e81be04e04402001c00400400053e0602141be04203602001c00400400053e0601bc16404e03602001c00400400053a06021416404e03601a01400400400053a0602c421606805002001c00200200053f1a
theorem hd1_11:_GAX.all (receiptTest 1)=true:=by decide+kernel
def _GBF:List ℕ:=decodeReceipts 16 0x24022c04e04a01c01c00400400053f06022a21604e04a01e01c00400400033e1e024021604804402002000400400053a02024021604804401e01c00400400033e1e02c426e04203602001c00400400053a22026c24204203e02002000400400053a02026c24204203e01e01c00400400033e1e024021604203e02001c00400400033e1e026c21603c03602001c00400400033e1e02c426e04e04401a01400400400053a3a026c24204e04a01a01a00400400033a1e026c24204e04a01801800400400053e06026c24204804401a01800400400053e06024021604e04401a01800400400053e06026c21604e04401601400400400053a0602c426e04203601a01400400400053a3a
theorem hd1_12:_GBF.all (receiptTest 1)=true:=by decide+kernel
def _GBG:List ℕ:=decodeReceipts 16 0x24021605605001a01800400400053f06026c21606805e01601400400400033a1a026c24205c05801601400400400033a1e026c24205605001601400400400053e06024021605c05001601400400400053a0602c426e04e04402001c00400400053a22026c24204e04a02002000400400053a02026c25804e04a01e01c00400400053a22025624204e04a01e01e00400400053a02025624204e04a01c01c00400400033e1e026c24204804402002000400400053a02026c25804804401e01e00400400053a02026c25804804401c01c00400400033e1e025624204804401e01c00400400033e1e024021604e04a02002000400400053a02024022c04e04a01e01e00400400033a1a
theorem hd1_13:_GBG.all (receiptTest 1)=true:=by decide+kernel
def _GBH:List ℕ:=decodeReceipts 16 0x2141ea04e04a02002000600600053a0202141ea04e04a01e01c00600600053f0602141ea04804402001c00600600033e1e01e81be04e04402001c00600600053e0602141be04203602001c00800600053f0601bc16404e03602001c00800600053a06021416404e03601a01400800600053a0602c426e06805002001c00400400053a02026c21606805002001c00400400053a1a02c426e06805001a01400400400053e3a026c21606805e01a01800400400033a1a026c24205c05801a01800400400053a1a026c24205605001a01a00400400033f1e026c24205605401801800400400033a1e026c24205205001801800400400053f06024021605c05801a01800400400033f1e
theorem hd1_14:_GBH.all (receiptTest 1)=true:=by decide+kernel
def _GBI:List ℕ:=decodeReceipts 16 0x21420005605401e01c00600600053a1a021420005205001e01c00600600033f1e01fe1ea05605001e01c00600600033f1e01e81be05c05002001c00600600053e4e01bc16406805002001c00800600053e4e02141be06805e01a01800800800033a1a02141be05c05001a01800800800053f0602141be06805001601400800800053e0602141be06805e01a01800600600033a1a02141be05c05001a01800600600053e0602141be06805001601400600600053e0601bc16406805001a01400800600053a0602141ea04e04a02002000800800053a0202141ea04e04a01e01c00800800033e1e02141ea04804402001c00800800033f1e01e81be04e04402001c00800800053f06
theorem hd1_15:_GBI.all (receiptTest 1)=true:=by decide+kernel
def _GBJ:List ℕ:=decodeReceipts 16 0x26c21604e04401601400600600053a0602c426e04203601a01400800800053a3a026c21604203601a01400800800053e0602c426e04203601a01400600600053a3a026c21604203601a01400600600053e0602141be06805e02001c00800800033a1a02141ea05c05802001c00800800053a1a02141ea05605002002000800800053a02021420005605401e01c00800800053a1a021420005205001e01e00800800033a1a021420005205001c01c00800800053f0601fe1ea05605001e01c00800800053e4e01e81be05c05002001c00800800053f4e02141be06805e02001c00600600033a1a02141ea05c05802001c00600600053a1a02141ea05605002002000600600053a02
theorem hd1_16:_GBJ.all (receiptTest 1)=true:=by decide+kernel
def _GBK:List ℕ:=decodeReceipts 16 0x26c24204203e02002000600600053a02026c24204203e01e01c00600600033f1e024021604203e02001c00600600033f1e026c21603c03602001c00600600033f1e02c426e04e04401a01400800800053a3a026c24204e04a01a01a00800800033e1e026c24204e04a01801800800800053f06026c24204804401a01a00800800033a1e026c24204804401801800800800053e06024021604e04401a01800800800053e06026c21604e04401601400800800053a0602c426e04e04401a01400600600053a3a026c24204e04a01a01a00600600033e1e026c24204e04a01801800600600053e06026c24204804401a01800600600053f06024021604e04401a01800600600053e06
theorem hd1_17:_GBK.all (receiptTest 1)=true:=by decide+kernel
def _GBL:List ℕ:=decodeReceipts 16 0x24022c04e04a01e01e00600600033a1a024022c04e04a01c01c00600600033e1e022a21604e04a01e01c00600600033f1e024021604804402002000600600053a02024021604804401e01c00600600033e1e02c426e04203602001c00800800053a22026c24204203e02002000800800053a02026c25804203e01e01e00800800053a02026c25804203e01c01c00800800033a1e025624204203e01e01c00800800033e1e024021604203e02002000800800053a02024021604203e01e01c00800800033e1e026c24203c03602002000800800053a02026c24203c03601e01c00800800033e1e024021603c03602001c00800800033e1e02c426e04203602001c00600600053a22
theorem hd1_18:_GBL.all (receiptTest 1)=true:=by decide+kernel
def _GBM:List ℕ:=decodeReceipts 16 0x24022c04e04a01c01c00800800033e1e022a21604e04a01e01e00800800033a1a022a21604e04a01c01c00800800053f06024021604804402002000800800053a02024021604804401e01c00800800033f1e02c426e04e04402001c00600600053a22026c24204e04a02002000600600053a02026c25804e04a01e01c00600600053a22025624204e04a01e01e00600600053a02025624204e04a01c01c00600600033f1e026c24204804402002000600600053a02026c25804804401e01e00600600053a02026c25804804401c01c00600600033e1e025624204804401e01e00600600033a1a025624204804401c01c00600600033a1e024021604e04a02002000600600053a02
theorem hd1_19:_GBM.all (receiptTest 1)=true:=by decide+kernel
def _GBO:List ℕ:=decodeReceipts 16 0x26c24205c05801601400600600033a1e026c24205605001601400600600053e06024021605c05001601400600600053e0602c426e04e04402001c00800800053a22026c24204e04a02002000800800053a02026c25804e04a01e01c00800800053a22025624204e04a01e01e00800800053a02025624204e04e01c01c00800800053a1a025624204c04a01c01c00800800033f1e026c24204804402002000800800053a02026c25804804401e01e00800800053a02026c25804804401c01c00800800033f1e025624204804401e01e00800800033a1a025624204804401c01c00800800033e1e024021604e04a02002000800800053a02024022c04e04a01e01e00800800033a1a
theorem hd1_20:_GBO.all (receiptTest 1)=true:=by decide+kernel
def _GBP:List ℕ:=decodeReceipts 16 0x24021605c05001601400800800053e0602c426e06805001a01400600600053f3a026c21606805e01a01800600600033a1a026c24205c05801a01800600600053a1a026c25805605401a01a00600600053a1a025624205605401a01a00600600033f1e026c24205205001a01a00600600033e1e026c24205605401801800600600033e1e026c26405205001801800600600053a3a026225805205001801800600600053f06025624205205001801800600600053e06024021605c05801a01a00600600053a1a024021605c05801801800600600053f06024021605605001a01a00600600033e1e024021605605001801800600600053e06026c21606805e01601400600600033a1a
theorem hd1_21:_GBP.all (receiptTest 1)=true:=by decide+kernel
def _GBQ:List ℕ:=decodeReceipts 16 0x24c24205605401a01a00800800033f1e026c26405205001a01a00800800053a3a026225805205001a01a00800800033f1e025624205205001a01a00800800033e1e026c24205605401801800800800033e1e026c26405205001801800800800053a3a026225805205201801800800800053a1e026225805005001801800800800053f06025624205205001801800800800053f06024021605c05801a01a00800800053a1a024021605c05801801800800800033e1e024021605605001a01a00800800033e1e024021605605001801800800800053e06026c21606805e01601400800800033a1a026c24205c05801601400800800033e1e026c24205605001601400800800053f06
theorem hd1_22:_GBQ.all (receiptTest 1)=true:=by decide+kernel
def _GBR:List ℕ:=decodeReceipts 16 0x1e81be04e04402001c00a00a00053f2602141be04203602001c00e00e0005368602141be04203602001c00c00a00033f1e01bc16404e03602001c00e00a00053e06021416404e03601a01400c00a00053a0602c426e06805002001c00800800053e02026c21606805002001c00800800053a1a02c426e06805002001c00600600053e02026c21606805002001c00600600053a1a02c426e06805e01a01800800800053a0202c426e05c05001a01800800800053e3a02c426e06805001601400800800053a3a026c21606805e01a01800800800033a1a026c24205c05801a01800800800053a1a026c25805605401a01a00800800053a1a025624e05605401a01a00800800053a1a
theorem hd1_23:_GBR.all (receiptTest 1)=true:=by decide+kernel
def _GBS:List ℕ:=decodeReceipts 16 0x2141be06805e01a01800c00a00033a1a02141be05c05001a01800c00a00053f4e02141be06805001601400a00a00053f0601bc16406805001a01400c00a00053e0602141be04e04402001c00e00e0005368602141ea04e04a02002000c00c00053a02021420004e04a01e01e00c00c00033a1a021420004e04a01c01c00c00c00053f0601fe1ea04e04a01e01c00c00c00033f1e02141ea04804402002000c00c00053a0202141ea04804401e01c00c00c0005368601e81be04e04402001c00c00c00053e4e02141ea04e04a02002000a00a00053a0202141ea04e04a01e01c00a00a00033f1e02141ea04804402002000a00a00053a0202141ea04804401e01c00a00a00053f06
theorem hd1_24:_GBS.all (receiptTest 1)=true:=by decide+kernel
def _GBT:List ℕ:=decodeReceipts 16 0x21420005605401e01c00c00c00053a1a021420005205001e01e00c00c00033a1a021420005205001c01c00c00c0005368601fe1ea05605401e01c00c00c00053a1a01fe1ea05205001e01c00c00c00053e4e01e81be05c05802001c00c00c00053a1a01e81be05605002001c00c00c00053f4e02141ea05c05802001c00a00a00053a1a02141ea05605002002000a00a00053a02021420005605401e01c00a00a00053a1a021420005205001e01e00a00a00033a1a021420005205001c01c00a00a00033e1e01fe1ea05605001e01c00a00a00053f4e01e81be05c05802001c00a00a00053a1a01e81be05605002001c00a00a00053e4e01bc16406805002001c00e00a00053f4e
theorem hd1_25:_GBT.all (receiptTest 1)=true:=by decide+kernel
def _GBU:List ℕ:=decodeReceipts 16 0x26c21603c03602001c00c00c00053686026c24203c03602002000a00a00053a02026c24203c03601e01c00a00a00033e1e024021603c03602001c00a00a00033e1e02c426e04e04401a01400c00a00053a3a026c21604e04401a01800c00c00053686026c24204e04a01a01a00a00a00033f1e026c24204e04a01801800a00a00053686026c24204804401a01800a00a00053686024021604e04401a01800a00a00053f06026c21604e04401601400a00a00053e0602c421604203601a01400c00a0005368602141be06805002001c00e00e00033a1a02141be06805e02001c00c00a00033a1a02141ea05c05802001c00c00c00053a1a02141ea05605002002000c00c00053a02
theorem hd1_26:_GBU.all (receiptTest 1)=true:=by decide+kernel
def _GBV:List ℕ:=decodeReceipts 16 0x24022c04e04a01c01c00a00a00033f1e022a21604e04a01e01e00a00a00033a1a022a21604e04a01c01c00a00a00033e1e024021604804402002000a00a00053a02024022c04804401e01e00a00a00033a1a024022c04804401c01c00a00a00033e1e022a21604804401e01c00a00a00033e1e02c421604203602001c00e00e0005368602c426e04203602001c00c00a00053a22026c21604203e02001c00c00c00053686026c24204203e02002000a00a00053a02026c25804203e01e01e00a00a00053a02026c25804203e01c01c00a00a00053686025624204203e01e01c00a00a00033f1e024021604203e02002000a00a00053a02024021604203e01e01c00a00a00033e1e
theorem hd1_27:_GBV.all (receiptTest 1)=true:=by decide+kernel
def _GBW:List ℕ:=decodeReceipts 16 0x26c24204e04a02002000a00a00053a02026c25804e04a01e01c00a00a00053a22025624204e04a01e01e00a00a00053a02025624204e04e01c01c00a00a00053a1a025624e04c04c01c01c00a00a00053a1a025624e04a04a01c01c00a00a00033f1e024c24204c04a01c01c00a00a00033f1e026c24204804402002000a00a00053a02026c25804804401e01e00a00a00053a02026c26404804801c01c00a00a00053a22026225804804801c01c00a00a00033f1e026c25804604401c01c00a00a00033f1e025624204804401e01e00a00a00033a1a025624204804401c01c00a00a00033e1e024021604e04a02002000a00a00053a02024022c04e04a01e01e00a00a00033a1a
theorem hd1_28:_GBW.all (receiptTest 1)=true:=by decide+kernel
def _GBX:List ℕ:=decodeReceipts 16 0x24021605c05001601400a00a00053e0602c421604e04402001c00e00e0005368602c426e04e04402001c00c00a00053a22026c24204e04a02002000c00c00053a02026c25804e04a01e01c00c00c00053a22025624204e04a01e01e00c00c00053a02025624204e04a01c01c00c00c00053686026c24204804402002000c00c00053a02026c24204804401e01c00c00c00053686024021604e04a02002000c00c00053a02024022c04e04a01e01e00c00c00033a1a024022c04e04a01c01c00c00c00053686022a21604e04a01e01e00c00c00033a1a022a21604e04a01c01c00c00c00053686024021604804402002000c00c00053a02024021604804401e01c00c00c00053686
theorem hd1_29:_GBX.all (receiptTest 1)=true:=by decide+kernel
def _GBZ:List ℕ:=decodeReceipts 16 0x26225e05205201a01a00a00a00053a3a025c25805205201a01a00a00a00033f1e026225805005001a01a00a00a00033f1e025624205205001a01a00a00a00033f1e026c24205605401801800a00a00033f1e026c26405205001801800a00a00053a3a026225805205201801800a00a00053e1e026225805005001801800a00a00053686025624205205001801800a00a00053686024021605c05801a01a00a00a00053a1a024021605c05801801800a00a00033e1e024021605605001a01a00a00a00033f1e024021605605001801800a00a00053f06026c21606805e01601400a00a00033a1a026c24205c05801601400a00a00033e1e026c24205605001601400a00a00053686
theorem hd1_30:_GBZ.all (receiptTest 1)=true:=by decide+kernel
def _GCA:List ℕ:=decodeReceipts 16 0x2c426e06805002001c00c00a00053f02026c21606805002001c00c00a00053a1a02c426e06805e01a01800c00a00053a0202c426e05c05001a01800c00a00053e3a02c426e06805001601400a00a00053e3a026c21606805e01a01800c00a00033a1a026c24205c05801a01800c00c00053a1a026c24205605001a01800c00c00053686024021605c05801a01800c00c00053a1a024021605605001a01800c00c00053686026c24205c05801a01800a00a00053a1a026c25805605401a01a00a00a00053a1a025624e05605401a01a00a00a00053a1a024c24205605601a01a00a00a00053a1a024c24205405401a01a00a00a00033f1e026c26405205001a01a00a00a00053a3a
theorem hd1_31:_GCA.all (receiptTest 1)=true:=by decide+kernel
def _GCB:List ℕ:=decodeReceipts 2 0x2c426e06805002001c00e00e00053f02026c21606805002001c00e00e00033e1a
theorem hd1_32:_GCB.all (receiptTest 1)=true:=by decide+kernel
def codes1:List ℕ:=d1_0++d1_1++d1_2++d1_3++d1_4++d1_5++d1_6++d1_7++d1_8++d1_9++_GAM++_GAX++_GBF++_GBG++_GBH++_GBI++_GBJ++_GBK++_GBL++_GBM++_GBO++_GBP++_GBQ++_GBR++_GBS++_GBT++_GBU++_GBV++_GBW++_GBX++_GBZ++_GCA++_GCB
def boxes1:List Box:=codes1.map receiptBox
theorem boxesvalid1: ∀a∈boxes1,valid 1 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes1.all (receiptTest 1)=true:=by
  simp only [codes1,List.all_append,hd1_0,hd1_1,hd1_2,hd1_3,hd1_4,hd1_5,hd1_6,hd1_7,hd1_8,hd1_9,hd1_10,hd1_11,hd1_12,hd1_13,hd1_14,hd1_15,hd1_16,hd1_17,hd1_18,hd1_19,hd1_20,hd1_21,hd1_22,hd1_23,hd1_24,hd1_25,hd1_26,hd1_27,hd1_28,hd1_29,hd1_30,hd1_31,hd1_32,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d2_0:List ℕ:=decodeReceipts 16 0x5c03205c03201401000a00800000000005c03205c03201401000600400073a0a005c03205c03200e00800600400000000005c03203001c02001600e00400053a0a005c03203001c01400800a00400000000005c03201a01002001600e00400053a0a005c03201a01001400800a00400000000005c03200e00401c00800e00400000000003001c03001c02001600e00400053a0a003001c03001c01400800a00400000000003001c01a01002001600e00400053a0a003001c01a01001400800a00400000000003001c00e00401c00800e00400000000001a01001a01002001600e00400053a0a001a01001a01001400800a00400000000001a00400e00401c00800e00400000000
theorem hd2_0:d2_0.all (receiptTest 2)=true:=by decide+kernel
def d2_1:List ℕ:=decodeReceipts 16 0x1640b6068038014008006004000736c601640b603601e02001600e00400053a0601640b603601e01400800a0040000000001640b601c01202001600e00400053a0a01640b601c01201400800a0040000000001640b601000c01e01400e0040005368e01640b601000c0120080080040000000001640b600a00401400800a0040000000000b405e06803802001600e00400053a0600b405e06803801400800a004000736c600b405e03601e02001600e00400053a0600b405e03601e01400800a0040000000000b405e01c01202001600e00400053a0a00b405e01c01201400800a0040000000000b405e01000401e00800e00400000000005c03205c03202001600e00400053a06
theorem hd2_1:d2_1.all (receiptTest 2)=true:=by decide+kernel
def d2_2:List ℕ:=decodeReceipts 16 0x2141ea05c05202002000400400033a1602141ea05c05201e01c0040040005368601e81be05c05202001c00400400053e4e02141be06805201a0160040040005368601bc16606805202001600400400053a4e02141660500380200160060040005368602c416606803801400800a004000736c202c416603601e02001600e0040005368602c416603601e01400800a0040000000002c416601c01202001600e0040005368602c416601c01201400800a0040000000002c416601000c01e01400e0040005368a02c416601000c0120080080040000000002c416600a00401400800a0040000000001640b606803802001600e00400053f0601640b606803801401000a0080005368a
theorem hd2_2:d2_2.all (receiptTest 2)=true:=by decide+kernel
def d2_3:List ℕ:=decodeReceipts 16 0x26c21606805e02001c00400400033a1a026c24205c05202002000400400053a02026c24205c05801e01c00400400053a1a026c24205605201e01c00400400053686024021605c05202002000400400053a02024021605c05201e01c0040040005368602c426e06805201a01600400400053e3a026c21606805201a0160040040005368602c42160500380200160060060005368602c421605003802001c0040040003369e02c421605003801a0160040040005368602141be06805e02001c00600600033a1a02141be05c05202001c0060060005368602141be06805201a0160060060005368601bc166068052020016006006000536a602141be06805e02001c00400400033a1a
theorem hd2_3:d2_3.all (receiptTest 2)=true:=by decide+kernel
def d2_4:List ℕ:=decodeReceipts 10 0x2c416606803802001600e00a0005368602c41660680380200160080080005368602c426e06805e02001c00600600053e0202c426e05c05202001c0060060003369e026c21606805e02001c00600600033a1a026c21605c05202001c0060060005368602c421606805201a0160060060005368602c426e06805e02001c00400400053a0202c426e05c05202002000400400053a0202c426e05c05201e01c004004000536ba
theorem hd2_4:d2_4.all (receiptTest 2)=true:=by decide+kernel
def codes2:List ℕ:=d2_0++d2_1++d2_2++d2_3++d2_4
def boxes2:List Box:=codes2.map receiptBox
theorem boxesvalid2: ∀a∈boxes2,valid 2 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes2.all (receiptTest 2)=true:=by
  simp only [codes2,List.all_append,hd2_0,hd2_1,hd2_2,hd2_3,hd2_4,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d3_0:List ℕ:=decodeReceipts 10 0x2c416606803802001800e0060005368602c416606803801600c00a0060000000002c416603600602000c00e0060000000001640b606803802001800e00600053f0601640b606803801600c00a0060000000001640b603600602000c00e0060000000000b405e06803802001800e00600053a0600b405e06803801600c00a0060000000000b405e03600602000c00e00600000000005c00605c00602000c00e00600000000
theorem hd3_0:d3_0.all (receiptTest 3)=true:=by decide+kernel
def codes3:List ℕ:=d3_0
def boxes3:List Box:=codes3.map receiptBox
theorem boxesvalid3: ∀a∈boxes3,valid 3 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes3.all (receiptTest 3)=true:=by
  simp only [codes3,List.all_append,hd3_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d4_0:List ℕ:=decodeReceipts 1 0x2c400806800802001000e00800000000
theorem hd4_0:d4_0.all (receiptTest 4)=true:=by decide+kernel
def codes4:List ℕ:=d4_0
def boxes4:List Box:=codes4.map receiptBox
theorem boxesvalid4: ∀a∈boxes4,valid 4 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes4.all (receiptTest 4)=true:=by
  simp only [codes4,List.all_append,hd4_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d5_0:List ℕ:=decodeReceipts 1 0x2c400a06800a02001400e00a00000000
theorem hd5_0:d5_0.all (receiptTest 5)=true:=by decide+kernel
def codes5:List ℕ:=d5_0
def boxes5:List Box:=codes5.map receiptBox
theorem boxesvalid5: ∀a∈boxes5,valid 5 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes5.all (receiptTest 5)=true:=by
  simp only [codes5,List.all_append,hd5_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d6_0:List ℕ:=decodeReceipts 1 0x2c400c06800c02001800e00c00000000
theorem hd6_0:d6_0.all (receiptTest 6)=true:=by decide+kernel
def codes6:List ℕ:=d6_0
def boxes6:List Box:=codes6.map receiptBox
theorem boxesvalid6: ∀a∈boxes6,valid 6 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes6.all (receiptTest 6)=true:=by
  simp only [codes6,List.all_append,hd6_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def d7_0:List ℕ:=decodeReceipts 1 0x2c400e06800e02001c00e00e00000000
theorem hd7_0:d7_0.all (receiptTest 7)=true:=by decide+kernel
def codes7:List ℕ:=d7_0
def boxes7:List Box:=codes7.map receiptBox
theorem boxesvalid7: ∀a∈boxes7,valid 7 a:=by
 intro a ha
 obtain ⟨code,hc,rfl⟩:=List.mem_map.mp ha
 apply receipt_sound
 have hh:codes7.all (receiptTest 7)=true:=by
  simp only [codes7,List.all_append,hd7_0,Bool.and_self]
 exact List.all_eq_true.mp hh code hc
def root (m:ℕ):Box:=⟨max 1 m,7,2*max 1 m,16,0,52,0,354⟩
def tree1:Tree:=(CP.decode 20 0x201008000136d01ff007f80136d0006101fd007f0002e901fb0002d407e801f9007e0002b901f7007d8002b90120d01f5007d001f3007c801f1000aa4049b404af407c001ef007b8012ed01ed000a2404c7407b0012bd0029901eb007a801e9007a0002890131d01e7004af400a640031400ae4079801e5000314079001e300031400ae4048340014400ba4078801e100780002b901df00483400ba4002d404db400354077801dd0077001db0076801d900039404af4003d4076001d70003d400924075801d500750000e501d300748000e50115d000f501d100740000f5002490120d01cf0073801cd0073001cb007280025901c90049b4009a40039404af4003d4072001c70071801c5004c74071000239000e501c300708000e5012bd000f50024901c10070001bf00039406f801bd00039404574003d406f001bb006e8000e501b9004574003d400924048340014404db40018406e001b7006d801b5006d001b300039406c8012bd000f501b1006c0000f50120d0005101af006b801ad0003d406b00120d00051001e90136d000610021901ab006a801a9006a0000c501a700092406980120d0005101a50002d404db4069000219000d50027901a30068801a100680019f00678019d00039400a640670019b000a6403ff4003d400ae406680199000ae403d340660019700658019500650000e5002990193003ff4003d400ae406480191000ae403d340014400ba400184064000ded018f00638002e9018d0002d4063000ded000d5018b00628018900620000e50187003ff4003d4061801850003d400924061000f4d018300608000f5018100600000f500249017f003d34001440018405f8017d0001840086405f000ded017b000354009e4042b405e80179004db405e00177004db4000c405d80175000ba405d0000b50173005c80171005c0016f0049b404af405b8016d004c7405b0012bd00299016b005a80169005a0002890131d0167004af400a640031400ae4059801650003140590016300031400ae40483400ba40588016100580002b9015f00483400ba4002d404db40578015d00570015b00568012bd0159000a6405600157005580131d0155004af400a640031400ae4055001530003140548015100031400ae40483400ba40540014f00538002b9014d00483400ba4002d404db4000c4003540530014b0052801490052001470009a40039404af4003d40518014500510000e5014300508000e5012bd000f500249014100500013f00039404f8013d00039404574003d404f0013b0003d4009240483404db404e80139004e00137004d8000e5012bd000f50135004d0013300039404c8013100039404af4003d40092404c0012f004b8000e5012d004574003d404b0012b0003d4009240483404db4000c404a80129004a001270003940498012bd000f5012500490000f50120d012300488000f50121004834007a404db40480011f00478000f5011d0048340470001e90136d0003100219011b004680119000314046001170003140092404580120d01150002d404db40450011300448000c5011100092404400120d010f0002d404db4000c40438010d004db40430010b004db4000c40086400354009e40428010900420010700418010500039400a64041000ffd000f5002b90103003d3400ba4040801010040000ff003f80029900fd003ff4003d400ae403f000f4d002e90003100fb0037b403e800f9000ba403e0000b500f7003d8002e900f50002d4000c403d000ded000d500f3003c8000f500f100092403c000f4d00ef003b8000f500ed00092403b000f4d0003100eb00086403a800ded00e9000354009e4042b403a000e7004db4039800e50039000e30038800e1000a640031400ae4038000df000ae40483400ba4037800dd00370002b900db00483400ba4002d404db400354036800d90036000d700358000e5012bd000f500d50035000d30003940348012bd000f50024900d10034000cf00039403380115d000f500cd00330000f5002490120d0136d00cb0032800c90003d403200120d00c70007a404db400864031800c500310000c500c300092403080120d00c10002d404db4030000bf004db40086400354009e402f800bd002f000bb0003d400ae402e800f4d002e900b90037b402e0000d500b7002d8000f500b500092402d000f4d00b300086402c800ded00b1000354009e4042b402c000af002b800ad002b0002b900ab002a8002b90120d002e900a9002a0002e9000b50136d000d500a70029800a50003d402900024900a300288000f500a10009240483404db4028000219009f000354009e40278009d00270009b0003d400ae4026800f4d002e900990037b40260000d500970009e4042b40004400084001040258009500250002e90136d0093002480136d000310091002400136d00075008f0009e40238010ad008d002300136d008b002280136d0007500890009e40220010ad008700004400084021800055000950085002100083004db4001840208000d500810005240200010ad007f001f80136d007d001f00136d00031007b001e80079004db4000c40035401e000770003540052401d8010ad0075001d00136d007300035401c800710003540052401c0010ad006f000044000840010401b8006d001b0000350005500095006b001a8006900035401a0000a900670042b40198000210004100650019000630000440188000350005500095006100180005f0001940178005d0000840012400104001e400364006a40170005b000254016800590016000570000440008401580055000524015000530005240217401480001100510000d400154002540140004f0013800021004d000154002540130004b001280006500490012000021000490004100079000d9001a90047001180009500450011000430010800149004100100001490043d003f00004400f8000350005500095003d000f0003b0001540025400e80039000e0000650037000d800021000490004100079000d9001a90035000d000330001540025400c80031000c0002f00004400b8000350005500095002d000b0002b000a8000110002100290001540025400a000270009800250000440008400900005500230000e4000c4001a4003240088002100080001f000044000840078001d0000440070000350005500095001b000680019000600001100021001700015400254005800150005000130000440008400480005500110000e4000c4001a40040000f00038000d0000440008400300005500095000b00028000900020000110002100070001540018000390003100050001000030000800011000210001000154000000039000310006d00069000cd000c90017d00179002dd0059d00b1d).1
theorem cv1:Covered 1 (valid 1) (root 1):=by
 apply CP.sound (listBox boxes1) boxes1.length 1 (valid 1) (tree:=tree1)
 · exact listBox_valid boxes1 (valid 1) boxesvalid1
 · decide+kernel
def tree2:Tree:=(CP.decode 15 0x4900120004700118002e9004500110002e90136d00430003540108004100100000f5002e9003f000f8003d000f0002b9000f5003b000e8000f50120d002e90136d0039000e00136d000d5000210037000d800350003540008400a2400d00033000ba400c8000d500310037b400c0002f000b8000f5002d003d3400ba400b0000d5002b0037b40008400a800289010ad0003100041002900029400a00027000294009800250002940090002300025400880005900089000e9001b9002100080001f0000c4002940078001d0002940070001b0002940068001900025400600005900089000e9001b9001700058000a5001500050000a5001300048000a50011000224003a4006e40040000f00038000d0001d4000c4002940030000b00029400280009000294002000079000d9000700018000a5000500010000a500030001e400080001000294000000079000dd000d90018d00189002ed005ad00b2d).1
theorem cv2:Covered 2 (valid 2) (root 2):=by
 apply CP.sound (listBox boxes2) boxes2.length 2 (valid 2) (tree:=tree2)
 · exact listBox_valid boxes2 (valid 2) boxesvalid2
 · decide+kernel
def tree3:Tree:=(CP.decode 6 0x900020000b500070006e4001800050002d40010001b9000300008000b500010006e40000002ed005ad00b2d).1
theorem cv3:Covered 3 (valid 3) (root 3):=by
 apply CP.sound (listBox boxes3) boxes3.length 3 (valid 3) (tree:=tree3)
 · exact listBox_valid boxes3 (valid 3) boxesvalid3
 · decide+kernel
def tree4:Tree:=(CP.decode 1 0x0).1
theorem cv4:Covered 4 (valid 4) (root 4):=by
 apply CP.sound (listBox boxes4) boxes4.length 4 (valid 4) (tree:=tree4)
 · exact listBox_valid boxes4 (valid 4) boxesvalid4
 · decide+kernel
def tree5:Tree:=(CP.decode 1 0x0).1
theorem cv5:Covered 5 (valid 5) (root 5):=by
 apply CP.sound (listBox boxes5) boxes5.length 5 (valid 5) (tree:=tree5)
 · exact listBox_valid boxes5 (valid 5) boxesvalid5
 · decide+kernel
def tree6:Tree:=(CP.decode 1 0x0).1
theorem cv6:Covered 6 (valid 6) (root 6):=by
 apply CP.sound (listBox boxes6) boxes6.length 6 (valid 6) (tree:=tree6)
 · exact listBox_valid boxes6 (valid 6) boxesvalid6
 · decide+kernel
def tree7:Tree:=(CP.decode 1 0x0).1
theorem cv7:Covered 7 (valid 7) (root 7):=by
 apply CP.sound (listBox boxes7) boxes7.length 7 (valid 7) (tree:=tree7)
 · exact listBox_valid boxes7 (valid 7) boxesvalid7
 · decide+kernel
theorem covered (m:ℕ) (hm:0<m) (hh:m≤7):Covered m (valid m) (root m):=by
 interval_cases m
 · exact cv1
 · exact cv2
 · exact cv3
 · exact cv4
 · exact cv5
 · exact cv6
 · exact cv7

end AJP

end SubmissionLower
end ProximityPrize
end
section
namespace ProximityPrize.SubmissionLower
namespace BQD
open ProximityPrize.Benchmark
open MvPolynomial RCN095 RCN135 RCN136 RCN156 RCN234
open CW DJ CB
open DC FN BX DP
open DU ER EF
open BD GF NX
open GZ ME LK
open HI LV BH DR
open FF ZGL ON YY
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
variable {K I:Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {t y r cap low:ℕ}
theorem from_sources (hLow:2985<low) (nodes:I ↪ K) (hI:Fintype.card I=262144) (P:Packet (nodes:I→K) t y r)
 [Fact (Irreducible P.F)] (hFT:low≤wt AT P.F)
 (S:Source P.F) (hS:Profile S 16 52 354 7 0 1)
 (hcap:4000000000000000≤cap) (hid:MG t y r≤cap)
 (hcov: ∀m,0<m→m≤7→PA.Covered m
   (BW.Valid m low t y r cap) (AJP.root m)):
 P.seeds.card≤cap:=by
 classical
 have hchar:P.F.degreeOf 2<2130706433:=P.IZ.2.1.trans_lt (by have:=P.rhigh;omega)
 have hST:S.T=354:=hS.2.2.1
 have hs:=ADG P.F S (by rw [hST];omega) P.rdegree hchar
   (by rw [hS.2.2.2.2.1];decide)
 have hpow:(Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣QC (carrierMap P.F) S.P:=by
   change (Polynomial.X-Polynomial.C (ratio (carrierMap P.F) P.F))^1∣(asS S.P).map (carrierMap P.F)
   simpa only [Source.d,hS.2.2.2.2.1,Nat.zero_add] using hs.2
 have hroot:NT (carrierMap P.F) (ratio (carrierMap P.F) P.F) S.P=0:=by
   exact Polynomial.dvd_iff_isRoot.mp (by simpa only [pow_one] using hpow)
 obtain ⟨J,hJ,hJS,hJroot,_⟩:=ADQ
   (NT (carrierMap P.F) (ratio (carrierMap P.F) P.F)) S.P (AHY P.F S) hroot
 obtain ⟨hJne,hm,hms,hJb,hJu,hJt,hJs⟩:=AVL P.F S (by rw [hST];omega) J hJ hJS hJroot
 rw [hS.1] at hJb
 rw [hS.2.1] at hJu
 rw [hS.2.2.1] at hJt
 rw [hS.2.2.2.1] at hJs
 let m:=multiplicity P.F J
 have hn:=_Q15 J
 have horder:1≤order J:=Nat.succ_le_of_lt (hm.trans_le hms)
 have hadm:PA.Admissible m (point J):=
   ⟨hms,horder,hn.2.2.1,hn.2.1,hn.2.2.2,hn.1⟩
 have hx:Contains (AJP.root m) (point J):=by
   dsimp only [Contains,AJP.root,point]
   refine ⟨max_le horder hms,hJs,?_,hJb,Nat.zero_le _,hJu,Nat.zero_le _,hJt⟩
   have hh:=hn.2.2.1
   omega
 obtain ⟨a,hvalid,ha⟩:=hcov m hm (hms.trans hJs) (point J) hadm hx
 exact BW.BLH nodes hI P hFT hLow hcap hid J hJ horder a ha rfl hJne hJroot hvalid

theorem packet_count (nodes:I ↪ K) (hI:Fintype.card I=262144)
 (P:Packet (nodes:I→K) 3910 60 13) (hFT:3681≤wt AT P.F):
 P.seeds.card≤274000000000000000:=by
 classical
 letI:Fact (Irreducible P.F):=⟨P.irreducible⟩
 rcases VT MJ.p0 MJ.shape0 97989970 (by decide)
     MJ.dimension0 nodes P.u0 P.u1 hI P.F P.irreducible (by change 354<_;omega)
     13 60 3910 (by decide) (by decide) (by decide) ⟨P.r_weight,P.y_weight,P.total_weight⟩
     with ⟨Q,hQ⟩ | ⟨S,hS⟩
 · exact (KY.helper_count MJ.p0 nodes P
     (by decide) (by decide) (by decide) (by decide) Q hQ).le.trans (by decide)
 exact from_sources (by decide) nodes hI P hFT S hS (by decide) (by decide+kernel) AJP.covered

end
end BQD

end SubmissionLower
end ProximityPrize
end
