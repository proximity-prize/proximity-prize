import ProximityPrize.SubmissionLower.R6960RescueSourceReceipt0
import ProximityPrize.SubmissionLower.R6962B1HelperFreeSource

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

namespace Lower6962.B1.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open P1_7 (Bank debit)
open Lower6960.HelperSource (WidthGuard cutoffCount surplus)
open Lower6960.RescueSource (fastPhase fastSurplus fastSurplus_eq buffered)

structure B1Checked (t : Bank) (r c v : ℕ) : Prop where
  bank_ok : P3_7_1.BankOK t
  seed_ok : t.shape.U<K1.p
  reserve_ok : 2*r≤t.shape.B
  width_first : WidthGuard t 179808 2360 r
  first : 0<surplus t 179808 2360 r 1 c v
  next : surplus t 179808 2360 r 1 c v ≤ surplus t 179808 2361 r 1 c v

theorem b1_checked_from_values (t : Bank) (r c v : ℕ) (hb : P3_7_1.BankOK t)
    (seed : t.shape.U<K1.p) (reserve : 2*r≤t.shape.B) (width : WidthGuard t 179808 2360 r)
    (slope : t.shape.J<131071-2361) (shift : 2*2361*(r+t.shape.J)<t.shape.m*179808)
    {a b x y : ℕ} (a0 : fastPhase t.shape 179808 2360 r 1 c v 0 = a)
    (a1 : fastPhase t.shape 179808 2360 r 1 c v 1 = b)
    (b0 : fastPhase t.shape 179808 2361 r 1 c v 0 = x)
    (b1 : fastPhase t.shape 179808 2361 r 1 c v 1 = y)
    (pos : 0<((a-b : ℕ) : ℤ)-(debit 2360 t : ℤ))
    (inc : ((a-b : ℕ) : ℤ)-(debit 2360 t : ℤ) ≤ ((x-y : ℕ) : ℤ)-(debit 2361 t : ℤ)) :
    B1Checked t r c v := by
  have h1 := fastSurplus_eq t 2360 r c v (by omega)
    ((Nat.mul_le_mul_right (r+t.shape.J) (by decide : 2*2360≤2*2361)).trans_lt shift)
  have h2 := fastSurplus_eq t 2361 r c v slope shift
  unfold fastSurplus at h1 h2
  rw [a0,a1] at h1
  rw [b0,b1] at h2
  refine ⟨hb,seed,reserve,width,?_,?_⟩
  · rwa [← h1]
  · rwa [← h1, ← h2]

theorem B1Checked.width {t : Bank} {r c v h : ℕ} (cert : B1Checked t r c v)
    (lo : 2360≤h) (hi : h≤2382) : WidthGuard t 179808 h r :=
  Lower6960.HelperSource.width_at_height t 179808 2360 h r lo (by omega) cert.reserve_ok cert.width_first

theorem B1Checked.cutoff_fit {t : Bank} {r c v h : ℕ} (cert : B1Checked t r c v)
    (lo : 2360≤h) (hi : h≤2382) : buffered t h r+2*h*r<t.shape.m*179808 :=
  Lower6960.FreeSource.buffered_fit t 179808 h r (cert.width lo hi)

theorem B1Checked.avoids {t : Bank} {r c v h : ℕ} (cert : B1Checked t r c v)
    {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2360≤h) (hi : h≤2382) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 1≤G.natDegree) (seed : v≤seedDegree G) (excess : G.natDegree+c≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word t.shape (buffered t h r), ¬ G∣Q :=
  Lower6960.HelperSource.crt_avoiding_row Crt word t 179808 r 1 c v (by omega) (by omega) (by decide)
    cert.bank_ok.nodes cert.bank_ok.moment.1 cert.bank_ok.moment.2 cert.seed_ok
    (cert.width lo hi)
    (Lower6960.HelperSource.surplus_positive t 179808 2360 h r 1 c v lo (by omega) cert.first cert.next)
    irr seeded slope seed excess

private def reserves : List ℕ := [0, 1, 2, 3, 4, 6, 9, 13, 19, 28, 40]

def reserve (i : Fin 11) : ℕ := reserves.get ⟨i.val, i.isLt⟩

private def banks0 : List Bank :=
  [
    ⟨⟨960,1335,283,87620⟩,26219672764416,86145454229⟩,
    ⟨⟨1062,1477,313,95389⟩,35473580097536,128959520571⟩,
    ⟨⟨1232,1714,363,99345⟩,55334633209856,233571597436⟩,
    ⟨⟨1316,1830,388,108367⟩,67458666856448,303684814568⟩,
    ⟨⟨1512,2103,446,112911⟩,102300425912320,529424164143⟩,
    ⟨⟨1737,2416,512,128306⟩,154954118725632,921202327390⟩,
    ⟨⟨2075,2886,612,151527⟩,264157279027200,1875530241577⟩,
    ⟨⟨2525,3511,744,182621⟩,475433846702080,4103832483835⟩,
    ⟨⟨2892,4022,853,238837⟩,714712232493056,7069458009600⟩,
    ⟨⟨3572,4969,1053,324838⟩,1345717644558336,16453071033518⟩,
    ⟨⟨4450,6190,1312,450158⟩,2601521007820800,39614339172421⟩
  ]

private def bank0 (i : Fin 11) : Bank := banks0.get ⟨i.val, i.isLt⟩
private def banks1 : List Bank :=
  [
    ⟨⟨960,1335,283,83044⟩,26219672764416,86145454229⟩,
    ⟨⟨1062,1477,313,90414⟩,35473580097536,128959520571⟩,
    ⟨⟨1158,1610,341,98411⟩,45941835694080,181905112010⟩,
    ⟨⟨1316,1830,388,102715⟩,67458666856448,303684814568⟩,
    ⟨⟨1512,2103,446,107024⟩,102300425912320,529424164143⟩,
    ⟨⟨1737,2416,512,121630⟩,154954118725632,921202327390⟩,
    ⟨⟨2075,2886,612,143635⟩,264157279027200,1875530241577⟩,
    ⟨⟨2525,3511,744,173127⟩,475433846702080,4103832483835⟩,
    ⟨⟨2892,4022,853,226398⟩,714712232493056,7069458009600⟩,
    ⟨⟨3572,4969,1053,307952⟩,1345717644558336,16453071033518⟩,
    ⟨⟨4450,6190,1312,426747⟩,2601521007820800,39614339172421⟩
  ]

private def bank1 (i : Fin 11) : Bank := banks1.get ⟨i.val, i.isLt⟩
private def banks2 : List Bank :=
  [
    ⟨⟨902,1254,266,64501⟩,21761818624000,67126395064⟩,
    ⟨⟨998,1388,294,69924⟩,29437072506880,100574709245⟩,
    ⟨⟨1084,1507,319,76536⟩,37677055344640,139622427180⟩,
    ⟨⟨1237,1720,365,78125⟩,56071971930112,237225287687⟩,
    ⟨⟨1335,1856,393,83889⟩,70337008500736,320967029657⟩,
    ⟨⟨1528,2125,450,95143⟩,105450276388864,551268078730⟩,
    ⟨⟨1833,2549,540,111503⟩,181989115428864,1140907389456⟩,
    ⟨⟨2222,3090,655,134136⟩,324185245089792,2463505684704⟩,
    ⟨⟨2255,3136,665,233771⟩,338940010168320,2614168304540⟩,
    ⟨⟨3786,5265,1116,215317⟩,1602148446240768,20739864795191⟩,
    ⟨⟨3916,5447,1155,388707⟩,1773642765041664,23765264612076⟩
  ]

private def bank2 (i : Fin 11) : Bank := banks2.get ⟨i.val, i.isLt⟩
private def banks3 : List Bank :=
  [
    ⟨⟨583,810,174,28950⟩,5947077427200,11844388628⟩,
    ⟨⟨645,897,193,31693⟩,8062750949376,17817574928⟩,
    ⟨⟨748,1039,223,33305⟩,12527232614400,31970332220⟩,
    ⟨⟨800,1112,239,36200⟩,15343613378560,41970326200⟩,
    ⟨⟨919,1277,275,38110⟩,23270612008960,73033428061⟩,
    ⟨⟨1056,1469,316,43461⟩,35282947145728,127673139311⟩,
    ⟨⟨1262,1754,377,51216⟩,60098858975232,259089577144⟩,
    ⟨⟨1535,2134,459,61780⟩,108153919242240,567513111862⟩,
    ⟨⟨1758,2445,526,79949⟩,162480846274560,977606803800⟩,
    ⟨⟨2173,3021,650,107630⟩,306628722950144,2277241812251⟩,
    ⟨⟨2707,3764,809,147358⟩,592120184832000,5480284994149⟩
  ]

private def bank3 (i : Fin 11) : Bank := banks3.get ⟨i.val, i.isLt⟩

private def bankFamilies : List (Fin 11 → Bank) := [bank0, bank1, bank2, bank3]

def bank (rect : Fin 4) (i : Fin 11) : Bank := bankFamilies.get ⟨rect.val, rect.isLt⟩ i

def excess (rect : Fin 4) : ℕ := ([0, 0, 0, 1] : List ℕ).get ⟨rect.val, rect.isLt⟩
def seed (rect : Fin 4) : ℕ := ([1, 2, 7, 1] : List ℕ).get ⟨rect.val, rect.isLt⟩
def jetCap (rect : Fin 4) : ℕ := ([1, 1, 1, 7] : List ℕ).get ⟨rect.val, rect.isLt⟩
def seedCap (rect : Fin 4) : ℕ := ([1, 6, 61, 56] : List ℕ).get ⟨rect.val, rect.isLt⟩

def cutoff (h : ℕ) (rect : Fin 4) (i : Fin 11) : ℕ :=
  buffered (bank rect i) h (reserve i)

theorem shape_guards (rect : Fin 4) (i : Fin 11) :
    0<(bank rect i).shape.J ∧ (bank rect i).shape.J≤(bank rect i).shape.B ∧
      (bank rect i).shape.B<K1.p ∧ (bank rect i).shape.U<K1.p ∧
      (bank rect i).shape.m*179808<K1.p := by
  fin_cases rect <;> fin_cases i <;> decide +kernel

#print axioms B1Checked.avoids
end Lower6962.B1.RescueSource
