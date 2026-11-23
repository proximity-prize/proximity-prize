import ProximityPrize.SubmissionLower.KoalaAt2428Gate10
import ProximityPrize.SubmissionLower.KoalaGateSharedData
import ProximityPrize.SubmissionLower.KoalaGateChunkSums
import ProximityPrize.SubmissionLower.KoalaSplitGateWords

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

set_option linter.defProp false

namespace KoalaAt2428Gate11
open KoalaGateSharedData
open FadicGate KoalaGateCheck
open KoalaWeightedRate (Envelope)
open KoalaFarBridge (rowCheck plainCheck)

def envelope : Envelope :=
  ⟨137,56,12,137,56,3562,4437,⟨2567926019269032960,13279934072995436160,6618610727177433600⟩,1125879162488298368640⟩
abbrev split:ℕ:=96
abbrev unit:ℕ:=495437287300736079360
abbrev terminal:ℕ:=73
abbrev gate:=KoalaSplitRow.rate envelope split unit

private def boxesTape : List (List Entry) := [
  unpack 1 0x13ec3670,unpack 2 0x49500fe15f3005c,unpack 3 0x4b4d56c48ccd8c17a32f52,unpack 3 0x4b4dd5648cf13219a9eacf,unpack 4 0x4b4d9ac498e58c48492101b598974,unpack 5 0x4b8dd88494e1e44b0cd8648cf8f61d60d542,unpack 5 0x4b4ddc6490ba084b8f90848492121f106579,unpack 6 0x490b65e4bd212a490ed864b4a1e048cf11e216e040e,
  unpack 6 0x494f9a24bcf592498c2204b0e93c4889602231d7767,unpack 7 0x490c6224a529de4b8fd4448cdd904b8a5e4488f8fa2524ee81,unpack 8 0x4cd260c490e990490ca3a4bd0914490dda44bcd95c484cd76272ba9fe,unpack 8 0x4d12df64952d6448ced784c0d5b4488e5c64b891f648d00e229320edf,unpack 9 0x480d4f24d93dea49505d44c0bde4490d9fe48d19104b8c96648495f42ae1bbea,unpack 9 0x490c23e4c52934494d64c4953d524bcc98e48ce9944c0c956480bda42ce8f952,unpack 10 0x4b8d9764a13a124b889e64993d5e494d64c4bd050a48cae2c4b8f0fa484d9442e997edc,unpack 10 0x4b0a9304a94e444c4b9ee4912d6a488ed8a4c0c9c648cf1584bcb590480c58e309fe3c5,
  unpack 11 0x4d94238480b9404a9525e4c901ba490e5b64849e424c4e99248914f84c0d540480c98432a6adb1,unpack 11 0x490c26a4c52100494e29c4cd2d3e491058e4c8e59a480c9cc488e1864bcbd7a480c9843456ce38,unpack 12 0x4c9cade47c72064d55d72488ed7a4ccf5e848cf1c848cf9b04c4a60a48510fc4c0c16c480cd7a365d9824,unpack 12 0x4b1370c4b0dca04b16a50478bd564d505e6480a2724913d2c4c8d9704849e3e4c50ca047cb5bc3863ee96,unpack 12 0x499121447cb94e4e55e3848cf5984c89a3848d4d68488e9724c48256481150a4c4c15e480d9643a6ab882,unpack 13 0x4ce0e48480cd78488edd44d8de9c4951a0a4cd1cb6484e9e04cca2224852cc44808e6c4c0f8b247cbda83c1ad909,unpack 14 0x4b56e504b9c61a474b55e49ceee04cd30ca49525ec4cc9e4c4811d1a488edb04c8c990480e1724c47e0247d0cee3e21a2f5,unpack 15 0x47879aa4cdf6824a13e36478b5504ad866c4b8a148498e2a84d12900484f1844c4cda6484e1be48092644c9048c478c5923fd1d1ea,
  unpack 15 0x49509ca4cdd6d8480aa5c47cf8be4ad867a4c0a93e48d1a2a4d4e19e484fd90480e1d64d0cd80480e9804c06a1847d14d841d88d68,unpack 16 0x470b9024b53ecc4c5f22c474b56a484ede44994a264d09e26488f1ca4d134e0488fdf247ce57a4ccbd9c47ce9704ccbd5447c766644344fb6,unpack 17 0x46c953c470c0e64d5d6d24a93ad2474ad7c495759048cbe9a4dd15964790cd84d4e9a048501f6480e99a4c872464853cae4c8a190474d180458f77db,unpack 18 0x46c953c6889d2627525764d1dec049115ea46ca9904ad470c47500de4e525cc478d9c44d8a64a4812516480f18e4ccc59a478d98c4d0bd3e4787a5e47eb2bbb,unpack 18 0x464914a46891384b57e304cdf6884748a14470e4de4a99690474c15e4e50e064850dd44d0c98c480f58447cddbe4d0c58c47cdd884ccc136474c1ac499ca6a7,unpack 19 0x46095406bc953a21089604d5d6c64b5be14468ad7c484be5849d4e5447100ba4e929c8480f6064d89e2047d2ccc480f9c44ccb18647c828e4c90c78478d9684ba36224,unpack 19 0x460952e464954e48cfdbc4d1fa6a4953e1446cb16e4954a024891de647cedc04e0a66a4814d2a4d8d196480a69a478dda44d1149c478e56c4d0b15e474c5a24da9c705,unpack 20 0x46cc16e460994446091444b16e264d1fe62470ddce46cb5624a9431c4711d0848d21fc4d0c54e48101f64dcd57e48101ac478e9ac4d4b98e478e9624d05e3647518be4fb0740e,
  unpack 20 0x454953c458914a46095324d5d6b24bdbe80464c150468b95a4b1b2a846cb58848d3e284d0520e48569004dcd97e478f1de47c86844cd208e47cd5a84d0b554474cd8c5160b178,unpack 21 0x480fdb6450914a45c914e48905aa4cdd6a049d524c464e0f8478ede84a17656468bd7e48cdf1e4dd306e478e5b64e90190470c9e2478f58a4d8c176474d59a4d0b54a4746e8c53660422,unpack 21 0x448993044c913c45891604b176104c9d2b047d256a4647e0248d719a489322646cbd7248d46124e4f9aa474d5ca4e0e572474e19e478e1c04d8c16c47072a84d9242446cb9c655179beb,unpack 22 0x491320a444954044c915245c9d2e4d1da964c1c6b045ca984464e0fa49d7a96478ae9647534ea48529d04e4e5c847d05984d8b9a847cfd96470cdb24d8c962474dd844d4a572470d978571e65d7,unpack 22 0x64b9807b49d3c0dc8d5e481099e4cdd6a04a16e4845cad744589daa4ba063e464b9684811a22470e9b04ecfd9a478f1de4dcc16a47c9e9646d38c24dcc560478e1764d0ad6a46cbdbc58ce865e,unpack 23 0xb9a1b042c6dc2440993a44895484a96a304c9da9247915ce45ce104474e9f64a14b14460f8e248d523c468bd7e4e8f1bc478f5d44e0d556478f1ba4747ad64d9283e470cdb24dcc516468c5b45ad5504a,unpack 23 0x213de442875c4440955644495364d1d6aa4c1d2a845cc560458c93648946144894a2e460bd844915a24460a9b04f105a647896d24e12c6c474f5bc474f1964dcb95c470cdb24d4b15c470c5a25cdba6bb,unpack 23 0x13ecaa08034993c47501ac8c1a3300b1c9c883c5648069047849d6ac44713d64464c1784894e48474f98c4e8766c47149024ecf58a468cdb847476c24e13c4646cd1864dcb14c46ccd9a5ee270a7,
  unpack 23 0x100919b24305de64a16e1c4c5fa2e481360844c85be450d11a4b5d2ce464d58a468f1ba48126164790dec4dca16847909a64ecdd9c46ce9be470e1a04e0c14246cd1944dcbd4c46ccd9060e92c1f,unpack 23 0x8129ef54122f1306d0cec470a11c01004b1d6469196e4a1c63e45899ea47d2dfa470f5b2479161a4e4c950474f5d64e4c18a470e9ae46ce9984e4c14046cd9944d8a17c46cd18e62995b1a,unpack 23 0x204084f79a384f8a808101d19d047d59e448d3a6445d0530485720845c725a47d25e24f0e58e46ce9bc4e4bd66470f59a46cd1ce4e0c55c46cc9a64dcbd2c470d18264f64c7d,unpack 23 0x1020408102040810153d8e4852a8246928e64f0f9ea470a6a6471019e4e0b588474f1984e0b97e46ce18c468d1a84dca56c46cd97a6650458d,unpack 23 0x1020408102040810d53e0882d3e080113d664fd21d446d1d9e46cf59c4e44a94470f9b446cd9b84e8cd42468d1924d8a966470d96c68ad36f0,unpack 23 0x204081020408102040810b52208465593a4e0dd9047d05a646086a446ce1ac4e0bd4e46ccd904dcad58464c5b46a073000,unpack 23 0x204081020408102040811c93e083893e08440fa084f544e0464f57c4e8527c46cdd94460bdce4e8c504464c9aa6c642163,unpack 23 0x810204081020408102040811d1358a3c945c246d197a4e4b1924687e9046cd59e4d89d60468c9a86e14505e,
  unpack 23 0x40810204081020408102040811713e084353d384dcdd7c468f1844645ec44e4b932464c9a0701b0bd6,unpack 23 0x2040810204081020408102040811813e084993d16468ed96464f1624e012c2464d19471cb3ad1,unpack 23 0x102040810204081020408102040812913d803993d924d4c16c468d1624605ad274282c34,unpack 23 0x8102040810204081020408102040812bd315e3e5218c454d96e474e55477335749,unpack 23 0x81020408102040810204081020408134d3e083653d624691542464d97e78e3a31c,unpack 23 0x408102040810204081020408102040813693dda34d3d424590d867a3dc778,unpack 23 0x20408102040810204081020408102040813653d8e3413d667c43b89d,unpack 23 0x102040810204081020408102040810204081371356a98371778,
  unpack 23 0x1020408102040810204081020408102040814113e08a5afa18f]
def boxes (r : ℕ) : List FadicGate.Entry :=
  if r < 16 then [] else boxesTape.getD (r-16) []

def plain : ℕ → ℕ × ℕ × ℕ
  | _ => (0,0,0)

private def powersTape : List String := [
  "","","","","","","","",
  "","","","","","","","",
  "!$","!$'","!$'","!#',","!#&,0","!#&*0",z4F,"!#&+28",
  "!#&).9?","!#&).59G","!#%*/3;I",z5A,"!#%),5=EK",z4j,z4i,z6B,
  z4S,"!#%',28AESQq","!#%(,28CAUSi",z4N,"!#$'*/59DQWXy","!#%'+04:EKYWq~#(","!#$'+04;FEZYi~#,~#(","!#$'+05;GF]Za~#$~#,",
  z6T,z63,z3v,z5g,z5U,z5R,z3l,z2v,
  z3f,z2t,z3U,z3V,z3S,(zz69 ++ "#O~#K~#G~#8"),(zz67 ++ "#S~#O~#G~#8"),(zz68 ++ "#W~#S~#G~#8"),
  (zz104 ++ "ro~#;~#[~#V~#G~#8"),"!#$%(+/26=GFWViwrl~#)~#R~#W~#G~#8","!#$%(+/27=HGXW`xrls~#@~#W~#G~#8","!#$%(+037>HHZWUxrlf~#-~#W~#G~#8","!#$%'*-37>DHSWSnrlfw~#D~#G~#8","!#$%'*-38??HLWSdrlfd~#0~#G~#8","!##%'*.48?=HFWSYrlf`z~#G~#8","!#$%(*.18;=HFWSPrlf`g~#4~#8",
  "!##%'+.057=HFWSPhlf`Y~!~~#8","!##%').037=HFPSP^lf`Yk~#8","!##%'),037=BFISPSlf`YW~#%","!##%'),037==FCSPMlf`YTo","!##%'),037=<FCSPMbf`YT[","!##%'),037=<FCSPMWf`YTN","!##%'(,-379<FCMPMNf`YTN","!##%'(,-376<FCFPMJf`YTN"]

def powers (r : ℕ) : List ℕ :=
  if r=0 then [] else KoalaSplitGateWords.powers (powersTape.getD (r-1) "")

def plainPowers : ℕ → List ℕ
  | _ => []

def tailPowers : List ℕ := KoalaSplitGateWords.powers "!##$&(*-046<@CAPMJ[`YTNHcgWG8)"

def priced (r:ℕ):Bool:=rowCheck gate r (boxes r) (powers r) (plain r) (plainPowers r)
private theorem priced_list : (List.range 72).all (fun i => priced (i+1)) = true := by decide +kernel

theorem prices {r : ℕ} (hr : 0 < r) (hR : r < terminal) : priced r = true :=
  price hr hR priced_list

theorem tail:plainCheck gate terminal (4012,1650,550) tailPowers=true:=by decide +kernel

private theorem exactLoss0 : lossChunk 1 envelope plain boxes 0 24 = 9731749453675 :=
  by decide +kernel

private theorem exactLoss24 : lossChunk 1 envelope plain boxes 24 24 = 8446385125477 :=
  by decide +kernel

private theorem exactLoss48 : lossChunk 1 envelope plain boxes 48 24 = 2497083287116 :=
  by decide +kernel

theorem loss_bound (N : ℕ) : Bound envelope terminal plain boxes 20675217866268 N :=
  loss_of_chunks 1 envelope terminal plain boxes 20675217866268 N (by decide) (by decide)
    (LossSum.empty _ _ _ _
      |>.append 24 9731749453675 exactLoss0
      |>.append 24 8446385125477 exactLoss24
      |>.append 24 2497083287116 exactLoss48)

def receipt : KoalaSplitProof.Receipt envelope split unit :=
  ⟨terminal, plain, boxes, powers, plainPowers, tailPowers, 20675217866268,
    by decide,by decide,loss_bound,fun _ h h' => prices h h', tail⟩

end KoalaAt2428Gate11

#print axioms KoalaAt2428Gate11.loss_bound
#print axioms KoalaAt2428Gate11.receipt
