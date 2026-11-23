import ProximityPrize.SubmissionLower.High6960High55Stages

set_option Elab.async false
set_option autoImplicit true
set_option maxRecDepth 18000

namespace High6960High55Stages

open High6960High55
open K1_14 (Shape)
open P3 (p)

private def Checks (lo : ℕ) (ss : List Stage) : Prop :=
  ∀ s ∈ ss,BankCertificate lo s.reserve 0 s.free ∧ BankCertificate lo s.reserve 1 s.moving
private theorem nil {lo:ℕ} : Checks lo []:=fun _ hs => (List.not_mem_nil hs).elim
private theorem cons {lo : ℕ} {s : Stage} {ss : List Stage}
    (hf:BankCertificate lo s.reserve 0 s.free)
    (hm:BankCertificate lo s.reserve 1 s.moving)
    (ht:Checks lo ss):Checks lo (s::ss) :=
  List.forall_mem_cons.mpr ⟨⟨hf,hm⟩,ht⟩
set_option quotPrecheck false

local notation "bank!" kk "," ww "," zz "," dd =>
  checked (k := kk) (w := ww) (z := zz) (d := dd)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 4000000 in
private theorem certificates (b : Band) : Checks (start b) (stages b) := by
  cases b with
  | h2570 =>
    rw [stages,start]
    refine cons (bank! 102,161496,21867698006688,288655842072) (bank! 489,523729,53182330608645984,3547619957712000) ?_
    refine cons (bank! 109,156614,32061854668752,452030748912) (bank! 479,414923,70473243793425168,4579087085087784) ?_
    refine cons (bank! 120,177713,42242722368096,664625024412) (bank! 535,541986,103713973812485208,7334979948171072) ?_
    refine cons (bank! 131,198812,54713065259016,957489099696) (bank! 571,462221,143121040390304760,10745168909506980) ?_
    refine cons (bank! 142,219911,68372656881984,1337864008992) (bank! 609,562283,191081109782169000,15369743024514000) ?_
    refine cons (bank! 151,138106,88351563398448,1848557638608) (bank! 725,642484,276761408662555200,26441723566762200) ?_
    refine cons (bank! 150,261089,124567476012228,2665150101240) (bank! 792,796038,367355963717918688,38498288224437888) ?_
    refine cons (bank! 198,191639,226840353246000,7120860965712) (bank! 966,838672,887179328423484648,111664819686758160) ?_
    refine cons (bank! 227,212779,883979041030128,31593255736536) (bank! 1181,1078880,2418141870146061540,369098272070560044) ?_
    refine cons (bank! 307,361961,807974571095424,37182809355984) (bank! 1322,1129748,3343374140383680228,573498066786439104) ?_
    refine cons (bank! 295,251666,2666953748362560,119555837094504) (bank! 1548,1396447,6477276735637675380,1431667910245465884) ?_
    refine cons (bank! 363,290553,6317195452572456,339366965461200) (bank! 2030,1799607,16190333014528596924,4587421189299953352) ?_
    refine cons (bank! 342,267455,106849761194732904,5545867322056896) (bank! 1693,1470828,28080127772262450000,6181142321245191120) ?_
    refine cons (bank! 387,392519,170056505007313392,10036813422865032) (bank! 1721,1312141,96941014806501938784,18467960688745418976) ?_
    refine cons (bank! 741,738950,20031880067699904,2266063954153200) (bank! 3125,2737111,84970208399365836360,38477411826834936384) ?_
    refine cons (bank! 884,757922,78325948240455600,11352716349105816) (bank! 4821,4230996,358802663814709289280,271673898769044820440) ?_
    refine cons (bank! 1073,1028898,150354493310371200,28919493644347200) (bank! 5786,5021140,720458185227386238612,688290425979382206036) ?_
    refine cons (bank! 1444,1406689,393612548559655392,113033841655027392) (bank! 7614,6481579,2189263383863496943584,2725758464084211499200) ?_
    exact nil
  | h8100 =>
    rw [stages,start]
    refine cons (bank! 16,137267,15608899152,39067056) (bank! 29,160324,159928351128,491706792) ?_
    refine cons (bank! 30,184033,68903790624,224288160) (bank! 54,295764,910994098896,4823788224) ?_
    refine cons (bank! 48,262694,308161482552,1545528600) (bank! 90,503180,4108714839936,42748945344) ?_
    refine cons (bank! 76,339528,995071719192,12594985608) (bank! 142,691745,8047808663472,401858102028) ?_
    exact nil

theorem stage_bounds (b : Band) {s : Stage} (hs : s ∈ stages b)
    {h:ℕ} (hl:start b≤h) (hh:h≤131071) :
    (WidthGuard h s.reserve s.free.shape ∧
      debit h s.free < gain h s.reserve s.free.shape 0 ∧ s.free.shape.U < p) ∧
    (WidthGuard h s.reserve s.moving.shape ∧
      debit h s.moving < gain h s.reserve s.moving.shape 1 ∧ s.moving.shape.U < p):=by
  obtain ⟨hf,hm⟩:=certificates b s hs
  exact ⟨of_certificate hl hh hf,of_certificate hl hh hm⟩

#print axioms stage_bounds
end High6960High55Stages
