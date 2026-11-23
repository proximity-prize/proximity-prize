import ProximityPrize.SubmissionLower.Compact54Packed

set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000

open Compact54Packed (paidGroup checkedWindows)
open K1_13 (Shape)
open K1_13_8 (Valid)
open Final50PriceTableBase (Covered)
open Compact50Cover (PaidBatch tilesOf checks)

set_option linter.defProp false

namespace Pr657PaidTwo6thinTop9

private abbrev P:=PaidBatch .two6thin 9
private def batch0:List P:=paidGroup ["&14+-C &14Jyl &$kdL3 %|1[%7 %{y0YW #TbOZ3 &]hf,/ #~vOG~","#?DqIt #>J`c# #>5-Q+ _#xv# (<e/ %=mbl= $24PC #yg2l","#M^xp (Dns $^<QI #d+uE #!MLC (Dnw #}%-b| =wts","=wil =wtw =wt{ SLzw `I4j= =w^n SLz{ SL{!","j##{ (<YF j#$! $Zmz|E (<YJ j#$& %wNYx9 $ZWG`9","(<YN j#$* #>J`+- (<YR j#$. =oI9 =oTE =o`N","j#$2 =o`R j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 27 24 = true :=
  checkedWindows tiles 135 27 [8, 8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+9) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop9

namespace Pr657PaidTwo6thinTop10

private abbrev P:=PaidBatch .two6thin 10
private def batch0:List P:=paidGroup ["&14Bdp &14S&W &-w~&? #~`zX# #@TWe3 %|G(1^ $^r&ZM #?pyJl","#>a5Q~ #>5-0) _9Mf% =oT1 $24PC #yg2l #M^xp `_h47","#d,#C (Dns (Dnw =wts =wil =wtw =wt{ SLzw","#MUXI SD|C =w^l SLz{ SL{! j##{ (<YF j#$!","_{,<9 #!M+E (<YJ j#$& #{[qAr _eU}- (<YN j#$*","(<YR j#$. =o`N j#$2 =o`R j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 30 21 = true :=
  checkedWindows tiles 135 30 [8, 8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+10) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop10

namespace Pr657PaidTwo6thinTop11

private abbrev P:=PaidBatch .two6thin 11
private def batch0:List P:=paidGroup [",W-4Ph 9NpUC &'.([f &!wAt3 $''P4' $!DW`% cM==; `I5-|","_eVW/ _9N57 (<Y/ (<e; `_hU; #~4Y:d SM3p #M^bl","j#9l (Dns (Dnw =wts =wtw SD|; =okC (<YF","=ovC =wt{ SLzw =w^l SLz{ SL{! %;7bR9 j##{","j#$! #{[qX) _O$%= SDqI (<YJ j#$& (<YN j#$*","(<YR j#$. (<82 =oTE =o`N j#$2 #=|VY~ _#xT9","=o`R j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 33 18 = true :=
  checkedWindows tiles 135 33 [8, 8, 2]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+11) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop11

namespace Pr657PaidTwo6thinTop12

private abbrev P:=PaidBatch .two6thin 12
private def batch0:List P:=paidGroup ["*[9pt' 9NpUC &%$9(+ %~Q0sd #~JG<# bS,w; aCM|` #M^mp","SM3p $^0GyQ #A#`95 (Dns `u=:; #y_)G #8#^G j#.l","(Dnw (Dn{ =wtw =wt{ SLzw SLz{ (DLl (DLo","SL{! SL{& j#$! #!M+E SDqG (<YJ j#$& (<YN","j#$* (<YR j#$. =o`N j#$2 _#xI- (<86 =o`R","j#$6"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 135 36 15 = true :=
  checkedWindows tiles 135 36 [8, 7]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 135) (hj : a.j ≤ 50) :
    Covered ((Final50PriceCaps.start .two6thin).t+12) .two6thin a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo6thinTop12
