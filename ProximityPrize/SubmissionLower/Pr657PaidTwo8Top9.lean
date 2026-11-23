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

namespace Pr657PaidTwo8Top9

private abbrev P:=PaidBatch .two8 9
private def batch0:List P:=paidGroup ["&19fub &19oO) &+1g:= 74YR5 $#C}Vz d70$1 b-8Y% #i@(9", "-Pu6 -Pu: -Pu> %|LCZ- -PuB C&{> #i?oE o/5A", "C&{B $_qRl- #B8Y~E atbnE $cPKM C&{F C&{J C&{N", "XY$J XY$N XY$R XY$V o/*R o/*V o/*Z o/*_"] (by decide +kernel) ++ paidGroup ["o/*c #'b0_ #~r_^ o.qU #'b0c #'b0g #'b0k #'b0o", "#=76k #=76o #>OswE XXIQ #=76s #=76w #=76{"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 27 22 = true :=
  checkedWindows tiles 134 27 [8, 8, 6]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 9) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+9) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top9

namespace Pr657PaidTwo8Top10

private abbrev P:=PaidBatch .two8 10
private def batch0:List P:=paidGroup ["&19o!M &.wE!) $l|*@Y #AS}%% aHZ&) $%!lFE er{pY c<|&E", "#i@(= XY:5 -Pu6 -Pu: $y&hM #i?zE -Pu> -PuB", "%|6nkQ -PuF C&{B C&{F C&{J C&{N C&{R XY$N", "XY$R XY$V XY$Z XY$_ o/*Z $7G{b o.|U o/*_"] (by decide +kernel) ++ paidGroup ["o/*c o/*g o/*k #'b0g #'b0k #'b0o #'b0s #'b0w", "#'b0{ #=76w _)/CQ -P2^ #=76{"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 30 19 = true :=
  checkedWindows tiles 134 30 [8, 8, 3]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 10) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+10) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top10

namespace Pr657PaidTwo8Top11

private abbrev P:=PaidBatch .two8 11
private def batch0:List P:=paidGroup ["&19oCv &,W#9I sb0L- $#p(o1 dc8;E bBk`5 XY:9 -Pu:", "-Pu> #i?zI XY/A -PuB -PuF %?%]Sj #C2kfQ -PuJ", "C&{F C&{J C&{N C&{R C&{V XY$R XY$V #~ru^", "o/*U XY$Z `zQ)U XY$_ XY$c XY$g o/*c o/*g"] (by decide +kernel) ++ paidGroup ["o/*k o/*o o/*s #'b0o #'aw^ #'b%j #'b0s #'b0w", "#'b0{ #'b1! #'b1&"] (by decide +kernel)
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 33 16 = true :=
  checkedWindows tiles 134 33 [8, 8]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 11) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+11) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top11

namespace Pr657PaidTwo8Top12

private abbrev P:=PaidBatch .two8 12
private def batch0:List P:=paidGroup ["&1$<T= %KK^:Q #CtIi9 cRQX9 &A@6A -PuB #~s.Q o/@I", "-PuF $`*)6E #AS|aM -PuJ -PuN -PuR C&{N C&{R", "%1Xnf #~s#^ C&{V C&{Z C&{_ XY$Z XY$_ XY$c", "XY$g XY$k XY$o o/*k o/*o `NHX^ #RjGj o/*s"] (by decide +kernel) ++ paidGroup ["o/*w o/*{ #'b0w #'b0{ #'b1! #'b1&"]
private def batches:List P:=batch0
private abbrev tiles:=tilesOf batches
private theorem rows : checks tiles 134 36 13 = true :=
  checkedWindows tiles 134 36 [8, 5]
theorem price (a : Shape) (ha : Valid a) (ht : a.t = 12) (hb : a.b ≤ 134) (hj : a.j ≤ 48) :
    Covered ((Final50PriceCaps.start .two8).t+12) .two8 a :=
  Compact54Packed.coverAt (bs:=batches) rows a ha ht hb hj
end Pr657PaidTwo8Top12
