import ProximityPrize.SubmissionLower.Low48PrimaryPivotBins2Part588

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Low48PrimaryPivot
open K1_13_2_3

private theorem leaf908 : binChunk w2 908 4 = 8604598058 := by decide +kernel
private theorem leaf912 : binChunk w2 912 4 = 8859209907 := by decide +kernel
private theorem leaf916 : binChunk w2 916 4 = 9120942058 := by decide +kernel
private theorem leaf920 : binChunk w2 920 4 = 9390147870 := by decide +kernel
private theorem leaf924 : binChunk w2 924 4 = 9667089815 := by decide +kernel
private theorem leaf928 : binChunk w2 928 4 = 9951930102 := by decide +kernel
private theorem leaf932 : binChunk w2 932 4 = 10245038746 := by decide +kernel
private theorem leaf936 : binChunk w2 936 4 = 10546690610 := by decide +kernel
private theorem leaf940 : binChunk w2 940 4 = 10857056795 := by decide +kernel
private theorem leaf944 : binChunk w2 944 4 = 11176528182 := by decide +kernel
private theorem leaf948 : binChunk w2 948 4 = 11505396558 := by decide +kernel
private theorem leaf952 : binChunk w2 952 4 = 11843844887 := by decide +kernel
private theorem leaf956 : binChunk w2 956 4 = 12192286314 := by decide +kernel
private theorem leaf960 : binChunk w2 960 4 = 12551029730 := by decide +kernel
private theorem leaf964 : binChunk w2 964 4 = 12920269867 := by decide +kernel
private theorem leaf968 : binChunk w2 968 4 = 13300442230 := by decide +kernel
private theorem batch2_908_916 : binChunk w2 908 8 = 17463807965 :=
  binChunk_join (w := w2) (start := 908) (left := 4) (right := 4) (x := 8604598058) (y := 8859209907) leaf908 leaf912
private theorem batch2_916_924 : binChunk w2 916 8 = 18511089928 :=
  binChunk_join (w := w2) (start := 916) (left := 4) (right := 4) (x := 9120942058) (y := 9390147870) leaf916 leaf920
private theorem batch2_908_924 : binChunk w2 908 16 = 35974897893 :=
  binChunk_join (w := w2) (start := 908) (left := 8) (right := 8) (x := 17463807965) (y := 18511089928) batch2_908_916 batch2_916_924
private theorem batch2_924_932 : binChunk w2 924 8 = 19619019917 :=
  binChunk_join (w := w2) (start := 924) (left := 4) (right := 4) (x := 9667089815) (y := 9951930102) leaf924 leaf928
private theorem batch2_932_940 : binChunk w2 932 8 = 20791729356 :=
  binChunk_join (w := w2) (start := 932) (left := 4) (right := 4) (x := 10245038746) (y := 10546690610) leaf932 leaf936
private theorem batch2_924_940 : binChunk w2 924 16 = 40410749273 :=
  binChunk_join (w := w2) (start := 924) (left := 8) (right := 8) (x := 19619019917) (y := 20791729356) batch2_924_932 batch2_932_940
private theorem batch2_908_940 : binChunk w2 908 32 = 76385647166 :=
  binChunk_join (w := w2) (start := 908) (left := 16) (right := 16) (x := 35974897893) (y := 40410749273) batch2_908_924 batch2_924_940
private theorem batch2_940_948 : binChunk w2 940 8 = 22033584977 :=
  binChunk_join (w := w2) (start := 940) (left := 4) (right := 4) (x := 10857056795) (y := 11176528182) leaf940 leaf944
private theorem batch2_948_956 : binChunk w2 948 8 = 23349241445 :=
  binChunk_join (w := w2) (start := 948) (left := 4) (right := 4) (x := 11505396558) (y := 11843844887) leaf948 leaf952
private theorem batch2_940_956 : binChunk w2 940 16 = 45382826422 :=
  binChunk_join (w := w2) (start := 940) (left := 8) (right := 8) (x := 22033584977) (y := 23349241445) batch2_940_948 batch2_948_956
private theorem batch2_956_964 : binChunk w2 956 8 = 24743316044 :=
  binChunk_join (w := w2) (start := 956) (left := 4) (right := 4) (x := 12192286314) (y := 12551029730) leaf956 leaf960
private theorem batch2_964_972 : binChunk w2 964 8 = 26220712097 :=
  binChunk_join (w := w2) (start := 964) (left := 4) (right := 4) (x := 12920269867) (y := 13300442230) leaf964 leaf968
private theorem batch2_956_972 : binChunk w2 956 16 = 50964028141 :=
  binChunk_join (w := w2) (start := 956) (left := 8) (right := 8) (x := 24743316044) (y := 26220712097) batch2_956_964 batch2_964_972
private theorem batch2_940_972 : binChunk w2 940 32 = 96346854563 :=
  binChunk_join (w := w2) (start := 940) (left := 16) (right := 16) (x := 45382826422) (y := 50964028141) batch2_940_956 batch2_956_972
theorem batch2_908_972 : binChunk w2 908 64 = 172732501729 :=
  binChunk_join (w := w2) (start := 908) (left := 32) (right := 32) (x := 76385647166) (y := 96346854563) batch2_908_940 batch2_940_972

end Low48PrimaryPivot
