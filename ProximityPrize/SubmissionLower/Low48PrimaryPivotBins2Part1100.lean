import ProximityPrize.SubmissionLower.Low48PrimaryPivotBinReceipts

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option linter.defProp false

namespace Low48PrimaryPivot
open K1_13_2_3

private def leaf1100:=checkedBin w2 1100 4 34374602309
private def leaf1104:=checkedBin w2 1104 4 35355286640
private def leaf1108:=checkedBin w2 1108 4 36361887072
private def leaf1112:=checkedBin w2 1112 4 37395427926
private def leaf1116:=checkedBin w2 1116 4 38456782253
private def leaf1120:=checkedBin w2 1120 4 39546659641
private def leaf1124:=checkedBin w2 1124 4 40666193844
private def leaf1128:=checkedBin w2 1128 4 41816349067
private def leaf1132:=checkedBin w2 1132 4 42997884911
private def leaf1136:=checkedBin w2 1136 4 44211957681
private def leaf1140:=checkedBin w2 1140 4 45459517836
private def leaf1144:=checkedBin w2 1144 4 46741297444
private def leaf1148:=checkedBin w2 1148 4 48058439224
private def leaf1152:=checkedBin w2 1152 4 49411883580
private def leaf1156:=checkedBin w2 1156 4 50802372449
private def leaf1160:=checkedBin w2 1160 4 52231102488
private theorem batch2_1100_1108 : binChunk w2 1100 8 = 69729888949 :=
  binChunk_join (w:=w2) (start:=1100) (left:=4) (right:=4) (x:=34374602309) (y:=35355286640) leaf1100 leaf1104
private theorem batch2_1108_1116 : binChunk w2 1108 8 = 73757314998 :=
  binChunk_join (w:=w2) (start:=1108) (left:=4) (right:=4) (x:=36361887072) (y:=37395427926) leaf1108 leaf1112
private theorem batch2_1100_1116 : binChunk w2 1100 16 = 143487203947 :=
  binChunk_join (w:=w2) (start:=1100) (left:=8) (right:=8) (x:=69729888949) (y:=73757314998) batch2_1100_1108 batch2_1108_1116
private theorem batch2_1116_1124 : binChunk w2 1116 8 = 78003441894 :=
  binChunk_join (w:=w2) (start:=1116) (left:=4) (right:=4) (x:=38456782253) (y:=39546659641) leaf1116 leaf1120
private theorem batch2_1124_1132 : binChunk w2 1124 8 = 82482542911 :=
  binChunk_join (w:=w2) (start:=1124) (left:=4) (right:=4) (x:=40666193844) (y:=41816349067) leaf1124 leaf1128
private theorem batch2_1116_1132 : binChunk w2 1116 16 = 160485984805 :=
  binChunk_join (w:=w2) (start:=1116) (left:=8) (right:=8) (x:=78003441894) (y:=82482542911) batch2_1116_1124 batch2_1124_1132
private theorem batch2_1100_1132 : binChunk w2 1100 32 = 303973188752 :=
  binChunk_join (w:=w2) (start:=1100) (left:=16) (right:=16) (x:=143487203947) (y:=160485984805) batch2_1100_1116 batch2_1116_1132
private theorem batch2_1132_1140 : binChunk w2 1132 8 = 87209842592 :=
  binChunk_join (w:=w2) (start:=1132) (left:=4) (right:=4) (x:=42997884911) (y:=44211957681) leaf1132 leaf1136
private theorem batch2_1140_1148 : binChunk w2 1140 8 = 92200815280 :=
  binChunk_join (w:=w2) (start:=1140) (left:=4) (right:=4) (x:=45459517836) (y:=46741297444) leaf1140 leaf1144
private theorem batch2_1132_1148 : binChunk w2 1132 16 = 179410657872 :=
  binChunk_join (w:=w2) (start:=1132) (left:=8) (right:=8) (x:=87209842592) (y:=92200815280) batch2_1132_1140 batch2_1140_1148
private theorem batch2_1148_1156 : binChunk w2 1148 8 = 97470322804 :=
  binChunk_join (w:=w2) (start:=1148) (left:=4) (right:=4) (x:=48058439224) (y:=49411883580) leaf1148 leaf1152
private theorem batch2_1156_1164 : binChunk w2 1156 8 = 103033474937 :=
  binChunk_join (w:=w2) (start:=1156) (left:=4) (right:=4) (x:=50802372449) (y:=52231102488) leaf1156 leaf1160
private theorem batch2_1148_1164 : binChunk w2 1148 16 = 200503797741 :=
  binChunk_join (w:=w2) (start:=1148) (left:=8) (right:=8) (x:=97470322804) (y:=103033474937) batch2_1148_1156 batch2_1156_1164
private theorem batch2_1132_1164 : binChunk w2 1132 32 = 379914455613 :=
  binChunk_join (w:=w2) (start:=1132) (left:=16) (right:=16) (x:=179410657872) (y:=200503797741) batch2_1132_1148 batch2_1148_1164
theorem batch2_1100_1164 : binChunk w2 1100 64 = 683887644365 :=
  binChunk_join (w:=w2) (start:=1100) (left:=32) (right:=32) (x:=303973188752) (y:=379914455613) batch2_1100_1132 batch2_1132_1164

end Low48PrimaryPivot
