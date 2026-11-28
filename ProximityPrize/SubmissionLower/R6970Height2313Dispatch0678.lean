import ProximityPrize.SubmissionLower.R6970Height2313CompactSeed
import ProximityPrize.SubmissionLower.R6970Height2313CompactRoute
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_fecaa47bf637388d
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.Bundle6970_79dae9e18d4fd12c
import ProximityPrize.SubmissionLower.R6970Height2308PowerReceipts
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.Bundle6970_8633d2278e296fef
import ProximityPrize.SubmissionLower.R6970Height2313Dispatch0677
import ProximityPrize.SubmissionLower.R6970Height2313PowerRoute
import ProximityPrize.SubmissionLower.R6970Height2313Powers
import ProximityPrize.SubmissionLower.R6970Height2313SmallGrade

set_option Elab.async false

section Z6969Source1200
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch8Band2
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 1 0:=
  NormalRoute.tailOfRun [128, 1024] ⟨
    entire CompressedReceipts.cell1126 CompressedReceipts.checked1126,
    entire CompressedReceipts.cell1127 CompressedReceipts.checked1127,
    entire CompressedReceipts.cell1128 CompressedReceipts.checked1128⟩
private theorem tail2_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 40, 128, 512] ⟨
    entire CompressedReceipts.cell1129 CompressedReceipts.checked1129,
    needed ⟨0,by decide⟩,
    needed ⟨1,by decide⟩,
    needed ⟨2,by decide⟩,
    needed ⟨3,by decide⟩,
    needed ⟨4,by decide⟩,
    entire CompressedReceipts.cell1130 CompressedReceipts.checked1130,
    entire CompressedReceipts.cell1131 CompressedReceipts.checked1131,
    entire CompressedReceipts.cell1132 CompressedReceipts.checked1132,
    entire CompressedReceipts.cell1133 CompressedReceipts.checked1133⟩
private theorem leaf3_1025:Done (7:Fin 18) ⟨25,27,9,3,1025,none⟩:=entire CompressedReceipts.cell1142 CompressedReceipts.checked1142
private theorem tail3_1025 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 1025:=leaf3_1025
private theorem leaf3_257:Done (7:Fin 18) ⟨25,27,9,3,257,some 1024⟩:=entire CompressedReceipts.cell1141 CompressedReceipts.checked1141
private theorem tail3_257 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 257:=join (leaf3_257) (tail3_1025 needed)
private theorem leaf3_41:Done (7:Fin 18) ⟨25,27,9,3,41,some 256⟩:=PaidRows.c1140
private theorem tail3_41 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 41:=join (leaf3_41) (tail3_257 needed)
private theorem leaf3_21:Done (7:Fin 18) ⟨25,27,9,3,21,some 40⟩:=PaidRows.c1139
private theorem tail3_21 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 21:=join (leaf3_21) (tail3_41 needed)
private theorem leaf3_17:Done (7:Fin 18) ⟨25,27,9,3,17,some 20⟩:=
  NormalRoute.splitSeed 19 (PaidRows.c1138) (entire CompressedReceipts.cell1138b CompressedReceipts.checked1138b)
private theorem tail3_17 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 17:=join (leaf3_17) (tail3_21 needed)
private theorem leaf3_13:Done (7:Fin 18) ⟨25,27,9,3,13,some 16⟩:=PaidRows.c1137
private theorem tail3_13 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 13:=join (leaf3_13) (tail3_17 needed)
private theorem leaf3_9:Done (7:Fin 18) ⟨25,27,9,3,9,some 12⟩:=entire CompressedReceipts.cell1136 CompressedReceipts.checked1136
private theorem tail3_9 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 9:=join (leaf3_9) (tail3_13 needed)
private theorem leaf3_4:Done (7:Fin 18) ⟨25,27,9,3,4,some 8⟩:=entire CompressedReceipts.cell1135 CompressedReceipts.checked1135
private theorem tail3_4 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 4:=join (leaf3_4) (tail3_9 needed)
private theorem leaf3_0:Done (7:Fin 18) ⟨25,27,9,3,0,some 3⟩:=entire CompressedReceipts.cell1134 CompressedReceipts.checked1134
private theorem tail3_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 3 0:=join (leaf3_0) (tail3_4 needed)
private theorem tail4_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 4 0:=
  NormalRoute.tailOfRun [3, 64, 512, 1024, 2048] ⟨
    PaidRows.c1143,
    entire CompressedReceipts.cell1144 CompressedReceipts.checked1144,
    entire CompressedReceipts.cell1145 CompressedReceipts.checked1145,
    entire CompressedReceipts.cell1146 CompressedReceipts.checked1146,
    entire CompressedReceipts.cell1147 CompressedReceipts.checked1147,
    entire CompressedReceipts.cell1148 CompressedReceipts.checked1148⟩
private theorem leaf5_2049:Done (7:Fin 18) ⟨25,27,9,5,2049,some 4096⟩:=power _ 643299 (by decide) PowerReceipts.power41 (by decide) (by decide) (by decide)
private theorem leaf5_1025:Done (7:Fin 18) ⟨25,27,9,5,1025,some 2048⟩:=power _ 643299 (by decide) PowerReceipts.power40 (by decide) (by decide) (by decide)
private theorem tail5_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 25 27 9 5 0:=
  NormalRoute.tailOfRun [1, 128, 512, 1024, 2048, 4096] ⟨
    entire CompressedReceipts.cell1149 CompressedReceipts.checked1149,
    entire CompressedReceipts.cell1150 CompressedReceipts.checked1150,
    entire CompressedReceipts.cell1151 CompressedReceipts.checked1151,
    entire CompressedReceipts.cell1152 CompressedReceipts.checked1152,
    leaf5_1025,
    leaf5_2049,
    PaidRows.c1153⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (a:ℕ) (lo:0<a) (hi:a≤5):
    Tail (7:Fin 18) 25 27 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
  · exact tail5_0 needed
end Research6970.Height2313.Research6969.HighDispatch8Band2
end Z6969Source1200

section Z6969Source1201
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch8Band3
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 28 32 9 1 0:=
  NormalRoute.tailOfRun [128, 1024] ⟨
    entire CompressedReceipts.cell1154 CompressedReceipts.checked1154,
    entire CompressedReceipts.cell1155 CompressedReceipts.checked1155,
    entire CompressedReceipts.cell1156 CompressedReceipts.checked1156⟩
private theorem tail2_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 28 32 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 40, 96, 256] ⟨
    entire CompressedReceipts.cell1157 CompressedReceipts.checked1157,
    needed ⟨5,by decide⟩,
    needed ⟨6,by decide⟩,
    needed ⟨7,by decide⟩,
    needed ⟨8,by decide⟩,
    needed ⟨9,by decide⟩,
    PaidRows.c1158,
    entire CompressedReceipts.cell1159 CompressedReceipts.checked1159,
    entire CompressedReceipts.cell1160 CompressedReceipts.checked1160,
    entire CompressedReceipts.cell1161 CompressedReceipts.checked1161⟩
private theorem tail3_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 28 32 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 40, 128, 512] ⟨
    entire CompressedReceipts.cell1162 CompressedReceipts.checked1162,
    entire CompressedReceipts.cell1163 CompressedReceipts.checked1163,
    entire CompressedReceipts.cell1164 CompressedReceipts.checked1164,
    PaidRows.c1165,
    needed ⟨10,by decide⟩,
    entire CompressedReceipts.cell1166 CompressedReceipts.checked1166,
    PaidRows.c1167,
    entire CompressedReceipts.cell1168 CompressedReceipts.checked1168,
    entire CompressedReceipts.cell1169 CompressedReceipts.checked1169,
    entire CompressedReceipts.cell1170 CompressedReceipts.checked1170⟩
private theorem tail4_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 28 32 9 4 0:=
  NormalRoute.tailOfRun [3, 20, 64, 256, 1024] ⟨
    PaidRows.c1171,
    PaidRows.c1172,
    entire CompressedReceipts.cell1173 CompressedReceipts.checked1173,
    entire CompressedReceipts.cell1174 CompressedReceipts.checked1174,
    PaidRows.c1175,
    entire CompressedReceipts.cell1176 CompressedReceipts.checked1176⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (7:Fin 18) 28 32 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch8Band3
end Z6969Source1201

section Z6969Source1203
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch8Band4
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 33 40 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1177 CompressedReceipts.checked1177,
    entire CompressedReceipts.cell1178 CompressedReceipts.checked1178⟩
private theorem tail2_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 33 40 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 48, 96, 256] ⟨
    entire CompressedReceipts.cell1179 CompressedReceipts.checked1179,
    needed ⟨11,by decide⟩,
    needed ⟨12,by decide⟩,
    needed ⟨13,by decide⟩,
    needed ⟨14,by decide⟩,
    needed ⟨15,by decide⟩,
    entire CompressedReceipts.cell1180 CompressedReceipts.checked1180,
    entire CompressedReceipts.cell1181 CompressedReceipts.checked1181,
    entire CompressedReceipts.cell1182 CompressedReceipts.checked1182,
    entire CompressedReceipts.cell1183 CompressedReceipts.checked1183,
    entire CompressedReceipts.cell1184 CompressedReceipts.checked1184⟩
private theorem tail3_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 33 40 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 48, 128, 512] ⟨
    entire CompressedReceipts.cell1185 CompressedReceipts.checked1185,
    entire CompressedReceipts.cell1186 CompressedReceipts.checked1186,
    entire CompressedReceipts.cell1187 CompressedReceipts.checked1187,
    PaidRows.c1188,
    needed ⟨16,by decide⟩,
    PaidRows.c1189,
    entire CompressedReceipts.cell1190 CompressedReceipts.checked1190,
    entire CompressedReceipts.cell1191 CompressedReceipts.checked1191,
    entire CompressedReceipts.cell1192 CompressedReceipts.checked1192,
    PaidRows.c1193,
    entire CompressedReceipts.cell1194 CompressedReceipts.checked1194,
    entire CompressedReceipts.cell1195 CompressedReceipts.checked1195⟩
private theorem tail4_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 33 40 9 4 0:=
  NormalRoute.tailOfRun [3, 16, 28, 64, 128, 256] ⟨
    PaidRows.c1196,
    entire CompressedReceipts.cell1197 CompressedReceipts.checked1197,
    PaidRows.c1198,
    entire CompressedReceipts.cell1199 CompressedReceipts.checked1199,
    entire CompressedReceipts.cell1200 CompressedReceipts.checked1200,
    entire CompressedReceipts.cell1201 CompressedReceipts.checked1201,
    entire CompressedReceipts.cell1202 CompressedReceipts.checked1202⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (a:ℕ) (lo:0<a) (hi:a≤4):
    Tail (7:Fin 18) 33 40 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
  · exact tail4_0 needed
end Research6970.Height2313.Research6969.HighDispatch8Band4
end Z6969Source1203

section Z6969Source1205
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch8Band5
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 41 49 9 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1203 CompressedReceipts.checked1203,
    entire CompressedReceipts.cell1204 CompressedReceipts.checked1204⟩
private theorem tail2_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 41 49 9 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 128] ⟨
    entire CompressedReceipts.cell1205 CompressedReceipts.checked1205,
    needed ⟨17,by decide⟩,
    needed ⟨18,by decide⟩,
    needed ⟨19,by decide⟩,
    needed ⟨20,by decide⟩,
    needed ⟨21,by decide⟩,
    entire CompressedReceipts.cell1206 CompressedReceipts.checked1206,
    entire CompressedReceipts.cell1207 CompressedReceipts.checked1207,
    entire CompressedReceipts.cell1208 CompressedReceipts.checked1208,
    needed ⟨22,by decide⟩,
    entire CompressedReceipts.cell1209 CompressedReceipts.checked1209,
    entire CompressedReceipts.cell1210 CompressedReceipts.checked1210⟩
private theorem tail3_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 41 49 9 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 128] ⟨
    entire CompressedReceipts.cell1211 CompressedReceipts.checked1211,
    entire CompressedReceipts.cell1212 CompressedReceipts.checked1212,
    entire CompressedReceipts.cell1213 CompressedReceipts.checked1213,
    PaidRows.c1214,
    needed ⟨23,by decide⟩,
    PaidRows.c1215,
    entire CompressedReceipts.cell1216 CompressedReceipts.checked1216,
    entire CompressedReceipts.cell1217 CompressedReceipts.checked1217,
    entire CompressedReceipts.cell1218 CompressedReceipts.checked1218,
    entire CompressedReceipts.cell1219 CompressedReceipts.checked1219,
    entire CompressedReceipts.cell1220 CompressedReceipts.checked1220,
    PaidRows.c1221,
    entire CompressedReceipts.cell1222 CompressedReceipts.checked1222⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (7:Fin 18) 41 49 9 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch8Band5
end Z6969Source1205

section Z6969Source1206
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch8Band6
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 50 63 10 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    entire CompressedReceipts.cell1223 CompressedReceipts.checked1223,
    entire CompressedReceipts.cell1224 CompressedReceipts.checked1224⟩
private theorem tail2_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 50 63 10 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64] ⟨
    entire CompressedReceipts.cell1225 CompressedReceipts.checked1225,
    needed ⟨24,by decide⟩,
    needed ⟨25,by decide⟩,
    needed ⟨26,by decide⟩,
    needed ⟨27,by decide⟩,
    needed ⟨28,by decide⟩,
    entire CompressedReceipts.cell1226 CompressedReceipts.checked1226,
    entire CompressedReceipts.cell1227 CompressedReceipts.checked1227,
    PaidRows.c1228,
    needed ⟨29,by decide⟩,
    needed ⟨30,by decide⟩,
    entire CompressedReceipts.cell1229 CompressedReceipts.checked1229⟩
private theorem leaf3_49:Done (7:Fin 18) ⟨50,63,10,3,49,some 64⟩:=power _ 385979 (by decide) PowerReceipts.power48 (by decide) (by decide) (by decide)
private theorem tail3_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 50 63 10 3 0:=
  NormalRoute.tailOfRun [3, 8, 12, 16, 20, 24, 28, 32, 40, 48, 64, 96] ⟨
    entire CompressedReceipts.cell1230 CompressedReceipts.checked1230,
    entire CompressedReceipts.cell1231 CompressedReceipts.checked1231,
    PaidRows.c1232,
    needed ⟨31,by decide⟩,
    needed ⟨32,by decide⟩,
    needed ⟨33,by decide⟩,
    PaidRows.c1233,
    entire CompressedReceipts.cell1234 CompressedReceipts.checked1234,
    needed ⟨34,by decide⟩,
    BandPowerReceipts.cover8_41,
    leaf3_49,
    entire CompressedReceipts.cell1235 CompressedReceipts.checked1235,
    entire CompressedReceipts.cell1236 CompressedReceipts.checked1236⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (a:ℕ) (lo:0<a) (hi:a≤3):
    Tail (7:Fin 18) 50 63 10 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
  · exact tail3_0 needed
end Research6970.Height2313.Research6969.HighDispatch8Band6
end Z6969Source1206

section Z6969Source1207
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch8Band7
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
set_option maxHeartbeats 1600000
set_option maxRecDepth 16000
set_option linter.unusedVariables false
private theorem tail1_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 64 722 12 1 0:=
  NormalRoute.tailOfRun [128] ⟨
    PaidRows.c1237,
    entire CompressedReceipts.cell1238 CompressedReceipts.checked1238⟩
private theorem tail2_0 (needed:HighPendingSeed8.Required):Tail (7:Fin 18) 64 722 12 2 0:=
  NormalRoute.tailOfRun [8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52] ⟨
    entire CompressedReceipts.cell1239 CompressedReceipts.checked1239,
    needed ⟨35,by decide⟩,
    needed ⟨36,by decide⟩,
    needed ⟨37,by decide⟩,
    needed ⟨38,by decide⟩,
    needed ⟨39,by decide⟩,
    needed ⟨40,by decide⟩,
    needed ⟨41,by decide⟩,
    needed ⟨42,by decide⟩,
    needed ⟨43,by decide⟩,
    needed ⟨44,by decide⟩,
    needed ⟨45,by decide⟩,
    entire CompressedReceipts.cell1240 CompressedReceipts.checked1240⟩
theorem allDegrees (needed:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (a:ℕ) (lo:0<a) (hi:a≤2):
    Tail (7:Fin 18) 64 722 12 a 0:=by
  interval_cases a
  · exact tail1_0 needed
  · exact tail2_0 needed
end Research6970.Height2313.Research6969.HighDispatch8Band7
end Z6969Source1207

section Z6969Source1208
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatchSeed8
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute _root_.Research6970.Height2313.Research6969.HighPackets
open _root_.Research6970.Height2313.Research6969.BookView
theorem count (need:_root_.Research6970.Height2313.Research6969.HighPendingSeed8.Required) (s:State (7:Fin 18)):s.labels.card≤_root_.Research6969.CertifiedCell.target:=by
  let b:=_root_.Research6969.TransitionClassification.band s.f.natDegree
  have first:=_root_.Research6969.TransitionClassification.lower_bound s.high
  have last:=_root_.Research6969.OrdinaryComplete.upper_band s.degree_bound
  have all (b:Fin 8) (a:ℕ) (p:0<a) (h:a≤_root_.Research6969.TransitionClassification.maxGraph b): Tail (7:Fin 18) (_root_.Research6969.TransitionClassification.grade b) (_root_.Research6969.OrdinaryComplete.upper (savedMainGrade 7+savedRescueGrade 7) b) (_root_.Research6969.TransitionClassification.content b) a 0:=by
    fin_cases b
    · exact HighDispatch8Band0.allDegrees need a p h
    · exact HighDispatch8Band1.allDegrees need a p h
    · exact HighDispatch8Band2.allDegrees need a p h
    · exact HighDispatch8Band3.allDegrees need a p h
    · exact HighDispatch8Band4.allDegrees need a p h
    · exact HighDispatch8Band5.allDegrees need a p h
    · exact HighDispatch8Band6.allDegrees need a p h
    · exact HighDispatch8Band7.allDegrees need a p h
  have positive:0<s.graph.graphDegree:=by unfold Research6966.Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  exact all b s.graph.graphDegree positive s.graphBound s.clearContent ⟨first,last,rfl,rfl,Nat.zero_le _,by simp⟩
end Research6970.Height2313.Research6969.HighDispatchSeed8
end Z6969Source1208

section Z6969Source1209
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighPendingSeed9
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
def regions:Array Region:=#[⟨28,32,9,2,9,some 12⟩,⟨28,32,9,2,13,some 16⟩,⟨28,32,9,2,17,some 20⟩,⟨28,32,9,2,21,some 24⟩,⟨28,32,9,2,25,some 28⟩,⟨33,40,9,2,9,some 12⟩,⟨33,40,9,2,13,some 16⟩,⟨33,40,9,2,17,some 20⟩,⟨33,40,9,2,21,some 24⟩,⟨33,40,9,2,25,some 28⟩,⟨41,49,9,2,9,some 12⟩,⟨41,49,9,2,13,some 16⟩,⟨41,49,9,2,17,some 20⟩,⟨41,49,9,2,21,some 24⟩,⟨41,49,9,2,25,some 28⟩,⟨41,49,9,2,49,some 64⟩,⟨50,63,10,2,9,some 12⟩,⟨50,63,10,2,13,some 16⟩,⟨50,63,10,2,17,some 20⟩,⟨50,63,10,2,21,some 24⟩,⟨50,63,10,2,25,some 28⟩,⟨50,63,10,2,49,some 56⟩,⟨50,63,10,3,17,some 20⟩,⟨50,63,10,3,21,some 24⟩,⟨50,63,10,3,33,some 40⟩,⟨64,654,12,2,9,some 12⟩,⟨64,654,12,2,13,some 16⟩,⟨64,654,12,2,17,some 20⟩,⟨64,654,12,2,21,some 24⟩,⟨64,654,12,2,25,some 28⟩,⟨64,654,12,2,29,some 32⟩,⟨64,654,12,2,33,some 36⟩,⟨64,654,12,2,37,some 40⟩,⟨64,654,12,2,41,some 48⟩,⟨64,654,12,2,49,some 52⟩]
def atIndex (j:Fin regions.size):Region:=regions[j.val]
def Required:Prop:=∀j:Fin regions.size,Done (8:Fin 18) (atIndex j)
end Research6970.Height2313.Research6969.HighPendingSeed9
end Z6969Source1209

section Z6969Source1211
set_option autoImplicit true
namespace Research6970.Height2313.Research6969.HighDispatch9Band0
open _root_.Research6970.Height2313.Research6969
open _root_.Research6970.Height2313.Research6969.NormalRoute
theorem allDegrees (_ : _root_.Research6970.Height2313.Research6969.HighPendingSeed9.Required) (a : ℕ) (_ : 0 < a) (_ : a ≤ 6) :
    Tail (8 : Fin 18) 22 22 9 a 0 :=
  ExtendedJointBills.counted9 _ (by decide : 22 ≤ 26)
end Research6970.Height2313.Research6969.HighDispatch9Band0
end Z6969Source1211
