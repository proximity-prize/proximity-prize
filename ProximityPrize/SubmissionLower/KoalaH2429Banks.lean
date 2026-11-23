import ProximityPrize.SubmissionLower.KoalaH2430Banks

set_option autoImplicit false

namespace KoalaH2429Banks
open P1_7 (Stage Bank)

/-- Set the seed width. The stage geometry, node rows and pole moment stay fixed. -/
def resize (t : Bank) (U : ℕ) : Bank :=
  { t with shape := { t.shape with U := U } }

def resizeStage (s : Stage) (freeWidth movingWidth : ℕ) : Stage :=
  { s with free := resize s.free freeWidth, moving := resize s.moving movingWidth }

def stage00 : Stage := resizeStage KoalaH2430Banks.stage00 1053 17830
def stage01 : Stage := resizeStage KoalaH2430Banks.stage01 1168 20676
def stage02 : Stage := resizeStage KoalaH2430Banks.stage02 1182 20761
def stage03 : Stage := resizeStage KoalaH2430Banks.stage03 1287 25856
def stage04 : Stage := resizeStage KoalaH2430Banks.stage04 1299 28346
def stage05 : Stage := resizeStage KoalaH2430Banks.stage05 1400 25990
def stage06 : Stage := resizeStage KoalaH2430Banks.stage06 1517 30937
def stage07 : Stage := resizeStage KoalaH2430Banks.stage07 1988 34767
def stage08 : Stage := resizeStage KoalaH2430Banks.stage08 3757 47470
def stage09 : Stage := resizeStage KoalaH2430Banks.stage09 1423 36006
def stage10 : Stage := resizeStage KoalaH2430Banks.stage10 1913 45605
def stage11 : Stage := resizeStage KoalaH2430Banks.stage11 2845 50847
def stage12 : Stage := resizeStage KoalaH2430Banks.stage12 5533 69967
def stage13 : Stage := resizeStage KoalaH2430Banks.stage13 8098 98200
def stage14 : Stage := resizeStage KoalaH2430Banks.stage14 2497 61200
def stage15 : Stage := resizeStage KoalaH2430Banks.stage15 4658 83742
def stage16 : Stage := resizeStage KoalaH2430Banks.stage16 5944 101244
def stage17 : Stage := resizeStage KoalaH2430Banks.stage17 7389 125031
def stage18 : Stage := resizeStage KoalaH2430Banks.stage18 148512 182796
def stage19 : Stage := resizeStage KoalaH2430Banks.stage19 9557 159768
def stage20 : Stage := resizeStage KoalaH2430Banks.stage20 10481 177227
def stage21 : Stage := resizeStage KoalaH2430Banks.stage21 384284 295325

def widths : List (ℕ × ℕ) := [(1053, 17830), (1168, 20676), (1182, 20761), (1287, 25856), (1299, 28346), (1400, 25990), (1517, 30937), (1988, 34767), (3757, 47470), (1423, 36006), (1913, 45605), (2845, 50847), (5533, 69967), (8098, 98200), (2497, 61200), (4658, 83742), (5944, 101244), (7389, 125031), (148512, 182796), (9557, 159768), (10481, 177227), (384284, 295325)]

def stages : List Stage :=
  List.zipWith (fun (u : ℕ × ℕ) s => resizeStage s u.1 u.2) widths KoalaH2430Banks.stages
def terminalAt (U : ℕ) : Bank := resize KoalaH2430Banks.terminal U

def terminal : Bank := terminalAt 438444

end KoalaH2429Banks
