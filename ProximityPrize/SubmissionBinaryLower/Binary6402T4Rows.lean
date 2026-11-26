import ProximityPrize.SubmissionBinaryLower.Binary6402IntFarkas

set_option Elab.async false

/-!
# Shared Exact Sparse-Row Builders for Table 4A (32 non-`K` branches) and Table 4B (84 `K ≠ 0` branches)

Both the kernel-`decide` certificate modules (`B6401CertsT4a`, `B6401CertsT4b1`, `B6401CertsT4b2`)
and the algebraic soundness module (`B6401Table4Alg`) import this file so that the `Array SparseRow`
checked by `checkT4Bucket` and the `Array SparseRow` proved satisfied by algebraic `ker(D)` bounds
are **definitionally identical**!

All LHS entries are exact integers scaled by `BASE_DEN = 4 * N = 8,388,608`.
All static RHS fractions share denominator `BASE_DEN` so `dualRhsFrac` merges them in `O(1)` with
zero denominator blowup.
-/

namespace ProximityPrize.SubmissionBinaryLower
namespace B6402T4Rows

open B6401Params hiding A
open B6402HybridP64 (A)
open B6402IntFarkas

/-! ### Exact coefficient & RHS constructors -/

/-- Scale an integer coefficient `k` by `BASE_DEN = 4 * N`. -/
@[inline] def cI (k : ℤ) : ℤ := k * BASE_DEN

/-- Scale a half-integer `k / 2` by `BASE_DEN = 4 * N`. -/
@[inline] def cH (k : ℤ) : ℤ := k * (2 * (N : ℤ))

/-- Scale a quarter-integer `k / 4` by `BASE_DEN = 4 * N`. -/
@[inline] def cQ (k : ℤ) : ℤ := k * (N : ℤ)

/-- Scale `k * (wY / N)` by `BASE_DEN = 4 * N`. -/
@[inline] def cW (k : ℤ) : ℤ := k * (4 * (wY : ℤ))

/-- Static inequality row with RHS `num4 / 4 + (if eps then 30 / N else 0)` over `BASE_DEN = 4 * N`. -/
@[inline] def mkStat (entries : List (Nat × Int)) (num4 : ℤ) (eps : Bool := true) : SparseRow :=
  { entries := entries
    rhsNum := num4 * (N : ℤ) + if eps then 120 else 0
    rhsDen := BASE_DEN }

/-- Static equality row with RHS `num4 / 4` over `BASE_DEN = 4 * N`. -/
@[inline] def mkEq (entries : List (Nat × Int)) (num4 : ℤ := 0) : SparseRow :=
  { entries := entries
    rhsNum := num4 * (N : ℤ)
    rhsDen := BASE_DEN }

/-- Common prefix of `ubRows` and `eqRows` shared by ALL 116 Table 4 branches! -/
def baseT4Rows (ic cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : Nat) :
    List SparseRow × List SparseRow :=
  let eq0 : SparseRow := mkEq [(0, cI 1), (1, cI 1), (2, cI 1), (3, cI 1)] 4
  let ubCore : List SparseRow := [
    mkStat [(0, cI (-1)), (5, cI 1)] 0 false,
    mkStat [(1, cI (-1)), (6, cI 1)] 0 false,
    mkStat [(2, cI (-1)), (7, cI 1)] 0 false,
    mkStat [(3, cI (-1)), (8, cI 1)] 0 false,
    { entries := [(5, cI (-1)), (6, cI (-1)), (7, cI (-1)), (8, cI (-1))]
      rhsNum := -4 * (A : ℤ), rhsDen := BASE_DEN },
    { entries := [(ic, cI (-1))], rhsNum := -(cLoNum : ℤ), rhsDen := (cLoDen : ℤ) },
    { entries := [(ic, cI 1)], rhsNum := (cHiNum : ℤ), rhsDen := (cHiDen : ℤ) },
    { entries := [(6, cI 1), (7, cI 3), (8, cI 5), (ic, cW (-1))]
      rhsNum := 4 * (-(wY : ℤ) + 1), rhsDen := BASE_DEN },
    { entries := [(3, cI 1), (4, cI 2), (ic, cW (-1))]
      rhsNum := 4 * (-5 * (wY : ℤ) + 1), rhsDen := BASE_DEN }
  ]
  let ubLoG : List SparseRow :=
    if loGNum > 0 then
      [{ entries := [(5, cI (-1)), (6, cI 1), (7, cI 3), (8, cI 5), (ic, cW (-1))]
         rhsNum := (-(wY : ℤ) + 1) * (loGDen : ℤ) - (loGNum : ℤ) * (N : ℤ)
         rhsDen := (N : ℤ) * (loGDen : ℤ) }]
    else []
  let ubHiG : List SparseRow :=
    if hiGNum < hiGDen then
      [{ entries := [(5, cI 1), (6, cI (-1)), (7, cI (-3)), (8, cI (-5)), (ic, cW 1)]
         rhsNum := ((wY : ℤ) - 1) * (hiGDen : ℤ) + (hiGNum : ℤ) * (N : ℤ)
         rhsDen := (N : ℤ) * (hiGDen : ℤ) }]
    else []
  (ubCore ++ ubLoG ++ ubHiG, [eq0])

/-! ### Part 1: Table 4A (32 non-`K` branches) -/

/-- Branch tag for Table 4A (`36` total branches):
- `det` (1), `p0_zero` (1)
- `P0(m21Nz, rGt, p0M10D4, q2M21M10)` (2 + 8 = 10 valid combos)
- `b1c1(rGt, r4g4, bCase)` (2 × 2 × 6 = 24 combos; `bCase ∈ 0..5`:
  `0=B1_D2_holds, 1=B1_D2_fail, 2=B2_ODE_holds, 3=B2_ODE_fail, 4=B2_W2b_ODE_holds, 5=B2_W2b_ODE_fail`) -/
inductive T4ABranch where
  | det
  | p0Zero
  | p0 (m21Nz rGt p0M10D4 q2M21M10 : Bool)
  | b1c1 (rGt r4g4 : Bool) (bCase : Nat)
  deriving Repr, DecidableEq

def t4aNumVars : T4ABranch → Nat
  | .det => 10
  | .p0Zero => 10
  | .p0 .. => 23
  | .b1c1 .. => 21

/-- Static `(ubExtra, eqExtra)` rows for each of the 32 Table 4A branches, matching
`gen_exact_master_6401.build_nonK_branch_specs` row-for-row! -/
def t4aStaticRows : T4ABranch → List SparseRow × List SparseRow
  | .det =>
    let ic := 9
    ([mkStat [(1, cI 1), (2, cI 11), (3, cI 29), (4, cI 18), (ic, cH (-9))] (-50),
      mkStat [(2, cI 2), (3, cI 5), (4, cI 3), (ic, cQ (-3))] (-8)], [])
  | .p0Zero =>
    let ic := 9
    ([mkStat [(1, cI 1), (2, cI 11), (3, cI 29), (4, cI 18), (ic, cH (-9))] (-50),
      mkStat [(6, cI 2), (7, cI 4), (8, cI 6), (ic, cI (-1))] (-12)], [])
  | .p0 m21Nz rGt p0M10D4 q2M21M10 =>
    let ic := 22
    let rCore : List SparseRow := [
      mkStat [(9, cH 1), (13, cI 1), (ic, cH (-1))] (-6),
      mkStat [(9, cH 1), (14, cI 1), (ic, cH (-1))] (-4),
      mkStat [(15, cI 1), (1, cI (-1))] 0 false,
      mkStat [(16, cI 1), (2, cI (-1))] 0 false,
      mkStat [(17, cI 1), (3, cI (-1))] 0 false,
      mkStat [(18, cI 1), (4, cI (-1))] 0 false,
      mkStat [(19, cI 1), (15, cI (-1))] 0 false,
      mkStat [(20, cI 1), (16, cI (-1))] 0 false,
      mkStat [(21, cI 1), (17, cI (-1))] 0 false,
      mkStat [(19, cI 1), (6, cI (-1))] 0 false,
      mkStat [(20, cI 1), (7, cI (-1))] 0 false,
      mkStat [(21, cI 1), (8, cI (-1))] 0 false,
      mkStat [(6, cI 1), (19, cI (-1)), (1, cI (-1)), (15, cI 1)] 0 false,
      mkStat [(7, cI 1), (20, cI (-1)), (2, cI (-1)), (16, cI 1)] 0 false,
      mkStat [(8, cI 1), (21, cI (-1)), (3, cI (-1)), (17, cI 1)] 0 false,
      mkStat [(1, cI 4), (15, cI (-3)), (2, cI 16), (16, cI (-5)), (3, cI 34), (17, cI (-5)), (4, cI 18), (ic, cH (-9))] (-50),
      { entries := [(6, cI 2), (19, cI (-1)), (7, cI 4), (20, cI (-1)), (8, cI 6), (21, cI (-1)), (ic, cW (-1))]
        rhsNum := 4 * (-(wY : ℤ) + 1), rhsDen := BASE_DEN },
      mkStat [(1, cI 1), (15, cI (-1)), (2, cI 4), (16, cI (-2)), (3, cI 8), (17, cI (-2)), (4, cI 4), (9, cI 1), (ic, cI (-1))] (-12)
    ]
    let rM21 : List SparseRow :=
      if !m21Nz then [mkStat [(2, cI 2), (3, cI 4), (4, cI 2), (ic, cH (-1))] (-4)]
      else
        [mkStat [(9, cH 1), (12, cI 1), (ic, cH (-1))] (-8),
         mkStat [(10, cI 1), (12, cI 2), (ic, cI (-1))] (-14)]
    let rQ2 : List SparseRow :=
      if !q2M21M10 then
        [mkStat [(10, cI 1), (13, cI 2), (ic, cI (-1))] (-10),
         mkStat [(1, cI 1), (15, cI (-1)), (2, cI 4), (16, cI (-2)), (3, cI 8), (17, cI (-2)), (4, cI 4), (13, cI (-2))] 0]
      else
        [mkStat [(10, cI 1), (14, cI 2), (ic, cI (-1))] (-6),
         mkStat [(1, cI 1), (15, cI (-1)), (2, cI 4), (16, cI (-2)), (3, cI 8), (17, cI (-2)), (4, cI 4), (12, cI (-1)), (14, cI (-1))] 0]
    let (rR, eqR) : List SparseRow × List SparseRow :=
      if !rGt then
        ([mkStat [(9, cI (-1)), (10, cI 1)] 2,
          mkStat [(9, cI (-1)), (11, cI 1)] 2,
          mkStat [(15, cI 1), (16, cI 3), (17, cI 5), (18, cI 2), (9, cI (-4)), (ic, cH (-1))] (-2)], [])
      else
        ([mkStat [(9, cI 1), (10, cI (-1))] (-2),
          mkStat [(15, cI 1), (16, cI 3), (17, cI 5), (18, cI 2), (10, cI (-4)), (ic, cH (-1))] (-10)],
         [mkEq [(10, cI 1), (11, cI (-1))] 0])
    let rP0 : List SparseRow :=
      if !p0M10D4 then [mkStat [(2, cI 1), (16, cI 1), (3, cI 3), (17, cI 1), (4, cI 2), (10, cI (-2)), (12, cI (-1))] 0]
      else
        [mkStat [(10, cI 1), (14, cI 2), (ic, cI (-1))] (-6),
         mkStat [(2, cI 1), (16, cI 1), (3, cI 3), (17, cI 1), (4, cI 2), (9, cI (-2)), (14, cI (-1))] 0]
    (rCore ++ rM21 ++ rQ2 ++ rR ++ rP0, eqR)
  | .b1c1 rGt r4g4 bCase =>
    let ic := 20
    let eq0 : List SparseRow := [mkEq [(2, cI 1), (3, cI 3), (4, cI 2), (14, cI 1), (15, cI 1), (16, cI 1), (11, cI (-1))] 0]
    let rCore : List SparseRow := [
      mkStat [(14, cI 1), (1, cI (-1))] 0 false,
      mkStat [(15, cI 1), (2, cI (-1)), (3, cI (-1))] 0 false,
      mkStat [(19, cI 1), (18, cI (-1))] 0 false,
      mkStat [(18, cI 1), (19, cI 1), (9, cH (-1))] 0,
      mkStat [(1, cI 1), (2, cI 3), (3, cI 3), (14, cI (-1)), (15, cI (-3)), (17, cI (-1))] 0,
      mkStat [(11, cI 8), (17, cI 1), (10, cI (-1)), (ic, cI (-4))] (-40),
      mkStat [(1, cI 1), (2, cI 11), (3, cI 29), (4, cI 18), (10, cI (-1)), (ic, cI (-4))] (-40),
      mkStat [(3, cI 1), (4, cI 2), (10, cI (-1))] 0,
      mkStat [(10, cI 1), (ic, cH (-1))] (-10),
      mkStat [(9, cH 1), (10, cH (-1)), (11, cI 1), (ic, cQ (-1))] (-1),
      mkStat [(11, cI 2), (12, cI 1), (ic, cI (-1))] (-10),
      mkStat [(11, cI 2), (13, cI 1), (ic, cI (-1))] (-10),
      mkStat [(6, cI 1), (7, cI 1), (14, cI (-1)), (15, cI (-1)), (16, cI (-1)), (13, cI (-1))] 0,
      mkStat [(1, cI 1), (2, cI 11), (3, cI 29), (4, cI 18), (11, cI (-8)), (17, cI (-1))] 0,
      mkStat [(1, cI 1), (2, cI 8), (3, cI 20), (4, cI 10), (11, cI (-5)), (17, cI (-1))] 0,
      mkStat [(1, cI 1), (2, cI 6), (3, cI 12), (4, cI 6), (11, cI (-3)), (17, cI (-1))] 0,
      mkStat [(18, cI 4), (17, cI (-1))] 0,
      mkStat [(18, cI 2), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 3), (14, cI (-1)), (15, cI (-3)), (16, cI (-1))] 0
    ]
    let (rR, eqR) : List SparseRow × List SparseRow :=
      if !rGt then ([mkStat [(9, cI (-1)), (12, cI 1)] 2, mkStat [(9, cI (-1)), (13, cI 1)] 2], [])
      else ([mkStat [(9, cI 1), (12, cI (-1))] (-2)], [mkEq [(12, cI 1), (13, cI (-1))] 0])
    let rT : List SparseRow :=
      if !r4g4 then [mkStat [(17, cI 1), (9, cI (-4)), (ic, cH (-1))] (-2)]
      else [mkStat [(17, cI 1), (10, cI (-1)), (12, cI (-4))] 0]
    let b1Rows : List SparseRow := [
      -- (an0=1, am1=0, ae1=4, ae2=8, aerem=7, ad=0, aL=3/2)
      mkStat [(10, cI 1), (17, cI (-1)), (1, cI 1), (2, cI 3), (4, cI (-3)), (0, cI (-1)), (14, cI (-5)), (15, cI (-11)), (16, cI (-7))] 0,
      -- (an0=1, am1=0, ae1=4, ae2=5, aerem=3, ad=0, aL=2)
      mkStat [(10, cI 1), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI (-1)), (4, cI (-4)), (0, cI (-1)), (14, cI (-5)), (15, cI (-8)), (16, cI (-3))] 0
    ]
    let rB : List SparseRow :=
      if bCase == 0 then -- B1_D2_holds
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(10, cI 1), (17, cI 1), (1, cI (-1)), (2, cI (-3)), (3, cI (-7)), (4, cI (-4)), (0, cI (-1)), (9, cI (-5)), (14, cI (-2)), (15, cI (-2)), (16, cI (-2))] 0,
         mkStat [(10, cI (-1)), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 7), (4, cI 4), (0, cI 1), (9, cI 5), (14, cI 2), (15, cI 2), (16, cI 2)] 0,
         mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (10, cI 1), (ic, cH 1), (9, cI 4)] 14,
         mkStat [(1, cI 3), (2, cI 3), (3, cI 3), (14, cI (-3)), (15, cI (-3)), (16, cI (-2)), (18, cI (-2)), (17, cI (-1))] 0] ++ b1Rows
      else if bCase == 1 then -- B1_D2_fail
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(10, cI 1), (17, cI 1), (1, cI (-1)), (2, cI (-3)), (3, cI (-7)), (4, cI (-4)), (0, cI (-1)), (9, cI (-5)), (14, cI (-2)), (15, cI (-2)), (16, cI (-2))] 0,
         mkStat [(10, cI (-1)), (17, cI (-1)), (1, cI 1), (2, cI 3), (3, cI 7), (4, cI 4), (0, cI 1), (9, cI 5), (14, cI 2), (15, cI 2), (16, cI 2)] 0,
         mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (10, cI (-1)), (ic, cH (-1)), (9, cI (-4))] (-14)]
      else if bCase == 2 then -- B2_ODE_holds
        [mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (9, cI (-5)), (11, cI (-2))] (-12),
         mkStat [(1, cI 2), (2, cI 3), (3, cI 3), (14, cI (-2)), (15, cI (-3)), (16, cI (-1)), (17, cI (-1))] 0] ++ b1Rows
      else if bCase == 3 then -- B2_ODE_fail
        [mkStat [(0, cI (-6)), (1, cI (-4)), (14, cI (-2)), (15, cI (-6)), (9, cI (-5)), (11, cI (-2))] (-12),
         mkStat [(9, cI 4), (0, cI (-8)), (1, cI (-3)), (14, cI (-5)), (15, cI (-11)), (16, cI (-8)), (10, cI (-2)), (17, cI (-1)), (2, cI 3), (3, cI 3)] 0]
      else if bCase == 4 then -- B2_W2b_ODE_holds
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(17, cI (-1)), (10, cI (-1)), (1, cI 2), (2, cI 4), (3, cI 4), (14, cI (-2)), (15, cI (-4))] 0,
         mkStat [(1, cI 2), (2, cI 3), (3, cI 3), (14, cI (-2)), (15, cI (-3)), (16, cI (-1)), (17, cI (-1))] 0] ++ b1Rows
      else -- bCase == 5: B2_W2b_ODE_fail
        [mkStat [(0, cI 6), (1, cI 4), (14, cI 2), (15, cI 6), (9, cI 5), (11, cI 2)] 12,
         mkStat [(17, cI (-1)), (10, cI (-1)), (1, cI 2), (2, cI 4), (3, cI 4), (14, cI (-2)), (15, cI (-4))] 0,
         mkStat [(9, cI 4), (0, cI (-8)), (1, cI (-3)), (14, cI (-5)), (15, cI (-11)), (16, cI (-8)), (10, cI (-2)), (17, cI (-1)), (2, cI 3), (3, cI 3)] 0]
    (rCore ++ rR ++ rT ++ rB, eq0 ++ eqR)

def buildT4ARows (br : T4ABranch) (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : Nat) :
    Array SparseRow × Array SparseRow :=
  let ic := t4aNumVars br - 1
  let (ubB, eqB) := baseT4Rows ic cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
  let (ubS, eqS) := t4aStaticRows br
  ((ubB ++ ubS).toArray, (eqB ++ eqS).toArray)

/-! ### Part 2: Table 4B (84 `K ≠ 0` branches, `nv = 49, ic = 48`) -/

/-- Branch tag for Table 4B (`2 × 2 × 3 × 7 = 84` branches):
- `rGt`: `false = "r<=d+0.5"`, `true = "r>d+0.5"`
- `vCancel`: `false = "V_no_cancel"`, `true = "V_cancel"`
- `q1Case`: `0 = "D8g0"`, `1 = "D4r2g2"`, `2 = "r4g4"`
- `odeCase`:
  `0 = "ODE_holds_B1h"`, `1 = "ODE_holds_W2a1"`, `2 = "ODE_holds_W2a2"`, `3 = "ODE_holds_W2b"`,
  `4 = "ODE_fail_B1h"`, `5 = "ODE_fail_W2a"`, `6 = "ODE_fail_W2b"` -/
structure T4BBranch where
  rGt : Bool
  vCancel : Bool
  q1Case : Nat
  odeCase : Nat
  deriving Repr, DecidableEq

/-- Exact STEP15 row constructor (inputs scaled by 2 to stay pure `ℤ`!), matching
`gen_exact_master_6401.add_r15` bit-for-bit!
`mode`: `0 = "diff"`, `1 = "c04_w2a1"`, `2 = "c04_w2a2"`. -/
def mkR15 (r2 : Array ℤ) (mode : Nat) : SparseRow :=
  let am0   := r2[0]! ; let amb   := r2[1]! ; let am1  := r2[2]! ; let am2   := r2[3]! ; let ak3  := r2[4]!
  let amL0  := r2[5]! ; let amu1  := r2[6]! ; let amuO := r2[7]! ; let alam  := r2[8]! ; let adin := r2[9]!
  let admL  := r2[10]!; let adoth := r2[11]!; let aL0  := r2[12]!; let aa1   := r2[13]!; let aLnoU := r2[14]!
  -- Each raw coefficient is (value / 2), except col 9 which is -(1/2)*aa1 = -(aa1_2 / 4)!
  let base : List (Nat × Int) := [
    (0, cH (-am0)), (1, cH (-am0)), (18, cH (am0 - am1)), (26, cH (-amb)),
    (2, cH (-am2)), (19, cH am2), (3, cH (-am2)), (20, cH (am2 - ak3)),
    (27, cH (-amL0)), (34, cH (amL0 - admL + adoth)),
    (39, cH (amuO - amu1)), (29, cH (-amuO)),
    (16, cH (-alam)), (31, cH (adoth - adin)), (17, cH (aa1 - adoth)),
    (21, cH (-2 * aL0 + 2 * aLnoU)), (4, cH (-2 * aLnoU)), (9, cQ (-aa1))
  ]
  let extra : List (Nat × Int) × ℤ :=
    if mode == 0 then ([(11, cI 1), (30, cI (-1))], 0)
    else if mode == 1 then ([(11, cI 2), (13, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)], -12)
    else ([(11, cI 1), (12, cI (-1)), (10, cI 2), (13, cI (-2))], -16)
  -- Note: accumDualCols sums duplicate keys identically to merging them, and 16/9/17 only appear twice in mode 1!
  mkStat ((base ++ extra.1).filter fun p => p.2 != 0) extra.2 true

def row0A_2   : Array ℤ := #[2, 4, 0, -11, -4, -10, 0, 11, 6, 6, -4, 1, -2, 0, -2]
def row0C0_2  : Array ℤ := #[2, 7, 0, -8, -10, -13, 2, 10, 9, 2, -16, 2, -5, 0, -5]
def row0C1_2  : Array ℤ := #[2, 3, 0, -8, -2, -9, 2, 10, 5, 10, -16, 2, -1, 0, -1]
def rowC04_2  : Array ℤ := #[8, 8, 0, -8, -8, -8, 0, 8, 8, 8, 0, 8, -4, 0, -4]

/-- Static `(ubExtra, eqExtra)` rows for each of the 84 Table 4B branches, matching
`gen_exact_master_6401.build_exact_K_rows` row-for-row! -/
def t4bStaticRows (br : T4BBranch) : List SparseRow × List SparseRow :=
  let ic := 48
  let eqCore : List SparseRow := [
    mkEq [(44, cI 1), (45, cI 1), (31, cI (-1))],
    mkEq [(46, cI 1), (47, cI 1), (34, cI (-1))],
    mkEq [(2, cI 1), (19, cI (-1)), (3, cI 2), (20, cI (-1)), (4, cI 1), (25, cI 1), (10, cI (-1))],
    mkEq [(18, cI 1), (34, cI 1), (35, cI (-1))],
    mkEq [(0, cI 1), (1, cI 1), (18, cI (-1)), (2, cI 1), (19, cI (-1)), (3, cI 1), (20, cI (-1)), (28, cI (-1))],
    mkEq [(0, cI 1), (1, cI 1), (2, cI 1), (19, cI (-1)), (3, cI 1), (20, cI (-1)), (26, cI 1), (37, cI (-1))],
    mkEq [(19, cI 1), (20, cI 1), (26, cI 1), (27, cI (-1)), (29, cI 1), (13, cI (-1))],
    mkEq [(10, cI 2), (19, cI 1), (20, cI 1), (26, cI (-1)), (30, cI 1), (12, cI (-1))],
    mkEq [(12, cI 1), (10, cI (-2)), (13, cI 2), (19, cI (-3)), (20, cI (-3)), (34, cI 3), (35, cI (-1)), (36, cI (-1))],
    mkEq [(33, cI 1), (32, cI 1), (3, cI 2), (20, cI (-1)), (4, cI 2), (38, cI 1), (11, cI (-1))],
    mkEq [(41, cI 1), (42, cI 1), (43, cI 1), (21, cI (-1))]
  ]
  let ubCore : List SparseRow := [
    mkStat [(44, cI 1), (46, cI 1), (19, cI (-1))] 0 false,
    mkStat [(45, cI 1), (47, cI 1), (20, cI (-1))] 0 false,
    mkStat [(18, cI 1), (1, cI (-1))] 0 false,
    mkStat [(19, cI 1), (2, cI (-1))] 0 false,
    mkStat [(20, cI 1), (3, cI (-1))] 0 false,
    mkStat [(21, cI 1), (4, cI (-1))] 0 false,
    mkStat [(22, cI 1), (18, cI (-1))] 0 false,
    mkStat [(22, cI 1), (6, cI (-1))] 0 false,
    mkStat [(6, cI 1), (22, cI (-1)), (1, cI (-1)), (18, cI 1)] 0 false,
    mkStat [(23, cI 1), (19, cI (-1))] 0 false,
    mkStat [(23, cI 1), (7, cI (-1))] 0 false,
    mkStat [(7, cI 1), (23, cI (-1)), (2, cI (-1)), (19, cI 1)] 0 false,
    mkStat [(24, cI 1), (20, cI (-1))] 0 false,
    mkStat [(24, cI 1), (8, cI (-1))] 0 false,
    mkStat [(8, cI 1), (24, cI (-1)), (3, cI (-1)), (20, cI 1)] 0 false,
    mkStat [(6, cI 2), (22, cI (-1)), (7, cI 4), (23, cI (-1)), (8, cI 6), (24, cI (-1)), (ic, cH (-1))] (-2),
    mkStat [(26, cI 1), (25, cI (-1))] 0 false,
    mkStat [(26, cI 1), (27, cI 1), (19, cI (-1)), (20, cI (-1))] 0 false,
    mkStat [(27, cI 1), (16, cI (-1))] 0,
    mkStat [(17, cI 1), (9, cH (-1))] 0,
    mkStat [(31, cI 1), (32, cI 1), (33, cI 1), (34, cI 1), (17, cI (-1))] 0 false,
    mkStat [(33, cI 1), (0, cI (-1))] 0 false,
    mkStat [(32, cI 1), (18, cI (-1))] 0 false,
    mkStat [(34, cI 1), (27, cI (-1))] 0 false,
    mkStat [(27, cI 1), (43, cI 2), (16, cI (-1))] 0,
    mkStat [(39, cI 1), (32, cI 1), (18, cI (-1))] 0 false,
    mkStat [(39, cI 1), (40, cI 1), (29, cI (-1))] 0 false,
    mkStat [(20, cI 2), (31, cI (-2)), (34, cI (-2)), (26, cI (-1)), (41, cI 2), (43, cI 2), (16, cI (-1)), (40, cI (-1))] 0,
    mkStat [(33, cI 1), (32, cI 1), (27, cI 2), (34, cI (-2)), (30, cI (-1))] 0,
    mkStat [(33, cI 1), (18, cI 1), (39, cI (-1)), (27, cI 2), (34, cI (-2)), (30, cI (-1))] 0,
    mkStat [(33, cI 1), (32, cI 1), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (12, cI (-1))] 0,
    mkStat [(31, cI 3), (32, cI 1), (33, cI 1), (34, cI 1), (11, cI (-1))] 0,
    mkStat [(44, cI 3), (46, cI 1), (32, cI 1), (33, cI 1), (3, cI 2), (20, cI (-1)), (4, cI 2), (11, cI (-1))] 0,
    mkStat [(33, cI 4), (32, cI 3), (44, cI 12), (46, cI 2), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (11, cI (-1)), (ic, cI (-4))] (-40),
    mkStat [(33, cI 4), (32, cI 3), (44, cI 20), (46, cI 10), (25, cI (-8)), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (11, cI (-1)), (ic, cI (-4))] (-40),
    mkStat [(12, cI 1), (10, cI (-2)), (17, cI 4), (13, cI 10), (16, cI 8), (11, cI (-1)), (ic, cI (-4))] (-40),
    mkStat [(33, cI 4), (32, cI 3), (44, cI 12), (46, cI 2), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (16, cI (-8)), (13, cI (-10))] 0,
    mkStat [(33, cI 4), (32, cI 3), (44, cI 20), (46, cI 10), (25, cI (-8)), (1, cI 4), (18, cI (-3)), (2, cI 16), (19, cI (-5)), (3, cI 34), (20, cI (-5)), (4, cI 18), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (16, cI (-8)), (13, cI (-10))] 0,
    mkStat [(33, cI 4), (32, cI 3), (18, cI 1), (19, cI 3), (20, cI 3), (3, cI 2), (4, cI 2), (10, cI 2), (17, cI (-4)), (12, cI (-1)), (13, cI (-2))] 0,
    mkStat [(1, cI 1), (18, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
    mkStat [(31, cI 2), (34, cI 1), (27, cI 1), (2, cI 1), (19, cI (-1)), (3, cI 3), (20, cI (-1)), (4, cI 2), (10, cI (-1)), (16, cI (-1))] 0,
    mkStat [(11, cI 1), (ic, cH (-1))] (-10),
    mkStat [(2, cI 1), (3, cI 2), (4, cI 1), (10, cI 1), (12, cI (-1))] 0,
    mkStat [(12, cI 1), (ic, cH (-1))] (-6),
    mkStat [(9, cH 5), (17, cI (-2)), (10, cI 1), (16, cI 1), (11, cH (-1)), (12, cH (-1))] 0,
    mkStat [(9, cH 1), (10, cI 1), (16, cI 1), (14, cI 2), (17, cI (-2)), (12, cH (-1)), (ic, cQ (-1))] (-1),
    mkStat [(14, cI 5), (10, cI 2), (16, cI 2), (17, cI (-4)), (ic, cI (-1))] (-6),
    mkStat [(22, cI 1), (23, cI 1), (24, cI 1), (15, cI (-1))] 0
  ]
  let (ubR, eqR) : List SparseRow × List SparseRow :=
    if !br.rGt then ([mkStat [(9, cI (-1)), (14, cI 1)] 2, mkStat [(9, cI (-1)), (15, cI 1)] 2], [])
    else ([mkStat [(9, cI 1), (14, cI (-1))] (-2)], [mkEq [(14, cI 1), (15, cI (-1))]])
  let (ubV, eqV) : List SparseRow × List SparseRow :=
    if !br.vCancel then
      ([mkStat [(9, cH 1), (11, cH (-1)), (13, cI 1), (16, cI 1), (ic, cQ (-1))] (-1),
        mkStat [(13, cI 2), (16, cI 2), (15, cI 1), (ic, cI (-1))] (-10)], [])
    else ([], [mkEq [(13, cI 1), (9, cI (-1)), (10, cI (-1)), (14, cI (-1)), (17, cI 2)]])
  let ubQ1 : List SparseRow :=
    if br.q1Case == 0 then [mkStat [(9, cI (-4)), (17, cI 4), (10, cI (-2)), (12, cI 1), (13, cI 2), (ic, cH (-1))] (-2)]
    else if br.q1Case == 1 then [mkStat [(9, cI (-2)), (17, cI 4), (10, cI (-2)), (13, cI 2), (14, cI (-2))] 0]
    else [mkStat [(10, cI (-2)), (17, cI 4), (11, cI (-1)), (12, cI 1), (13, cI 2), (14, cI (-4))] 0]
  let (ubODE, eqODE) : List SparseRow × List SparseRow :=
    if br.odeCase < 4 then
      let u0 : List SparseRow := [
        mkStat [(1, cI 1), (32, cI (-1)), (2, cI 2), (19, cI (-1)), (3, cI 4), (20, cI (-1)), (4, cI 2), (16, cI (-1)), (13, cI (-1))] 0,
        mkStat [(1, cI 1), (27, cI 1), (32, cI (-1)), (16, cI (-1)), (29, cI (-1))] 0,
        mkR15 row0A_2 0
      ]
      if br.odeCase == 0 then -- ODE_holds_B1h
        (u0 ++ [mkR15 row0C0_2 0, mkR15 row0C1_2 0],
         [mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]])
      else if br.odeCase == 1 then -- ODE_holds_W2a1
        (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4,
                mkR15 rowC04_2 1], [])
      else if br.odeCase == 2 then -- ODE_holds_W2a2
        (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4,
                mkR15 rowC04_2 2], [])
      else -- ODE_holds_W2b
        (u0 ++ [mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4),
                mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
    else
      let u0 : List SparseRow := [
        mkStat [(9, cI 2), (17, cI (-4)), (44, cI 4), (32, cI 4), (34, cI 4), (33, cI 5),
                (0, cI (-2)), (1, cI (-2)), (18, cI 2), (3, cI 2), (4, cI 6),
                (36, cI (-1)), (35, cI (-2)), (11, cI (-2))] 0
      ]
      if br.odeCase == 4 then -- ODE_fail_B1h
        (u0 ++ [mkR15 row0C0_2 0, mkR15 row0C1_2 0],
         [mkEq [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))]])
      else if br.odeCase == 5 then -- ODE_fail_W2a
        (u0 ++ [mkStat [(37, cI (-2)), (16, cI (-2)), (9, cI (-5)), (17, cI 4)] (-4),
                mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
      else -- ODE_fail_W2b
        (u0 ++ [mkStat [(37, cI (-1)), (11, cI (-1)), (30, cI (-1))] (-4),
                mkStat [(37, cI 1), (16, cI 2), (9, cI 5), (17, cI (-4)), (11, cI (-1)), (30, cI (-1))] 4], [])
  (ubCore ++ ubR ++ ubV ++ ubQ1 ++ ubODE, eqCore ++ eqR ++ eqV ++ eqODE)

def buildT4BRows (br : T4BBranch) (cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen : Nat) :
    Array SparseRow × Array SparseRow :=
  let (ubB, eqB) := baseT4Rows 48 cLoNum cLoDen cHiNum cHiDen loGNum loGDen hiGNum hiGDen
  let (ubS, eqS) := t4bStaticRows br
  ((ubB ++ ubS).toArray, (eqB ++ eqS).toArray)

/-! ### Part 3: Bin-level bucket-ladder checker (`checkT4Bin`) -/

/-- One bin `[cLo, cHi]` covered by a contiguous partition of `g ∈ [0, 1]` into buckets! -/
structure T4BinCert where
  cLoNum : Nat
  cLoDen : Nat
  cHiNum : Nat
  cHiDen : Nat
  buckets : List T4BucketCert
  deriving Repr

/-- Check that `buckets` form a contiguous partition `[0/1 = lo_0 < hi_0 = lo_1 < ... < hi_{k-1} = 1/1]`,
every bucket passes `checkT4Bucket`, AND the summed integer caps stay below our global `2^64` budgets! -/
def checkT4Bin (nv : Nat)
    (rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow)
    (c1Cap c0Cap q2Cap : Nat) (bin : T4BinCert) : Bool :=
  let rec go (curN curD : Nat) (sumC1 sumC0 sumQ2 : Nat) : List T4BucketCert → Bool
    | [] => curN == curD && curD > 0 && sumC1 ≤ c1Cap && sumC0 ≤ c0Cap && sumQ2 ≤ q2Cap
    | b :: rest =>
      if b.loGDen == 0 || b.hiGDen == 0 then false
      else if curN * b.loGDen != b.loGNum * curD then false
      else if !(b.loGNum * b.hiGDen < b.hiGNum * b.loGDen) then false
      else if b.hiGNum > b.hiGDen then false
      else
        let (ub, eq) := rowBuilder bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b.loGNum b.loGDen b.hiGNum b.hiGDen
        if !checkT4Bucket nv ub eq bin.cLoNum bin.cLoDen bin.cHiNum bin.cHiDen b then false
        else
          let (c1', c0', q2') :=
            if b.m == 0 then (0, 0, 0)
            else (b.cap1.c1Bkt, b.cap1.c0Bkt, b.cap2.c1Bkt * 3850 + b.cap2.c0Bkt)
          go b.hiGNum b.hiGDen (sumC1 + c1') (sumC0 + c0') (sumQ2 + q2') rest
  go 0 1 0 0 0 bin.buckets

/-- Check that a list of `T4BinCert`s forms a contiguous cover of `[startLo, endHi]` and every bin passes `checkT4Bin`! -/
def checkT4Branch (nv : Nat)
    (rowBuilder : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array SparseRow × Array SparseRow)
    (startN startD endN endD c1Cap c0Cap q2Cap : Nat) (bins : List T4BinCert) : Bool :=
  let rec go (curN curD : Nat) : List T4BinCert → Bool
    | [] => curN * endD == endN * curD
    | bin :: rest =>
      if bin.cLoDen == 0 || bin.cHiDen == 0 then false
      else if curN * bin.cLoDen != bin.cLoNum * curD then false
      else if !checkT4Bin nv rowBuilder c1Cap c0Cap q2Cap bin then false
      else go bin.cHiNum bin.cHiDen rest
  go startN startD bins

end B6402T4Rows
end ProximityPrize.SubmissionBinaryLower
