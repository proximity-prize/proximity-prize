import ProximityPrize.SubmissionLower.MovingFiberProfile6811
import ProximityPrize.SubmissionLower.MovingFiberSources6811E

namespace ProximityPrize.SubmissionLower.MovingFiberCatalog6811
open MovingFiberProfile6811 MovingFiberInterpolation6811
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

local instance (P : Params) : Decidable P.WellFormed := by
  unfold Params.WellFormed
  infer_instance

def source0 : Params := ⟨132,54,24,180,1841,5,7⟩
def source1 : Params := ⟨134,56,25,180,2962,6,8⟩
def source2 : Params := ⟨136,56,25,185,2701,6,8⟩
def source3 : Params := ⟨116,46,21,158,2931,5,7⟩
def source4 : Params := ⟨114,45,21,155,3279,5,7⟩
def source5 : Params := ⟨158,63,29,215,3147,7,10⟩
def source6 : Params := ⟨166,73,34,226,3265,8,9⟩
def source7 : Params := ⟨114,47,21,154,2947,5,7⟩
def source8 : Params := ⟨142,56,26,193,2867,6,9⟩
def source9 : Params := ⟨174,76,36,236,2841,8,9⟩
def source10 : Params := ⟨170,71,32,231,3241,8,10⟩
def source11 : Params := ⟨98,41,19,132,2531,4,6⟩
def source12 : Params := ⟨142,59,27,193,2513,6,9⟩
def source13 : Params := ⟨158,69,32,214,2505,7,8⟩
def source14 : Params := ⟨146,58,27,198,2596,6,9⟩
def source15 : Params := ⟨98,41,19,133,2422,4,6⟩
def source16 : Params := ⟨150,60,28,204,2367,6,9⟩
def source17 : Params := ⟨162,71,33,218,2419,7,8⟩
def source18 : Params := ⟨114,47,22,155,2870,5,7⟩
def source19 : Params := ⟨166,66,31,226,2765,7,10⟩
def source20 : Params := ⟨174,76,36,237,2820,8,9⟩
def source21 : Params := ⟨111,46,22,151,3307,5,7⟩
def source22 : Params := ⟨189,83,39,256,3238,9,10⟩
def source23 : Params := ⟨114,45,20,155,3266,5,7⟩
def source24 : Params := ⟨190,84,40,258,3169,9,10⟩
def source25 : Params := ⟨111,46,21,151,3286,5,7⟩
def source26 : Params := ⟨189,83,39,257,3208,9,10⟩
def source27 : Params := ⟨72,31,14,98,979,2,3⟩
def source28 : Params := ⟨104,45,21,142,1697,4,5⟩
def source29 : Params := ⟨104,45,21,141,1835,4,6⟩
def source30 : Params := ⟨136,59,27,185,2423,6,7⟩

def sources : Fin 31 → Params := ![source0,source1,source2,source3,source4,source5,source6,source7,source8,source9,source10,source11,source12,source13,source14,source15,source16,source17,source18,source19,source20,source21,source22,source23,source24,source25,source26,source27,source28,source29,source30]
def groups : Fin 20 → Fin 3 → Params := ![![source0,source0,source0],
  ![source1,source1,source1],
  ![source2,source2,source2],
  ![source3,source3,source3],
  ![source4,source5,source6],
  ![source7,source8,source9],
  ![source10,source10,source10],
  ![source11,source12,source13],
  ![source11,source14,source13],
  ![source15,source16,source17],
  ![source18,source19,source20],
  ![source21,source5,source22],
  ![source23,source5,source24],
  ![source25,source5,source24],
  ![source25,source5,source26],
  ![source21,source5,source26],
  ![source27,source27,source27],
  ![source28,source28,source28],
  ![source29,source29,source29],
  ![source30,source30,source30]]

theorem wellFormed (g : Fin 20) (j : Fin 3) : (groups g j).WellFormed := by
  have h : ∀ g : Fin 20, ∀ j : Fin 3, (groups g j).WellFormed := by decide +kernel
  exact h g j

theorem common_caps (g : Fin 20) (j : Fin 3) :
    (groups g j).B ≤ 84 ∧ (groups g j).U ≤ 258 ∧ (groups g j).L ≤ 3307 ∧ (groups g j).s ≤ 40 := by
  have h : ∀ g : Fin 20, ∀ j : Fin 3,
    (groups g j).B ≤ 84 ∧ (groups g j).U ≤ 258 ∧ (groups g j).L ≤ 3307 ∧ (groups g j).s ≤ 40 := by decide +kernel
  exact h g j

theorem exists_source {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) (i : Fin 31) :
    ∃ P, Interpolant (sources i).m (sources i).B (sources i).s (sources i).U
      (sources i).L (sources i).k (sources i).n0 nodes u0 u1 P := by
  fin_cases i
  · change ∃ P, Interpolant 132 54 24 180 1841 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P0.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 134 56 25 180 2962 6 8 nodes u0 u1 P
    exact MovingFiberSources6811.P1.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 136 56 25 185 2701 6 8 nodes u0 u1 P
    exact MovingFiberSources6811.P2.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 116 46 21 158 2931 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P3.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 45 21 155 3279 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P4.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 158 63 29 215 3147 7 10 nodes u0 u1 P
    exact MovingFiberSources6811.P5.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 166 73 34 226 3265 8 9 nodes u0 u1 P
    exact MovingFiberSources6811.P6.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 47 21 154 2947 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P7.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 142 56 26 193 2867 6 9 nodes u0 u1 P
    exact MovingFiberSources6811.P8.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 174 76 36 236 2841 8 9 nodes u0 u1 P
    exact MovingFiberSources6811.P9.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 170 71 32 231 3241 8 10 nodes u0 u1 P
    exact MovingFiberSources6811.P10.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 98 41 19 132 2531 4 6 nodes u0 u1 P
    exact MovingFiberSources6811.P11.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 142 59 27 193 2513 6 9 nodes u0 u1 P
    exact MovingFiberSources6811.P12.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 158 69 32 214 2505 7 8 nodes u0 u1 P
    exact MovingFiberSources6811.P13.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 146 58 27 198 2596 6 9 nodes u0 u1 P
    exact MovingFiberSources6811.P14.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 98 41 19 133 2422 4 6 nodes u0 u1 P
    exact MovingFiberSources6811.P15.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 150 60 28 204 2367 6 9 nodes u0 u1 P
    exact MovingFiberSources6811.P16.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 162 71 33 218 2419 7 8 nodes u0 u1 P
    exact MovingFiberSources6811.P17.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 47 22 155 2870 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P18.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 166 66 31 226 2765 7 10 nodes u0 u1 P
    exact MovingFiberSources6811.P19.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 174 76 36 237 2820 8 9 nodes u0 u1 P
    exact MovingFiberSources6811.P20.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 111 46 22 151 3307 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P21.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 189 83 39 256 3238 9 10 nodes u0 u1 P
    exact MovingFiberSources6811.P22.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 114 45 20 155 3266 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P23.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 190 84 40 258 3169 9 10 nodes u0 u1 P
    exact MovingFiberSources6811.P24.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 111 46 21 151 3286 5 7 nodes u0 u1 P
    exact MovingFiberSources6811.P25.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 189 83 39 257 3208 9 10 nodes u0 u1 P
    exact MovingFiberSources6811.P26.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 72 31 14 98 979 2 3 nodes u0 u1 P
    exact MovingFiberSources6811.P27.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 104 45 21 142 1697 4 5 nodes u0 u1 P
    exact MovingFiberSources6811.P28.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 104 45 21 141 1835 4 6 nodes u0 u1 P
    exact MovingFiberSources6811.P29.exists_interpolant nodes u0 u1 hI
  · change ∃ P, Interpolant 136 59 27 185 2423 6 7 nodes u0 u1 P
    exact MovingFiberSources6811.P30.exists_interpolant nodes u0 u1 hI

def groupIndices : Fin 20 → Fin 3 → Fin 31 := ![![0,0,0],![1,1,1],![2,2,2],![3,3,3],![4,5,6],![7,8,9],![10,10,10],![11,12,13],![11,14,13],![15,16,17],![18,19,20],![21,5,22],![23,5,24],![25,5,24],![25,5,26],![21,5,26],![27,27,27],![28,28,28],![29,29,29],![30,30,30]]

theorem groups_eq_sources (g : Fin 20) (j : Fin 3) : groups g j = sources (groupIndices g j) := by
  have h : ∀ g : Fin 20, ∀ j : Fin 3, groups g j = sources (groupIndices g j) := by decide +kernel
  exact h g j

theorem exists_group {K I : Type} [Field K] [Fintype I]
    (nodes : I ↪ K) (u0 u1 : I → K) (hI : Fintype.card I = 262144) (g : Fin 20) :
    ∃ P : Fin 3 → SecondJetSupport.Poly (K := K), ∀ j,
      Interpolant (groups g j).m (groups g j).B (groups g j).s (groups g j).U
        (groups g j).L (groups g j).k (groups g j).n0 nodes u0 u1 (P j) := by
  classical
  have hex (j : Fin 3) : ∃ P, Interpolant (groups g j).m (groups g j).B (groups g j).s
      (groups g j).U (groups g j).L (groups g j).k (groups g j).n0 nodes u0 u1 P := by
    rw [groups_eq_sources g j]
    exact exists_source nodes u0 u1 hI (groupIndices g j)
  exact Classical.skolem.mp hex

#print axioms exists_group
end ProximityPrize.SubmissionLower.MovingFiberCatalog6811
