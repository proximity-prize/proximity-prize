import ProximityPrize.SubmissionLower.R6961LoRescueSource6961
import ProximityPrize.SubmissionLower.R6961LoHelperSource
import ProximityPrize.SubmissionLower.TwoJetCaseBBridge

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.Lo.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (helperBank helperCutoff helper_common_caps)
open TwoJetCaseBBridge (SmallRect61)

def jetCap (rect : Fin 10) : ℕ := ([1,1,1,2,4,7,1,2,4,7] : List ℕ).get ⟨rect.val,rect.isLt⟩
def seedCap (rect : Fin 10) : ℕ := ([1,6,22,17,13,11,85,80,80,80] : List ℕ).get ⟨rect.val,rect.isLt⟩

def smallRectOf (rect : Fin 10) : SmallRect61 :=
  match rect.val with
  | 0 => .r0
  | 1 => .r1
  | 2 => .r2a
  | 3 => .r3a_j2
  | 4 => .r3a_j4
  | _ => .r3a_j7

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤85) (mixed : 2≤j → u≤80) :
    ∃ rect : Fin 10, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect ∧
      (rect.val < 6 → (smallRectOf rect).In j u) := by
  by_cases hj1 : j = 1
  · by_cases hu1 : u ≤ 1
    · refine ⟨0, by change 1≤j; omega, by change j≤1; omega, by change 1≤u; omega, by change u≤1; omega, ?_⟩
      intro _; simp [smallRectOf, SmallRect61.In]; omega
    · by_cases hu6 : u ≤ 6
      · refine ⟨1, by change 1≤j; omega, by change j≤1; omega, by change 2≤u; omega, by change u≤6; omega, ?_⟩
        intro _; simp [smallRectOf, SmallRect61.In]; omega
      · by_cases hu22 : u ≤ 22
        · refine ⟨2, by change 1≤j; omega, by change j≤1; omega, by change 7≤u; omega, by change u≤22; omega, ?_⟩
          intro _; simp [smallRectOf, SmallRect61.In]; omega
        · refine ⟨6, by change 1≤j; omega, by change j≤1; omega, by change 23≤u; omega, by change u≤85; omega, ?_⟩
          intro h; omega
  · have hu80 : u ≤ 80 := mixed (by omega)
    by_cases hj2 : j = 2
    · by_cases hu17 : u ≤ 17
      · refine ⟨3, by change 2≤j; omega, by change j≤2; omega, by change 1≤u; omega, by change u≤17; omega, ?_⟩
        intro _; simp [smallRectOf, SmallRect61.In]; omega
      · refine ⟨7, by change 2≤j; omega, by change j≤2; omega, by change 18≤u; omega, by change u≤80; omega, ?_⟩
        intro h; omega
    · by_cases hj4 : j ≤ 4
      · by_cases hu13 : u ≤ 13
        · refine ⟨4, by change 3≤j; omega, by change j≤4; omega, by change 1≤u; omega, by change u≤13; omega, ?_⟩
          intro _; simp [smallRectOf, SmallRect61.In]; omega
        · refine ⟨8, by change 3≤j; omega, by change j≤4; omega, by change 14≤u; omega, by change u≤80; omega, ?_⟩
          intro h; omega
      · by_cases hu11 : u ≤ 11
        · refine ⟨5, by change 5≤j; omega, by change j≤7; omega, by change 1≤u; omega, by change u≤11; omega, ?_⟩
          intro _; simp [smallRectOf, SmallRect61.In]; omega
        · refine ⟨9, by change 5≤j; omega, by change j≤7; omega, by change 12≤u; omega, by change u≤80; omega, ?_⟩
          intro h; omega

theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2346≤h) (hi : h≤2449) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣P) :
    ∃ rect : Fin 10, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      (rect.val < 6 → (smallRectOf rect).In (jetDegree G) (seedDegree G)) ∧
      ∀ (i : Fin 17), (6 ≤ rect.val ∨ i ≠ 0) →
        ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU,hsmall⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,hsmall,fun i hok => ?_⟩
  exact rescue_row Crt word lo hi rect i hok irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

end Lower6961.Lo.RescueSource
