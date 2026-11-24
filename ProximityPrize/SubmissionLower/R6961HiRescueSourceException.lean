import ProximityPrize.SubmissionLower.R6961HiRescueSource6961
import ProximityPrize.SubmissionLower.R6961HiHelperSource

set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.Hi.RescueSource
open K1_14 (Jet L)
open K1_14_1 (PoleData CRTLift evaluated)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree)
open HelperSource (helperBank helperCutoff helper_common_caps)

def jetCap (rect : Fin 4) : ℕ := ([1,1,1,7] : List ℕ).get ⟨rect.val,rect.isLt⟩

def seedCap (rect : Fin 4) : ℕ := ([1,6,85,78] : List ℕ).get ⟨rect.val,rect.isLt⟩

private theorem fits_rectangle {j u : ℕ} (loJ : 1≤j) (hiJ : j≤7)
    (loU : 1≤u) (hiU : u≤85) (mixed : 2≤j → u≤78) :
    ∃ rect : Fin 4, 1+excess rect≤j ∧ j≤jetCap rect ∧ seed rect≤u ∧ u≤seedCap rect := by
  by_cases hJ : 2≤j
  · refine ⟨3,?_⟩
    change 2≤j ∧ j≤7 ∧ 1≤u ∧ u≤78
    exact ⟨hJ,hiJ,loU,mixed hJ⟩
  · by_cases hU : u≤1
    · refine ⟨0,?_⟩
      change 1≤j ∧ j≤1 ∧ 1≤u ∧ u≤1
      omega
    · by_cases hU' : u≤6
      · refine ⟨1,?_⟩
        change 1≤j ∧ j≤1 ∧ 2≤u ∧ u≤6
        omega
      · refine ⟨2,?_⟩
        change 1≤j ∧ j≤1 ∧ 7≤u ∧ u≤85
        omega

/-- A common moving prime in the powered helper determines one rescue schedule
for all 17 stages. Its actual degrees fit that rectangle's geometry caps. -/
theorem exceptional_rows {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2450≤h) (hi : h≤33579) {G : Jet} (irr : Irreducible G) (seeded : UsesSeed G)
    (slope : 0<G.natDegree)
    (common : ∀ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣P) :
    ∃ rect : Fin 4, G.natDegree=1 ∧ jetDegree G≤jetCap rect ∧ seedDegree G≤seedCap rect ∧
      ∀ i : Fin 17, ∃ Q ∈ evaluated Crt word (bank rect i).shape (cutoff h rect i), ¬ G∣Q := by
  obtain ⟨linear,loJ,hiJ,loU,hiU,mixed⟩ := helper_common_caps Crt word lo hi irr seeded slope common
  obtain ⟨rect,lowJ,highJ,lowU,highU⟩ := fits_rectangle loJ hiJ loU hiU mixed
  refine ⟨rect,linear,highJ,highU,fun i => ?_⟩
  exact rescue_row Crt word lo hi rect i irr seeded (by omega) lowU (by rw [linear]; exact lowJ)

#print axioms exceptional_rows

end Lower6961.Hi.RescueSource
