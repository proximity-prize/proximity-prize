import ProximityPrize.SubmissionLower.PortLowBase

set_option Elab.async false
set_option maxHeartbeats 2000000

namespace SmallAnchor6960Space
open K1_13 (Geom)
open PolynomialDifferential ReedSolomon.HiddenDerivative

private def gradeLimits:List ℕ:=[137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,137,135,135,133,133,133,131,131,129,129,127,127,125,125,123,123,121,121,119,119,117,117,115]
private def caps:List ℕ:=[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,56,55,55,53,53,51,51,49,49,47,47,45,45,43,43,41,41,39,39,36,36,34,34]

def gradeLimit (t:ℕ):ℕ:=gradeLimits[min t 56]?.getD 0

def cap (s:ℕ):ℕ:=if s < 138 then caps[s]?.getD 0 else 0

theorem cap_le_grade (s : ℕ) : cap s ≤ s := by
  by_cases hs:s < 138
  · have h : ∀ n : Fin 138, cap n.val ≤ n.val := by decide +kernel
    exact h ⟨s,hs⟩
  · simp [cap,hs]

theorem cap_le_index (s : ℕ) : cap s ≤ 56 := by
  by_cases hs:s < 138
  · have h : ∀ n : Fin 138, cap n.val ≤ 56 := by decide +kernel
    exact h ⟨s,hs⟩
  · simp [cap,hs]

private theorem gradeLimit_tail {t : ℕ} (ht : 56 < t) : gradeLimit t = 115 := by
  rw [gradeLimit,Nat.min_eq_right (by omega:56≤t)] <;> decide

theorem gradeLimit_antitone : Antitone gradeLimit := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hn:n < 57
  · have checks : ∀ t : Fin 57, gradeLimit (t.val + 1) ≤ gradeLimit t := by decide +kernel
    exact checks ⟨n,hn⟩
  · rw [gradeLimit_tail (by omega),gradeLimit_tail (by omega)]

theorem cap_of_grade {s t : ℕ} (ht : t ≤ 56) (hts : t ≤ s) (h : s ≤ gradeLimit t) : t ≤ cap s := by
  have hb:(List.range 57).all (fun i => decide (gradeLimit i≤137))=true:=by decide +kernel
  have hh:=of_decide_eq_true (List.all_eq_true.mp hb t (List.mem_range.mpr (by omega)))
  have checks : (List.range 138).all (fun s => (List.range 57).all
      (fun t => decide (t≤s→s≤gradeLimit t→t≤cap s)))=true:=by decide +kernel
  exact (of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checks s
    (List.mem_range.mpr (by omega))) t (List.mem_range.mpr (by omega)))) hts h

theorem cap_active (s : ℕ) (hs : s ≤ 137) : s + cap s ≤ 172 := by
  have checks:(List.range 138).all (fun g => decide (g+cap g≤172))=true:=by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checks s (List.mem_range.mpr (by omega)))

def AnchorEligible (u : JetVariable 3 →₀ ℕ) : Prop :=
  u.some.degree ≤ 137 ∧ u.some.weight (fun i => i.val) ≤ 56 ∧ u (some 3) ≤ 14 ∧
    u.some.degree≤gradeLimit (u (some 1)+u (some 2)+u (some 3)) ∧
    u.weight (differentialWeight 133499)≤102*179876 - 1+56

noncomputable def anchorSpace : Submodule Geom (DifferentialPolynomial Geom 3) :=
  MvPolynomial.restrictSupport Geom {u | AnchorEligible u}

noncomputable def anchorLocal (x y : Geom) : anchorSpace →ₗ[Geom] LocalPolynomial Geom 3 :=
  (localConstraintAt 102 x y).domRestrict _

end SmallAnchor6960Space
