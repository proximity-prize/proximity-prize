import ProximityPrize.SubmissionLower.PortLow8Price
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
namespace P0_9_8
open K1_13
open K1_13_8 (Valid zeroShape fullCap availableMass)
private theorem fat : c1 := by
  intro ⟨b,j,t⟩ h hb
  obtain ⟨h1,h2,h3⟩ := h
  obtain ⟨b20,j6,b17,b14,b7⟩ := hb
  change b ≤ 20 at b20
  change 1 ≤ t at h1
  change 3*t ≤ j at h2
  change j ≤ 6 at j6
  have tmax : t ≤ 2 := by omega
  have jmin : 3 ≤ j := by omega
  interval_cases t <;> interval_cases j <;> first | omega | skip
  all_goals dsimp at b17 b14 b7
  all_goals interval_cases b <;> first | omega | decide +kernel

private theorem empty_admissible : c2 := by
  intro s hs
  simp only [emptyThresholds,List.mem_cons,List.not_mem_nil,or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals unfold availableMass; simp only [sum_eq]; decide +kernel

private theorem oneMass4 : availableMass oneStart ⟨0,4,0⟩ (oneOrder ⟨0,4,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass5 : availableMass oneStart ⟨0,5,0⟩ (oneOrder ⟨0,5,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass6 : availableMass oneStart ⟨0,6,0⟩ (oneOrder ⟨0,6,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass7 : availableMass oneStart ⟨0,7,0⟩ (oneOrder ⟨0,7,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass8 : availableMass oneStart ⟨0,8,0⟩ (oneOrder ⟨0,8,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass9 : availableMass oneStart ⟨0,9,0⟩ (oneOrder ⟨0,9,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass10 : availableMass oneStart ⟨0,10,0⟩ (oneOrder ⟨0,10,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass11 : availableMass oneStart ⟨0,11,0⟩ (oneOrder ⟨0,11,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass12 : availableMass oneStart ⟨0,12,0⟩ (oneOrder ⟨0,12,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass13 : availableMass oneStart ⟨0,13,0⟩ (oneOrder ⟨0,13,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass14 : availableMass oneStart ⟨0,14,0⟩ (oneOrder ⟨0,14,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass15 : availableMass oneStart ⟨0,15,0⟩ (oneOrder ⟨0,15,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass16 : availableMass oneStart ⟨0,16,0⟩ (oneOrder ⟨0,16,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass17 : availableMass oneStart ⟨0,17,0⟩ (oneOrder ⟨0,17,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass18 : availableMass oneStart ⟨0,18,0⟩ (oneOrder ⟨0,18,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass19 : availableMass oneStart ⟨0,19,0⟩ (oneOrder ⟨0,19,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass20 : availableMass oneStart ⟨0,20,0⟩ (oneOrder ⟨0,20,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass21 : availableMass oneStart ⟨0,21,0⟩ (oneOrder ⟨0,21,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass22 : availableMass oneStart ⟨0,22,0⟩ (oneOrder ⟨0,22,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass23 : availableMass oneStart ⟨0,23,0⟩ (oneOrder ⟨0,23,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass24 : availableMass oneStart ⟨0,24,0⟩ (oneOrder ⟨0,24,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass25 : availableMass oneStart ⟨0,25,0⟩ (oneOrder ⟨0,25,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass26 : availableMass oneStart ⟨0,26,0⟩ (oneOrder ⟨0,26,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass27 : availableMass oneStart ⟨0,27,0⟩ (oneOrder ⟨0,27,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass28 : availableMass oneStart ⟨0,28,0⟩ (oneOrder ⟨0,28,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass29 : availableMass oneStart ⟨0,29,0⟩ (oneOrder ⟨0,29,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass30 : availableMass oneStart ⟨0,30,0⟩ (oneOrder ⟨0,30,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass31 : availableMass oneStart ⟨0,31,0⟩ (oneOrder ⟨0,31,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass32 : availableMass oneStart ⟨0,32,0⟩ (oneOrder ⟨0,32,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass33 : availableMass oneStart ⟨0,33,0⟩ (oneOrder ⟨0,33,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass34 : availableMass oneStart ⟨0,34,0⟩ (oneOrder ⟨0,34,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass35 : availableMass oneStart ⟨0,35,0⟩ (oneOrder ⟨0,35,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass36 : availableMass oneStart ⟨0,36,0⟩ (oneOrder ⟨0,36,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass37 : availableMass oneStart ⟨0,37,0⟩ (oneOrder ⟨0,37,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass38 : availableMass oneStart ⟨0,38,0⟩ (oneOrder ⟨0,38,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass39 : availableMass oneStart ⟨0,39,0⟩ (oneOrder ⟨0,39,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass40 : availableMass oneStart ⟨0,40,0⟩ (oneOrder ⟨0,40,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass41 : availableMass oneStart ⟨0,41,0⟩ (oneOrder ⟨0,41,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass42 : availableMass oneStart ⟨0,42,0⟩ (oneOrder ⟨0,42,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass43 : availableMass oneStart ⟨0,43,0⟩ (oneOrder ⟨0,43,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass44 : availableMass oneStart ⟨0,44,0⟩ (oneOrder ⟨0,44,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem oneMass45 : availableMass oneStart ⟨0,45,0⟩ (oneOrder ⟨0,45,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem one_admissible : c4 := by
  intro j hl hu
  interval_cases j
  · exact oneMass4
  · exact oneMass5
  · exact oneMass6
  · exact oneMass7
  · exact oneMass8
  · exact oneMass9
  · exact oneMass10
  · exact oneMass11
  · exact oneMass12
  · exact oneMass13
  · exact oneMass14
  · exact oneMass15
  · exact oneMass16
  · exact oneMass17
  · exact oneMass18
  · exact oneMass19
  · exact oneMass20
  · exact oneMass21
  · exact oneMass22
  · exact oneMass23
  · exact oneMass24
  · exact oneMass25
  · exact oneMass26
  · exact oneMass27
  · exact oneMass28
  · exact oneMass29
  · exact oneMass30
  · exact oneMass31
  · exact oneMass32
  · exact oneMass33
  · exact oneMass34
  · exact oneMass35
  · exact oneMass36
  · exact oneMass37
  · exact oneMass38
  · exact oneMass39
  · exact oneMass40
  · exact oneMass41
  · exact oneMass42
  · exact oneMass43
  · exact oneMass44
  · exact oneMass45
private def onePeak (j : ℕ) : Shape := ⟨119,j,min 9 (j/3)⟩
private theorem one_row (j : ℕ) (hl : 3 ≤ j) (hu : j ≤ 45) :
    P0_9.physicalPrice (onePeak j) (oneOrder (onePeak j)) ≤ indexBudget oneStart (factorCap - oneReserve) j := by
  interval_cases j <;> decide +kernel

private theorem one_paid : c5 := by
  intro a ha hb
  have hb0 : 1 + a.b ≤ 120 := hb.1
  have hb1 : 3 + a.j ≤ 48 := hb.2.1
  have hb2 : 1 + a.t ≤ 10 := hb.2.2
  have ht := ha.2.1
  have hp := ha.1
  have hm : InBox a (onePeak a.j) := ⟨by change a.b ≤ 119; omega, le_rfl, by change a.t ≤ min 9 (a.j/3); omega⟩
  have hfit : 3 * (onePeak a.j).t ≤ (onePeak a.j).j := by
    change 3 * min 9 (a.j/3) ≤ a.j
    have := min_le_right 9 (a.j/3)
    omega
  exact (P0_9_8_3.physical_mono hm ht hfit _).trans (one_row _ (by omega) (by omega))
private theorem twoMass3 : availableMass twoStart ⟨0,3,0⟩ (twoOrder ⟨0,3,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass4 : availableMass twoStart ⟨0,4,0⟩ (twoOrder ⟨0,4,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass5 : availableMass twoStart ⟨0,5,0⟩ (twoOrder ⟨0,5,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass6 : availableMass twoStart ⟨0,6,0⟩ (twoOrder ⟨0,6,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass7 : availableMass twoStart ⟨0,7,0⟩ (twoOrder ⟨0,7,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass8 : availableMass twoStart ⟨0,8,0⟩ (twoOrder ⟨0,8,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass9 : availableMass twoStart ⟨0,9,0⟩ (twoOrder ⟨0,9,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass10 : availableMass twoStart ⟨0,10,0⟩ (twoOrder ⟨0,10,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass11 : availableMass twoStart ⟨0,11,0⟩ (twoOrder ⟨0,11,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass12 : availableMass twoStart ⟨0,12,0⟩ (twoOrder ⟨0,12,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass13 : availableMass twoStart ⟨0,13,0⟩ (twoOrder ⟨0,13,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass14 : availableMass twoStart ⟨0,14,0⟩ (twoOrder ⟨0,14,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass15 : availableMass twoStart ⟨0,15,0⟩ (twoOrder ⟨0,15,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass16 : availableMass twoStart ⟨0,16,0⟩ (twoOrder ⟨0,16,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass17 : availableMass twoStart ⟨0,17,0⟩ (twoOrder ⟨0,17,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass18 : availableMass twoStart ⟨0,18,0⟩ (twoOrder ⟨0,18,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass19 : availableMass twoStart ⟨0,19,0⟩ (twoOrder ⟨0,19,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass20 : availableMass twoStart ⟨0,20,0⟩ (twoOrder ⟨0,20,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass21 : availableMass twoStart ⟨0,21,0⟩ (twoOrder ⟨0,21,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass22 : availableMass twoStart ⟨0,22,0⟩ (twoOrder ⟨0,22,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass23 : availableMass twoStart ⟨0,23,0⟩ (twoOrder ⟨0,23,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass24 : availableMass twoStart ⟨0,24,0⟩ (twoOrder ⟨0,24,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass25 : availableMass twoStart ⟨0,25,0⟩ (twoOrder ⟨0,25,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass26 : availableMass twoStart ⟨0,26,0⟩ (twoOrder ⟨0,26,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass27 : availableMass twoStart ⟨0,27,0⟩ (twoOrder ⟨0,27,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass28 : availableMass twoStart ⟨0,28,0⟩ (twoOrder ⟨0,28,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass29 : availableMass twoStart ⟨0,29,0⟩ (twoOrder ⟨0,29,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass30 : availableMass twoStart ⟨0,30,0⟩ (twoOrder ⟨0,30,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass31 : availableMass twoStart ⟨0,31,0⟩ (twoOrder ⟨0,31,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass32 : availableMass twoStart ⟨0,32,0⟩ (twoOrder ⟨0,32,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass33 : availableMass twoStart ⟨0,33,0⟩ (twoOrder ⟨0,33,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass34 : availableMass twoStart ⟨0,34,0⟩ (twoOrder ⟨0,34,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass35 : availableMass twoStart ⟨0,35,0⟩ (twoOrder ⟨0,35,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass36 : availableMass twoStart ⟨0,36,0⟩ (twoOrder ⟨0,36,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass37 : availableMass twoStart ⟨0,37,0⟩ (twoOrder ⟨0,37,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass38 : availableMass twoStart ⟨0,38,0⟩ (twoOrder ⟨0,38,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass39 : availableMass twoStart ⟨0,39,0⟩ (twoOrder ⟨0,39,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass40 : availableMass twoStart ⟨0,40,0⟩ (twoOrder ⟨0,40,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass41 : availableMass twoStart ⟨0,41,0⟩ (twoOrder ⟨0,41,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem twoMass42 : availableMass twoStart ⟨0,42,0⟩ (twoOrder ⟨0,42,0⟩ - 1) < P0_9.layerNeed := by
  unfold availableMass; simp only [sum_eq]; decide +kernel
private theorem two_admissible : c6 := by
  intro j hl hu
  interval_cases j
  · exact twoMass3
  · exact twoMass4
  · exact twoMass5
  · exact twoMass6
  · exact twoMass7
  · exact twoMass8
  · exact twoMass9
  · exact twoMass10
  · exact twoMass11
  · exact twoMass12
  · exact twoMass13
  · exact twoMass14
  · exact twoMass15
  · exact twoMass16
  · exact twoMass17
  · exact twoMass18
  · exact twoMass19
  · exact twoMass20
  · exact twoMass21
  · exact twoMass22
  · exact twoMass23
  · exact twoMass24
  · exact twoMass25
  · exact twoMass26
  · exact twoMass27
  · exact twoMass28
  · exact twoMass29
  · exact twoMass30
  · exact twoMass31
  · exact twoMass32
  · exact twoMass33
  · exact twoMass34
  · exact twoMass35
  · exact twoMass36
  · exact twoMass37
  · exact twoMass38
  · exact twoMass39
  · exact twoMass40
  · exact twoMass41
  · exact twoMass42
private def twoPeak (j : ℕ) : Shape := ⟨118,j,min 8 (j/3)⟩
private theorem two_row (j : ℕ) (hl : 3 ≤ j) (hu : j ≤ 42) :
    P0_9.physicalPrice (twoPeak j) (twoOrder (twoPeak j)) ≤ indexBudget twoStart (factorCap - twoReserve) j := by
  interval_cases j <;> decide +kernel

private theorem two_paid : c7 := by
  intro a ha hb
  have hb0 : 2 + a.b ≤ 120 := hb.1
  have hb1 : 6 + a.j ≤ 48 := hb.2.1
  have hb2 : 2 + a.t ≤ 10 := hb.2.2
  have ht := ha.2.1
  have hp := ha.1
  have hm : InBox a (twoPeak a.j) := ⟨by change a.b ≤ 118; omega, le_rfl, by change a.t ≤ min 8 (a.j/3); omega⟩
  have hfit : 3 * (twoPeak a.j).t ≤ (twoPeak a.j).j := by
    change 3 * min 8 (a.j/3) ≤ a.j
    have := min_le_right 8 (a.j/3)
    omega
  exact (P0_9_8_3.physical_mono hm ht hfit _).trans (two_row _ (by omega) (by omega))
theorem complete : P0_9.c8 :=
  of_children fat empty_admissible P0_9_8_3.proof one_admissible one_paid two_admissible two_paid
end P0_9_8
