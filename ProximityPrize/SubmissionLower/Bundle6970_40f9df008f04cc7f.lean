import ProximityPrize.SubmissionLower.Z6970CompanionAnchors
import ProximityPrize.SubmissionLower.Z6970CompanionBook
import ProximityPrize.SubmissionLower.Bundle6970_7998bebe72a7a065

section Pack_Z6970CompanionGroup00

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group0 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule0 cost := by
  intro x hx hcap
  change x.b ≤ 123 ∧ x.j ≤ 5 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 13908324562457638
  by_cases h_b62 : x.b ≤ 62
  · by_cases h_b31 : x.b ≤ 31
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨31,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee31_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b16 : x.b ≤ 16
        · have hp := corner x ⟨16,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee16_5_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b24 : x.b ≤ 24
          · by_cases h_b20 : x.b ≤ 20
            · have hp := corner x ⟨20,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee20_5_1_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b22 : x.b ≤ 22
              · have hp := corner x ⟨22,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤22 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee22_5_1_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b23 : x.b ≤ 23
                · have hp := corner x ⟨23,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤23 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee23_5_1_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨24,5,1⟩ 2 24 5 hx (by exact ⟨(show x.b≤24 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor22 ord ho))
                  rw [fee24_5_1_2] at hp
                  exact hp.trans (by decide)
          · have hp := corner x ⟨31,5,1⟩ 2 25 5 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 3) (anchor5 ord ho))
            rw [fee31_5_1_2] at hp
            exact hp.trans (by decide)
    · have hp := corner x ⟨62,5,1⟩ 3 30 3 hx (by exact ⟨(show x.b≤62 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 4) (anchor6 ord ho))
      rw [fee62_5_1_3] at hp
      exact hp.trans (by decide)
  · have hp := corner x ⟨123,5,1⟩ 6 48 3 hx (by exact ⟨(show x.b≤123 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 6 ≤ 20) (anchor11 ord ho))
    rw [fee123_5_1_6] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup00

section Pack_Z6970CompanionGroup01

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group1 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule1 cost := by
  intro x hx hcap
  change x.b ≤ 54 ∧ x.j ≤ 15 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 22940588105726584
  by_cases h_j9 : x.j ≤ 9
  · by_cases h_j6 : x.j ≤ 6
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨54,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤54 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee54_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b28 : x.b ≤ 28
        · by_cases h_b15 : x.b ≤ 15
          · have hp := corner x ⟨15,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee15_6_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_j5 : x.j ≤ 5
            · have hp := corner x ⟨28,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤28 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee28_5_1_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b22 : x.b ≤ 22
              · have hp := corner x ⟨22,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤22 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee22_6_1_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨28,6,1⟩ 2 21 6 hx (by exact ⟨(show x.b≤28 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                rw [fee28_6_1_2] at hp
                exact hp.trans (by decide)
        · have hp := corner x ⟨54,6,1⟩ 3 25 5 hx (by exact ⟨(show x.b≤54 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor5 ord ho))
          rw [fee54_6_1_3] at hp
          exact hp.trans (by decide)
    · by_cases h_b28 : x.b ≤ 28
      · by_cases h_b15 : x.b ≤ 15
        · by_cases h_j8 : x.j ≤ 8
          · by_cases h_b9 : x.b ≤ 9
            · have hp := corner x ⟨9,8,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee9_8_1_1] at hp
              exact hp.trans (by decide)
            · by_cases h_j7 : x.j ≤ 7
              · have hp := corner x ⟨15,7,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee15_7_1_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨15,8,1⟩ 2 10 8 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                rw [fee15_8_1_2] at hp
                exact hp.trans (by decide)
          · have hp := corner x ⟨15,9,1⟩ 2 2 9 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤9 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 3) (anchor7 ord ho))
            rw [fee15_9_1_2] at hp
            exact hp.trans (by decide)
        · by_cases h_j8 : x.j ≤ 8
          · by_cases h_j7 : x.j ≤ 7
            · have hp := corner x ⟨28,7,1⟩ 2 16 7 hx (by exact ⟨(show x.b≤28 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
              rw [fee28_7_1_2] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨28,8,1⟩ 3 14 8 hx (by exact ⟨(show x.b≤28 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor0 ord ho))
              rw [fee28_8_1_3] at hp
              exact hp.trans (by decide)
          · have hp := corner x ⟨28,9,1⟩ 4 14 8 hx (by exact ⟨(show x.b≤28 by omega),(show x.j≤9 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 5) (anchor0 ord ho))
            rw [fee28_9_1_4] at hp
            exact hp.trans (by decide)
      · have hp := corner x ⟨54,9,1⟩ 7 29 6 hx (by exact ⟨(show x.b≤54 by omega),(show x.j≤9 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 10) (anchor3 ord ho))
        rw [fee54_9_1_7] at hp
        exact hp.trans (by decide)
  · by_cases h_b29 : x.b ≤ 29
    · by_cases h_b17 : x.b ≤ 17
      · have hp := corner x ⟨17,15,1⟩ 6 1 10 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤15 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 6 ≤ 7) (anchor4 ord ho))
        rw [fee17_15_1_6] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨29,15,1⟩ 11 17 9 hx (by exact ⟨(show x.b≤29 by omega),(show x.j≤15 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 11 ≤ 11) (anchor2 ord ho))
        rw [fee29_15_1_11] at hp
        exact hp.trans (by decide)
    · by_cases h_b42 : x.b ≤ 42
      · have hp := corner x ⟨42,15,1⟩ 16 21 10 hx (by exact ⟨(show x.b≤42 by omega),(show x.j≤15 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 16 ≤ 16) (anchor10 ord ho))
        rw [fee42_15_1_16] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨54,15,1⟩ 21 33 10 hx (by exact ⟨(show x.b≤54 by omega),(show x.j≤15 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 21 ≤ 21) (anchor23 ord ho))
        rw [fee54_15_1_21] at hp
        exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup01

section Pack_Z6970CompanionGroup02

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group2 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule2 cost := by
  intro x hx hcap
  change x.b ≤ 124 ∧ x.j ≤ 10 ∧ x.t ≤ 3 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 25261884590037539
  by_cases h_b62 : x.b ≤ 62
  · by_cases h_b31 : x.b ≤ 31
    · by_cases h_t2 : x.t ≤ 2
      · by_cases h_j6 : x.j ≤ 6
        · by_cases h_j4 : x.j ≤ 4
          · have hp := corner x ⟨31,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee31_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b16 : x.b ≤ 16
            · have hp := corner x ⟨16,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee16_6_2_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b24 : x.b ≤ 24
              · by_cases h_j5 : x.j ≤ 5
                · have hp := corner x ⟨24,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤24 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee24_5_1_1] at hp
                  exact hp.trans (by decide)
                · by_cases h_b20 : x.b ≤ 20
                  · have hp := corner x ⟨20,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                    rw [fee20_6_2_1] at hp
                    exact hp.trans (by decide)
                  · have hp := corner x ⟨24,6,2⟩ 2 21 6 hx (by exact ⟨(show x.b≤24 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                    rw [fee24_6_2_2] at hp
                    exact hp.trans (by decide)
              · have hp := corner x ⟨31,6,2⟩ 2 25 5 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 3) (anchor5 ord ho))
                rw [fee31_6_2_2] at hp
                exact hp.trans (by decide)
        · by_cases h_b17 : x.b ≤ 17
          · by_cases h_j8 : x.j ≤ 8
            · by_cases h_b10 : x.b ≤ 10
              · have hp := corner x ⟨10,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee10_8_2_1] at hp
                exact hp.trans (by decide)
              · by_cases h_j7 : x.j ≤ 7
                · by_cases h_b14 : x.b ≤ 14
                  · have hp := corner x ⟨14,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                    rw [fee14_7_2_1] at hp
                    exact hp.trans (by decide)
                  · by_cases h_b16 : x.b ≤ 16
                    · by_cases h_b15 : x.b ≤ 15
                      · have hp := corner x ⟨15,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                        rw [fee15_7_2_1] at hp
                        exact hp.trans (by decide)
                      · have hp := corner x ⟨16,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                        rw [fee16_7_2_2] at hp
                        exact hp.trans (by decide)
                    · have hp := corner x ⟨17,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                      rw [fee17_7_2_2] at hp
                      exact hp.trans (by decide)
                · have hp := corner x ⟨17,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                  rw [fee17_8_2_2] at hp
                  exact hp.trans (by decide)
            · have hp := corner x ⟨17,10,2⟩ 3 2 9 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor7 ord ho))
              rw [fee17_10_2_3] at hp
              exact hp.trans (by decide)
          · by_cases h_j8 : x.j ≤ 8
            · have hp := corner x ⟨31,8,2⟩ 3 18 7 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor19 ord ho))
              rw [fee31_8_2_3] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨31,10,2⟩ 5 14 8 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 5 ≤ 5) (anchor0 ord ho))
              rw [fee31_10_2_5] at hp
              exact hp.trans (by decide)
      · by_cases h_b17 : x.b ≤ 17
        · have hp := corner x ⟨17,10,3⟩ 3 2 9 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤10 by omega),(show x.t≤3 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor7 ord ho))
          rw [fee17_10_3_3] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨31,10,3⟩ 5 14 8 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤10 by omega),(show x.t≤3 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 5 ≤ 5) (anchor0 ord ho))
          rw [fee31_10_3_5] at hp
          exact hp.trans (by decide)
    · by_cases h_j6 : x.j ≤ 6
      · have hp := corner x ⟨62,6,2⟩ 3 30 3 hx (by exact ⟨(show x.b≤62 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 4) (anchor6 ord ho))
        rw [fee62_6_2_3] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨62,10,3⟩ 10 29 6 hx (by exact ⟨(show x.b≤62 by omega),(show x.j≤10 by omega),(show x.t≤3 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 10 ≤ 10) (anchor3 ord ho))
        rw [fee62_10_3_10] at hp
        exact hp.trans (by decide)
  · have hp := corner x ⟨124,10,3⟩ 20 48 3 hx (by exact ⟨(show x.b≤124 by omega),(show x.j≤10 by omega),(show x.t≤3 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 20 ≤ 20) (anchor11 ord ho))
    rw [fee124_10_3_20] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup02

section Pack_Z6970CompanionGroup03

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group3 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule3 cost := by
  intro x hx hcap
  change x.b ≤ 52 ∧ x.j ≤ 4 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 7277877017449032
  by_cases h_j3 : x.j ≤ 3
  · have hp := corner x ⟨52,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤52 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
    rw [fee52_3_1_1] at hp
    exact hp.trans (by decide)
  · by_cases h_b27 : x.b ≤ 27
    · by_cases h_b14 : x.b ≤ 14
      · have hp := corner x ⟨14,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee14_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b21 : x.b ≤ 21
        · have hp := corner x ⟨21,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤21 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee21_4_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b24 : x.b ≤ 24
          · have hp := corner x ⟨24,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤24 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee24_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b26 : x.b ≤ 26
            · have hp := corner x ⟨26,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤26 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee26_4_1_1] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨27,4,1⟩ 2 27 4 hx (by exact ⟨(show x.b≤27 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 3) (anchor13 ord ho))
              rw [fee27_4_1_2] at hp
              exact hp.trans (by decide)
    · have hp := corner x ⟨52,4,1⟩ 3 27 4 hx (by exact ⟨(show x.b≤52 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor13 ord ho))
      rw [fee52_4_1_3] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup03

section Pack_Z6970CompanionGroup04

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group4 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule4 cost := by
  intro x hx hcap
  change x.b ≤ 7 ∧ x.j ≤ 10 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 16028451824349056
  by_cases h_j6 : x.j ≤ 6
  · have hp := corner x ⟨7,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
    rw [fee7_6_1_1] at hp
    exact hp.trans (by decide)
  · by_cases h_j8 : x.j ≤ 8
    · have hp := corner x ⟨7,8,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
      rw [fee7_8_1_1] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨7,10,1⟩ 3 2 9 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor7 ord ho))
      rw [fee7_10_1_3] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup04

section Pack_Z6970CompanionGroup05

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group5 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule5 cost := by
  intro x hx hcap
  change x.b ≤ 49 ∧ x.j ≤ 16 ∧ x.t ≤ 2 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 25261884590037539
  by_cases h_j9 : x.j ≤ 9
  · by_cases h_j6 : x.j ≤ 6
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨49,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤49 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee49_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b25 : x.b ≤ 25
        · by_cases h_b13 : x.b ≤ 13
          · have hp := corner x ⟨13,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤13 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee13_6_2_1] at hp
            exact hp.trans (by decide)
          · by_cases h_j5 : x.j ≤ 5
            · have hp := corner x ⟨25,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤25 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee25_5_1_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b19 : x.b ≤ 19
              · have hp := corner x ⟨19,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee19_6_2_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b22 : x.b ≤ 22
                · have hp := corner x ⟨22,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤22 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee22_6_2_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨25,6,2⟩ 2 21 6 hx (by exact ⟨(show x.b≤25 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                  rw [fee25_6_2_2] at hp
                  exact hp.trans (by decide)
        · have hp := corner x ⟨49,6,2⟩ 3 25 5 hx (by exact ⟨(show x.b≤49 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor5 ord ho))
          rw [fee49_6_2_3] at hp
          exact hp.trans (by decide)
    · by_cases h_b26 : x.b ≤ 26
      · by_cases h_j8 : x.j ≤ 8
        · by_cases h_b14 : x.b ≤ 14
          · by_cases h_b8 : x.b ≤ 8
            · have hp := corner x ⟨8,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee8_8_2_1] at hp
              exact hp.trans (by decide)
            · by_cases h_j7 : x.j ≤ 7
              · have hp := corner x ⟨14,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee14_7_2_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b11 : x.b ≤ 11
                · by_cases h_b10 : x.b ≤ 10
                  · have hp := corner x ⟨10,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                    rw [fee10_8_2_1] at hp
                    exact hp.trans (by decide)
                  · have hp := corner x ⟨11,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤11 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                    rw [fee11_8_2_2] at hp
                    exact hp.trans (by decide)
                · have hp := corner x ⟨14,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                  rw [fee14_8_2_2] at hp
                  exact hp.trans (by decide)
          · by_cases h_j7 : x.j ≤ 7
            · by_cases h_b20 : x.b ≤ 20
              · by_cases h_b17 : x.b ≤ 17
                · by_cases h_b16 : x.b ≤ 16
                  · by_cases h_b15 : x.b ≤ 15
                    · have hp := corner x ⟨15,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                      rw [fee15_7_2_1] at hp
                      exact hp.trans (by decide)
                    · have hp := corner x ⟨16,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                      rw [fee16_7_2_2] at hp
                      exact hp.trans (by decide)
                  · have hp := corner x ⟨17,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                    rw [fee17_7_2_2] at hp
                    exact hp.trans (by decide)
                · have hp := corner x ⟨20,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                  rw [fee20_7_2_2] at hp
                  exact hp.trans (by decide)
              · have hp := corner x ⟨26,7,2⟩ 2 21 6 hx (by exact ⟨(show x.b≤26 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                rw [fee26_7_2_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨26,8,2⟩ 3 14 8 hx (by exact ⟨(show x.b≤26 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor0 ord ho))
              rw [fee26_8_2_3] at hp
              exact hp.trans (by decide)
        · have hp := corner x ⟨26,9,2⟩ 4 4 9 hx (by exact ⟨(show x.b≤26 by omega),(show x.j≤9 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor16 ord ho))
          rw [fee26_9_2_4] at hp
          exact hp.trans (by decide)
      · have hp := corner x ⟨49,9,2⟩ 7 22 7 hx (by exact ⟨(show x.b≤49 by omega),(show x.j≤9 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor21 ord ho))
        rw [fee49_9_2_7] at hp
        exact hp.trans (by decide)
  · by_cases h_b26 : x.b ≤ 26
    · by_cases h_b15 : x.b ≤ 15
      · have hp := corner x ⟨15,16,2⟩ 7 1 10 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤16 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor4 ord ho))
        rw [fee15_16_2_7] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨26,16,2⟩ 11 10 10 hx (by exact ⟨(show x.b≤26 by omega),(show x.j≤16 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 11 ≤ 11) (anchor18 ord ho))
        rw [fee26_16_2_11] at hp
        exact hp.trans (by decide)
    · by_cases h_j13 : x.j ≤ 13
      · have hp := corner x ⟨49,13,2⟩ 14 21 10 hx (by exact ⟨(show x.b≤49 by omega),(show x.j≤13 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 14 ≤ 16) (anchor10 ord ho))
        rw [fee49_13_2_14] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨49,16,2⟩ 21 7 14 hx (by exact ⟨(show x.b≤49 by omega),(show x.j≤16 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 21 ≤ 21) (anchor12 ord ho))
        rw [fee49_16_2_21] at hp
        exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup05

section Pack_Z6970CompanionGroup06

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group6 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule6 cost := by
  intro x hx hcap
  change x.b ≤ 7 ∧ x.j ≤ 18 ∧ x.t ≤ 4 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 6572347837558208*x.b
  by_cases h_j10 : x.j ≤ 10
  · by_cases h_j6 : x.j ≤ 6
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨7,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee7_4_1_1] at hp
        have lb : 1≤x.b := by omega
        exact hp.trans ((by decide : 1860286169749847 ≤ 6572347837558208*1).trans (Nat.mul_le_mul_left 6572347837558208 lb))
      · have hp := corner x ⟨7,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee7_6_2_1] at hp
        have lb : 2≤x.b := by omega
        exact hp.trans ((by decide : 7578096547665412 ≤ 6572347837558208*2).trans (Nat.mul_le_mul_left 6572347837558208 lb))
    · by_cases h_j8 : x.j ≤ 8
      · by_cases h_b5 : x.b ≤ 5
        · by_cases h_b4 : x.b ≤ 4
          · by_cases h_b3 : x.b ≤ 3
            · have hp := corner x ⟨3,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤3 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee3_8_2_1] at hp
              have lb : 3≤x.b := by omega
              exact hp.trans ((by decide : 19717043512674622 ≤ 6572347837558208*3).trans (Nat.mul_le_mul_left 6572347837558208 lb))
            · have hp := corner x ⟨4,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee4_8_2_1] at hp
              have lb : 4≤x.b := by omega
              exact hp.trans ((by decide : 19717072974392791 ≤ 6572347837558208*4).trans (Nat.mul_le_mul_left 6572347837558208 lb))
          · have hp := corner x ⟨5,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee5_8_2_1] at hp
            have lb : 5≤x.b := by omega
            exact hp.trans ((by decide : 19717102436110961 ≤ 6572347837558208*5).trans (Nat.mul_le_mul_left 6572347837558208 lb))
        · have hp := corner x ⟨7,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee7_8_2_1] at hp
          have lb : 6≤x.b := by omega
          exact hp.trans ((by decide : 19717161359547300 ≤ 6572347837558208*6).trans (Nat.mul_le_mul_left 6572347837558208 lb))
      · have hp := corner x ⟨7,10,3⟩ 3 2 9 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤10 by omega),(show x.t≤3 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor7 ord ho))
        rw [fee7_10_3_3] at hp
        have lb : 3≤x.b := by omega
        exact hp.trans ((by decide : 14885952097104539 ≤ 6572347837558208*3).trans (Nat.mul_le_mul_left 6572347837558208 lb))
  · have hp := corner x ⟨7,18,4⟩ 11 1 11 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤18 by omega),(show x.t≤4 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 11 ≤ 11) (anchor15 ord ho))
    rw [fee7_18_4_11] at hp
    have lb : 4≤x.b := by omega
    exact hp.trans ((by decide : 25597114738948922 ≤ 6572347837558208*4).trans (Nat.mul_le_mul_left 6572347837558208 lb))

end Height2307Companion
end Pack_Z6970CompanionGroup06

section Pack_Z6970CompanionGroup07

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group7 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule7 cost := by
  intro x hx hcap
  change x.b ≤ 58 ∧ x.j ≤ 14 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 22940588105726584
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_b29 : x.b ≤ 29
    · by_cases h_j5 : x.j ≤ 5
      · have hp := corner x ⟨29,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤29 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee29_5_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b16 : x.b ≤ 16
        · by_cases h_b9 : x.b ≤ 9
          · have hp := corner x ⟨9,8,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee9_8_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_j7 : x.j ≤ 7
            · by_cases h_j6 : x.j ≤ 6
              · have hp := corner x ⟨16,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee16_6_1_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b13 : x.b ≤ 13
                · have hp := corner x ⟨13,7,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤13 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee13_7_1_1] at hp
                  exact hp.trans (by decide)
                · by_cases h_b15 : x.b ≤ 15
                  · have hp := corner x ⟨15,7,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                    rw [fee15_7_1_1] at hp
                    exact hp.trans (by decide)
                  · have hp := corner x ⟨16,7,1⟩ 2 16 7 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                    rw [fee16_7_1_2] at hp
                    exact hp.trans (by decide)
            · have hp := corner x ⟨16,8,1⟩ 2 10 8 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
              rw [fee16_8_1_2] at hp
              exact hp.trans (by decide)
        · by_cases h_j7 : x.j ≤ 7
          · by_cases h_j6 : x.j ≤ 6
            · by_cases h_b23 : x.b ≤ 23
              · by_cases h_b20 : x.b ≤ 20
                · have hp := corner x ⟨20,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee20_6_1_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨23,6,1⟩ 2 21 6 hx (by exact ⟨(show x.b≤23 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                  rw [fee23_6_1_2] at hp
                  exact hp.trans (by decide)
              · have hp := corner x ⟨29,6,1⟩ 2 21 6 hx (by exact ⟨(show x.b≤29 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                rw [fee29_6_1_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨29,7,1⟩ 2 16 7 hx (by exact ⟨(show x.b≤29 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
              rw [fee29_7_1_2] at hp
              exact hp.trans (by decide)
          · have hp := corner x ⟨29,8,1⟩ 3 14 8 hx (by exact ⟨(show x.b≤29 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor0 ord ho))
            rw [fee29_8_1_3] at hp
            exact hp.trans (by decide)
    · by_cases h_j5 : x.j ≤ 5
      · have hp := corner x ⟨58,5,1⟩ 2 30 3 hx (by exact ⟨(show x.b≤58 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 4) (anchor6 ord ho))
        rw [fee58_5_1_2] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨58,8,1⟩ 6 29 6 hx (by exact ⟨(show x.b≤58 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 6 ≤ 10) (anchor3 ord ho))
        rw [fee58_8_1_6] at hp
        exact hp.trans (by decide)
  · by_cases h_b31 : x.b ≤ 31
    · by_cases h_b17 : x.b ≤ 17
      · by_cases h_j11 : x.j ≤ 11
        · have hp := corner x ⟨17,11,1⟩ 4 4 9 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor16 ord ho))
          rw [fee17_11_1_4] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨17,14,1⟩ 6 1 10 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤14 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 6 ≤ 7) (anchor4 ord ho))
          rw [fee17_14_1_6] at hp
          exact hp.trans (by decide)
      · have hp := corner x ⟨31,14,1⟩ 10 17 9 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤14 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 10 ≤ 11) (anchor2 ord ho))
        rw [fee31_14_1_10] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨58,14,1⟩ 19 32 9 hx (by exact ⟨(show x.b≤58 by omega),(show x.j≤14 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 19 ≤ 19) (anchor14 ord ho))
      rw [fee58_14_1_19] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup07

section Pack_Z6970CompanionGroup08

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group8 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule8 cost := by
  intro x hx hcap
  change x.b ≤ 62 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 22940588105726584
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_b31 : x.b ≤ 31
    · by_cases h_j5 : x.j ≤ 5
      · have hp := corner x ⟨31,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee31_5_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b17 : x.b ≤ 17
        · by_cases h_b10 : x.b ≤ 10
          · have hp := corner x ⟨10,8,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee10_8_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_j7 : x.j ≤ 7
            · by_cases h_j6 : x.j ≤ 6
              · have hp := corner x ⟨17,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee17_6_1_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b14 : x.b ≤ 14
                · have hp := corner x ⟨14,7,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee14_7_1_1] at hp
                  exact hp.trans (by decide)
                · by_cases h_b16 : x.b ≤ 16
                  · by_cases h_b15 : x.b ≤ 15
                    · have hp := corner x ⟨15,7,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                      rw [fee15_7_1_1] at hp
                      exact hp.trans (by decide)
                    · have hp := corner x ⟨16,7,1⟩ 2 16 7 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                      rw [fee16_7_1_2] at hp
                      exact hp.trans (by decide)
                  · have hp := corner x ⟨17,7,1⟩ 2 16 7 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                    rw [fee17_7_1_2] at hp
                    exact hp.trans (by decide)
            · have hp := corner x ⟨17,8,1⟩ 2 10 8 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
              rw [fee17_8_1_2] at hp
              exact hp.trans (by decide)
        · by_cases h_j7 : x.j ≤ 7
          · by_cases h_j6 : x.j ≤ 6
            · by_cases h_b24 : x.b ≤ 24
              · by_cases h_b21 : x.b ≤ 21
                · have hp := corner x ⟨21,6,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤21 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee21_6_1_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨24,6,1⟩ 2 21 6 hx (by exact ⟨(show x.b≤24 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                  rw [fee24_6_1_2] at hp
                  exact hp.trans (by decide)
              · have hp := corner x ⟨31,6,1⟩ 2 21 6 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                rw [fee31_6_1_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨31,7,1⟩ 3 18 7 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor19 ord ho))
              rw [fee31_7_1_3] at hp
              exact hp.trans (by decide)
          · have hp := corner x ⟨31,8,1⟩ 3 14 8 hx (by exact ⟨(show x.b≤31 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor0 ord ho))
            rw [fee31_8_1_3] at hp
            exact hp.trans (by decide)
    · by_cases h_j5 : x.j ≤ 5
      · have hp := corner x ⟨62,5,1⟩ 2 30 3 hx (by exact ⟨(show x.b≤62 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 4) (anchor6 ord ho))
        rw [fee62_5_1_2] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨62,8,1⟩ 7 29 6 hx (by exact ⟨(show x.b≤62 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 10) (anchor3 ord ho))
        rw [fee62_8_1_7] at hp
        exact hp.trans (by decide)
  · by_cases h_b33 : x.b ≤ 33
    · by_cases h_b18 : x.b ≤ 18
      · by_cases h_b11 : x.b ≤ 11
        · have hp := corner x ⟨11,13,1⟩ 4 4 9 hx (by exact ⟨(show x.b≤11 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor16 ord ho))
          rw [fee11_13_1_4] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨18,13,1⟩ 5 6 9 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 5 ≤ 5) (anchor17 ord ho))
          rw [fee18_13_1_5] at hp
          exact hp.trans (by decide)
      · have hp := corner x ⟨33,13,1⟩ 10 17 9 hx (by exact ⟨(show x.b≤33 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 10 ≤ 11) (anchor2 ord ho))
        rw [fee33_13_1_10] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨62,13,1⟩ 18 32 9 hx (by exact ⟨(show x.b≤62 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 18 ≤ 19) (anchor14 ord ho))
      rw [fee62_13_1_18] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup08

section Pack_Z6970CompanionGroup09

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group9 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule9 cost := by
  intro x hx hcap
  change x.b ≤ 10 ∧ x.j ≤ 15 ∧ x.t ≤ 2 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 22064481967072149
  by_cases h_j9 : x.j ≤ 9
  · by_cases h_j6 : x.j ≤ 6
    · have hp := corner x ⟨10,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
      rw [fee10_6_2_1] at hp
      exact hp.trans (by decide)
    · by_cases h_j8 : x.j ≤ 8
      · by_cases h_j7 : x.j ≤ 7
        · have hp := corner x ⟨10,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee10_7_2_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b6 : x.b ≤ 6
          · have hp := corner x ⟨6,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee6_8_2_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b8 : x.b ≤ 8
            · have hp := corner x ⟨8,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee8_8_2_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b9 : x.b ≤ 9
              · have hp := corner x ⟨9,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee9_8_2_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨10,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                rw [fee10_8_2_2] at hp
                exact hp.trans (by decide)
      · have hp := corner x ⟨10,9,2⟩ 2 2 9 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤9 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 3) (anchor7 ord ho))
        rw [fee10_9_2_2] at hp
        exact hp.trans (by decide)
  · have hp := corner x ⟨10,15,2⟩ 7 1 10 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤15 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor4 ord ho))
    rw [fee10_15_2_7] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup09

section Pack_Z6970CompanionGroup10

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group10 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule10 cost := by
  intro x hx hcap
  change x.b ≤ 38 ∧ x.j ≤ 18 ∧ x.t ≤ 2 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 25261884590037539
  by_cases h_j10 : x.j ≤ 10
  · by_cases h_j6 : x.j ≤ 6
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨38,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee38_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b20 : x.b ≤ 20
        · have hp := corner x ⟨20,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee20_6_2_1] at hp
          exact hp.trans (by decide)
        · by_cases h_j5 : x.j ≤ 5
          · have hp := corner x ⟨38,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee38_5_1_1] at hp
            exact hp.trans (by decide)
          · have hp := corner x ⟨38,6,2⟩ 2 21 6 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
            rw [fee38_6_2_2] at hp
            exact hp.trans (by decide)
    · by_cases h_b20 : x.b ≤ 20
      · by_cases h_j8 : x.j ≤ 8
        · by_cases h_b11 : x.b ≤ 11
          · by_cases h_j7 : x.j ≤ 7
            · have hp := corner x ⟨11,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤11 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee11_7_2_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b7 : x.b ≤ 7
              · have hp := corner x ⟨7,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee7_8_2_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b9 : x.b ≤ 9
                · have hp := corner x ⟨9,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee9_8_2_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨11,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤11 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                  rw [fee11_8_2_2] at hp
                  exact hp.trans (by decide)
          · by_cases h_j7 : x.j ≤ 7
            · by_cases h_b16 : x.b ≤ 16
              · by_cases h_b14 : x.b ≤ 14
                · have hp := corner x ⟨14,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee14_7_2_1] at hp
                  exact hp.trans (by decide)
                · by_cases h_b15 : x.b ≤ 15
                  · have hp := corner x ⟨15,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                    rw [fee15_7_2_1] at hp
                    exact hp.trans (by decide)
                  · have hp := corner x ⟨16,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                    rw [fee16_7_2_2] at hp
                    exact hp.trans (by decide)
              · have hp := corner x ⟨20,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                rw [fee20_7_2_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨20,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
              rw [fee20_8_2_2] at hp
              exact hp.trans (by decide)
        · have hp := corner x ⟨20,10,2⟩ 4 4 9 hx (by exact ⟨(show x.b≤20 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor16 ord ho))
          rw [fee20_10_2_4] at hp
          exact hp.trans (by decide)
      · by_cases h_j8 : x.j ≤ 8
        · have hp := corner x ⟨38,8,2⟩ 4 19 7 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor20 ord ho))
          rw [fee38_8_2_4] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨38,10,2⟩ 7 17 9 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 11) (anchor2 ord ho))
          rw [fee38_10_2_7] at hp
          exact hp.trans (by decide)
  · by_cases h_j14 : x.j ≤ 14
    · by_cases h_b21 : x.b ≤ 21
      · have hp := corner x ⟨21,14,2⟩ 7 1 10 hx (by exact ⟨(show x.b≤21 by omega),(show x.j≤14 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor4 ord ho))
        rw [fee21_14_2_7] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨38,14,2⟩ 13 21 10 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤14 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 13 ≤ 16) (anchor10 ord ho))
        rw [fee38_14_2_13] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨38,18,2⟩ 20 7 14 hx (by exact ⟨(show x.b≤38 by omega),(show x.j≤18 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 20 ≤ 21) (anchor12 ord ho))
      rw [fee38_18_2_20] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup10

section Pack_Z6970CompanionGroup11

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group11 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 0 ord)
    (corner : Corners ord cost) : Within rule11 cost := by
  intro x hx hcap
  change x.b ≤ 125 ∧ x.j ≤ 10 ∧ x.t ≤ 2 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 25261884590037539
  by_cases h_b63 : x.b ≤ 63
  · by_cases h_b32 : x.b ≤ 32
    · by_cases h_j6 : x.j ≤ 6
      · by_cases h_j4 : x.j ≤ 4
        · have hp := corner x ⟨32,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤32 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee32_4_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b17 : x.b ≤ 17
          · have hp := corner x ⟨17,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee17_6_2_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b25 : x.b ≤ 25
            · by_cases h_j5 : x.j ≤ 5
              · have hp := corner x ⟨25,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤25 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee25_5_1_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b21 : x.b ≤ 21
                · have hp := corner x ⟨21,6,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤21 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee21_6_2_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨25,6,2⟩ 2 21 6 hx (by exact ⟨(show x.b≤25 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor1 ord ho))
                  rw [fee25_6_2_2] at hp
                  exact hp.trans (by decide)
            · have hp := corner x ⟨32,6,2⟩ 2 25 5 hx (by exact ⟨(show x.b≤32 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 3) (anchor5 ord ho))
              rw [fee32_6_2_2] at hp
              exact hp.trans (by decide)
      · by_cases h_b17 : x.b ≤ 17
        · by_cases h_j8 : x.j ≤ 8
          · by_cases h_b10 : x.b ≤ 10
            · have hp := corner x ⟨10,8,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee10_8_2_1] at hp
              exact hp.trans (by decide)
            · by_cases h_j7 : x.j ≤ 7
              · by_cases h_b14 : x.b ≤ 14
                · have hp := corner x ⟨14,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee14_7_2_1] at hp
                  exact hp.trans (by decide)
                · by_cases h_b16 : x.b ≤ 16
                  · by_cases h_b15 : x.b ≤ 15
                    · have hp := corner x ⟨15,7,2⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                      rw [fee15_7_2_1] at hp
                      exact hp.trans (by decide)
                    · have hp := corner x ⟨16,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤16 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                      rw [fee16_7_2_2] at hp
                      exact hp.trans (by decide)
                  · have hp := corner x ⟨17,7,2⟩ 2 16 7 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor9 ord ho))
                    rw [fee17_7_2_2] at hp
                    exact hp.trans (by decide)
              · have hp := corner x ⟨17,8,2⟩ 2 10 8 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor8 ord ho))
                rw [fee17_8_2_2] at hp
                exact hp.trans (by decide)
          · have hp := corner x ⟨17,10,2⟩ 3 2 9 hx (by exact ⟨(show x.b≤17 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor7 ord ho))
            rw [fee17_10_2_3] at hp
            exact hp.trans (by decide)
        · by_cases h_j8 : x.j ≤ 8
          · by_cases h_j7 : x.j ≤ 7
            · have hp := corner x ⟨32,7,2⟩ 3 18 7 hx (by exact ⟨(show x.b≤32 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor19 ord ho))
              rw [fee32_7_2_3] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨32,8,2⟩ 4 14 8 hx (by exact ⟨(show x.b≤32 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 5) (anchor0 ord ho))
              rw [fee32_8_2_4] at hp
              exact hp.trans (by decide)
          · have hp := corner x ⟨32,10,2⟩ 6 17 9 hx (by exact ⟨(show x.b≤32 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 6 ≤ 11) (anchor2 ord ho))
            rw [fee32_10_2_6] at hp
            exact hp.trans (by decide)
    · by_cases h_j6 : x.j ≤ 6
      · have hp := corner x ⟨63,6,2⟩ 3 30 3 hx (by exact ⟨(show x.b≤63 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 4) (anchor6 ord ho))
        rw [fee63_6_2_3] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨63,10,2⟩ 10 29 6 hx (by exact ⟨(show x.b≤63 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 10 ≤ 10) (anchor3 ord ho))
        rw [fee63_10_2_10] at hp
        exact hp.trans (by decide)
  · have hp := corner x ⟨125,10,2⟩ 20 48 3 hx (by exact ⟨(show x.b≤125 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 20 ≤ 20) (anchor11 ord ho))
    rw [fee125_10_2_20] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup11

section Pack_Z6970CompanionGroup12

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group12 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 2 ord)
    (corner : Corners ord cost) : Within rule12 cost := by
  intro x hx hcap
  change x.b ≤ 19 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 3570788005668000
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · by_cases h_j3 : x.j ≤ 3
        · have hp := corner x ⟨19,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee19_3_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b10 : x.b ≤ 10
          · have hp := corner x ⟨10,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee10_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b15 : x.b ≤ 15
            · by_cases h_b13 : x.b ≤ 13
              · have hp := corner x ⟨13,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤13 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee13_4_1_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨15,4,1⟩ 2 14 4 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor26 ord ho))
                rw [fee15_4_1_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨19,4,1⟩ 2 14 4 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor26 ord ho))
              rw [fee19_4_1_2] at hp
              exact hp.trans (by decide)
      · by_cases h_b10 : x.b ≤ 10
        · by_cases h_b6 : x.b ≤ 6
          · have hp := corner x ⟨6,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee6_5_1_1] at hp
            exact hp.trans (by decide)
          · have hp := corner x ⟨10,5,1⟩ 2 7 5 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor31 ord ho))
            rw [fee10_5_1_2] at hp
            exact hp.trans (by decide)
        · have hp := corner x ⟨19,5,1⟩ 4 9 5 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor32 ord ho))
          rw [fee19_5_1_4] at hp
          exact hp.trans (by decide)
    · by_cases h_b11 : x.b ≤ 11
      · by_cases h_b7 : x.b ≤ 7
        · have hp := corner x ⟨7,8,1⟩ 5 2 6 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 5 ≤ 5) (anchor24 ord ho))
          rw [fee7_8_1_5] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨11,8,1⟩ 7 4 6 hx (by exact ⟨(show x.b≤11 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor30 ord ho))
          rw [fee11_8_1_7] at hp
          exact hp.trans (by decide)
      · have hp := corner x ⟨19,8,1⟩ 12 11 6 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 12 ≤ 12) (anchor33 ord ho))
        rw [fee19_8_1_12] at hp
        exact hp.trans (by decide)
  · by_cases h_j11 : x.j ≤ 11
    · by_cases h_j10 : x.j ≤ 10
      · have hp := corner x ⟨19,10,1⟩ 20 3 9 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 20 ≤ 22) (anchor25 ord ho))
        rw [fee19_10_1_20] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨19,11,1⟩ 25 1 11 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 25 ≤ 27) (anchor28 ord ho))
        rw [fee19_11_1_25] at hp
        exact hp.trans (by decide)
    · by_cases h_j12 : x.j ≤ 12
      · have hp := corner x ⟨19,12,1⟩ 29 1 12 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤12 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 29 ≤ 30) (anchor29 ord ho))
        rw [fee19_12_1_29] at hp
        exact hp.trans (by decide)
      · by_cases h_b12 : x.b ≤ 12
        · have hp := corner x ⟨12,13,1⟩ 22 3 9 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 22 ≤ 22) (anchor25 ord ho))
          rw [fee12_13_1_22] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨19,13,1⟩ 34 11 13 hx (by exact ⟨(show x.b≤19 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 34 ≤ 34) (anchor34 ord ho))
          rw [fee19_13_1_34] at hp
          exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup12

section Pack_Z6970CompanionGroup13

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group13 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 2 ord)
    (corner : Corners ord cost) : Within rule13 cost := by
  intro x hx hcap
  change x.b ≤ 4 ∧ x.j ≤ 10 ∧ x.t ≤ 2 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 2865653131914797
  by_cases h_j6 : x.j ≤ 6
  · by_cases h_t1 : x.t ≤ 1
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨4,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee4_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_j5 : x.j ≤ 5
        · have hp := corner x ⟨4,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee4_5_1_1] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨4,6,1⟩ 3 2 6 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor24 ord ho))
          rw [fee4_6_1_3] at hp
          exact hp.trans (by decide)
    · have hp := corner x ⟨4,6,2⟩ 3 2 6 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤6 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor24 ord ho))
      rw [fee4_6_2_3] at hp
      exact hp.trans (by decide)
  · by_cases h_j8 : x.j ≤ 8
    · have hp := corner x ⟨4,8,2⟩ 7 1 7 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 11) (anchor27 ord ho))
      rw [fee4_8_2_7] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨4,10,2⟩ 16 3 9 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤10 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 16 ≤ 22) (anchor25 ord ho))
      rw [fee4_10_2_16] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup13

section Pack_Z6970CompanionGroup14

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group14 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 3 ord)
    (corner : Corners ord cost) : Within rule14 cost := by
  intro x hx hcap
  change x.b ≤ 18 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 3285684089007720
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · by_cases h_j3 : x.j ≤ 3
        · have hp := corner x ⟨18,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee18_3_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b10 : x.b ≤ 10
          · have hp := corner x ⟨10,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee10_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b14 : x.b ≤ 14
            · by_cases h_b12 : x.b ≤ 12
              · have hp := corner x ⟨12,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee12_4_1_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨14,4,1⟩ 2 13 4 hx (by exact ⟨(show x.b≤14 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor38 ord ho))
                rw [fee14_4_1_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨18,4,1⟩ 2 13 4 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor38 ord ho))
              rw [fee18_4_1_2] at hp
              exact hp.trans (by decide)
      · by_cases h_b10 : x.b ≤ 10
        · by_cases h_b6 : x.b ≤ 6
          · by_cases h_b4 : x.b ≤ 4
            · have hp := corner x ⟨4,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee4_5_1_1] at hp
              exact hp.trans (by decide)
            · by_cases h_b5 : x.b ≤ 5
              · have hp := corner x ⟨5,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee5_5_1_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨6,5,1⟩ 2 6 5 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor37 ord ho))
                rw [fee6_5_1_2] at hp
                exact hp.trans (by decide)
          · have hp := corner x ⟨10,5,1⟩ 2 6 5 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor37 ord ho))
            rw [fee10_5_1_2] at hp
            exact hp.trans (by decide)
        · have hp := corner x ⟨18,5,1⟩ 4 8 5 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor42 ord ho))
          rw [fee18_5_1_4] at hp
          exact hp.trans (by decide)
    · by_cases h_b10 : x.b ≤ 10
      · have hp := corner x ⟨10,8,1⟩ 7 3 6 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor36 ord ho))
        rw [fee10_8_1_7] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨18,8,1⟩ 12 9 6 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 12 ≤ 12) (anchor43 ord ho))
        rw [fee18_8_1_12] at hp
        exact hp.trans (by decide)
  · by_cases h_j11 : x.j ≤ 11
    · by_cases h_j10 : x.j ≤ 10
      · have hp := corner x ⟨18,10,1⟩ 21 1 9 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 21 ≤ 22) (anchor40 ord ho))
        rw [fee18_10_1_21] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨18,11,1⟩ 25 1 10 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 25 ≤ 25) (anchor35 ord ho))
        rw [fee18_11_1_25] at hp
        exact hp.trans (by decide)
    · by_cases h_b12 : x.b ≤ 12
      · have hp := corner x ⟨12,13,1⟩ 24 1 10 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 24 ≤ 25) (anchor35 ord ho))
        rw [fee12_13_1_24] at hp
        exact hp.trans (by decide)
      · by_cases h_j12 : x.j ≤ 12
        · have hp := corner x ⟨18,12,1⟩ 30 1 12 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤12 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 30 ≤ 30) (anchor41 ord ho))
          rw [fee18_12_1_30] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨18,13,1⟩ 35 13 13 hx (by exact ⟨(show x.b≤18 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 35 ≤ 35) (anchor44 ord ho))
          rw [fee18_13_1_35] at hp
          exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup14

section Pack_Z6970CompanionGroup15

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group15 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 3 ord)
    (corner : Corners ord cost) : Within rule15 cost := by
  intro x hx hcap
  change x.b ≤ 3 ∧ x.j ≤ 8 ∧ x.t ≤ 2 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 2865635836600980
  by_cases h_j5 : x.j ≤ 5
  · have hp := corner x ⟨3,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤3 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
    rw [fee3_5_1_1] at hp
    exact hp.trans (by decide)
  · by_cases h_j7 : x.j ≤ 7
    · have hp := corner x ⟨3,7,2⟩ 5 1 6 hx (by exact ⟨(show x.b≤3 by omega),(show x.j≤7 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 5 ≤ 5) (anchor39 ord ho))
      rw [fee3_7_2_5] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨3,8,2⟩ 7 3 6 hx (by exact ⟨(show x.b≤3 by omega),(show x.j≤8 by omega),(show x.t≤2 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor36 ord ho))
      rw [fee3_8_2_7] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup15

section Pack_Z6970CompanionGroup16

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group16 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 4 ord)
    (corner : Corners ord cost) : Within rule16 cost := by
  intro x hx hcap
  change x.b ≤ 15 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 3000588283283676
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · by_cases h_j3 : x.j ≤ 3
        · have hp := corner x ⟨15,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee15_3_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b8 : x.b ≤ 8
          · have hp := corner x ⟨8,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee8_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b12 : x.b ≤ 12
            · by_cases h_b10 : x.b ≤ 10
              · have hp := corner x ⟨10,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee10_4_1_1] at hp
                exact hp.trans (by decide)
              · by_cases h_b11 : x.b ≤ 11
                · have hp := corner x ⟨11,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤11 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                  rw [fee11_4_1_1] at hp
                  exact hp.trans (by decide)
                · have hp := corner x ⟨12,4,1⟩ 2 12 4 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor45 ord ho))
                  rw [fee12_4_1_2] at hp
                  exact hp.trans (by decide)
            · have hp := corner x ⟨15,4,1⟩ 2 12 4 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor45 ord ho))
              rw [fee15_4_1_2] at hp
              exact hp.trans (by decide)
      · by_cases h_b8 : x.b ≤ 8
        · by_cases h_b5 : x.b ≤ 5
          · have hp := corner x ⟨5,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee5_5_1_1] at hp
            exact hp.trans (by decide)
          · have hp := corner x ⟨8,5,1⟩ 2 5 5 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor49 ord ho))
            rw [fee8_5_1_2] at hp
            exact hp.trans (by decide)
        · have hp := corner x ⟨15,5,1⟩ 4 7 5 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 4) (anchor50 ord ho))
          rw [fee15_5_1_4] at hp
          exact hp.trans (by decide)
    · by_cases h_b9 : x.b ≤ 9
      · have hp := corner x ⟨9,8,1⟩ 7 2 6 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor48 ord ho))
        rw [fee9_8_1_7] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨15,8,1⟩ 11 7 6 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 11 ≤ 11) (anchor51 ord ho))
        rw [fee15_8_1_11] at hp
        exact hp.trans (by decide)
  · by_cases h_j11 : x.j ≤ 11
    · have hp := corner x ⟨15,11,1⟩ 22 1 9 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 22 ≤ 22) (anchor46 ord ho))
      rw [fee15_11_1_22] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨15,13,1⟩ 31 1 12 hx (by exact ⟨(show x.b≤15 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 31 ≤ 31) (anchor47 ord ho))
      rw [fee15_13_1_31] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup16

section Pack_Z6970CompanionGroup17

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group17 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 5 ord)
    (corner : Corners ord cost) : Within rule17 cost := by
  intro x hx hcap
  change x.b ≤ 12 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 2865635836600980
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · by_cases h_j3 : x.j ≤ 3
        · have hp := corner x ⟨12,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee12_3_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b7 : x.b ≤ 7
          · have hp := corner x ⟨7,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee7_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b10 : x.b ≤ 10
            · have hp := corner x ⟨10,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤10 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee10_4_1_1] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨12,4,1⟩ 2 11 4 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor57 ord ho))
              rw [fee12_4_1_2] at hp
              exact hp.trans (by decide)
      · by_cases h_b7 : x.b ≤ 7
        · by_cases h_b4 : x.b ≤ 4
          · by_cases h_b3 : x.b ≤ 3
            · have hp := corner x ⟨3,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤3 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee3_5_1_1] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨4,5,1⟩ 2 4 5 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor52 ord ho))
              rw [fee4_5_1_2] at hp
              exact hp.trans (by decide)
          · have hp := corner x ⟨7,5,1⟩ 2 4 5 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor52 ord ho))
            rw [fee7_5_1_2] at hp
            exact hp.trans (by decide)
        · have hp := corner x ⟨12,5,1⟩ 3 5 5 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor56 ord ho))
          rw [fee12_5_1_3] at hp
          exact hp.trans (by decide)
    · have hp := corner x ⟨12,8,1⟩ 9 3 6 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 9 ≤ 9) (anchor55 ord ho))
      rw [fee12_8_1_9] at hp
      exact hp.trans (by decide)
  · by_cases h_j11 : x.j ≤ 11
    · have hp := corner x ⟨12,11,1⟩ 18 1 8 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 18 ≤ 19) (anchor53 ord ho))
      rw [fee12_11_1_18] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨12,13,1⟩ 27 1 10 hx (by exact ⟨(show x.b≤12 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 27 ≤ 27) (anchor54 ord ho))
      rw [fee12_13_1_27] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup17

section Pack_Z6970CompanionGroup18

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group18 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 6 ord)
    (corner : Corners ord cost) : Within rule18 cost := by
  intro x hx hcap
  change x.b ≤ 9 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 2865618541287163
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨9,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee9_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b5 : x.b ≤ 5
        · by_cases h_b3 : x.b ≤ 3
          · by_cases h_b2 : x.b ≤ 2
            · have hp := corner x ⟨2,5,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
              rw [fee2_5_1_1] at hp
              exact hp.trans (by decide)
            · have hp := corner x ⟨3,5,1⟩ 2 3 5 hx (by exact ⟨(show x.b≤3 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor58 ord ho))
              rw [fee3_5_1_2] at hp
              exact hp.trans (by decide)
          · have hp := corner x ⟨5,5,1⟩ 2 3 5 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor58 ord ho))
            rw [fee5_5_1_2] at hp
            exact hp.trans (by decide)
        · have hp := corner x ⟨9,5,1⟩ 2 3 5 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor58 ord ho))
          rw [fee9_5_1_2] at hp
          exact hp.trans (by decide)
    · have hp := corner x ⟨9,8,1⟩ 7 1 6 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 8) (anchor59 ord ho))
      rw [fee9_8_1_7] at hp
      exact hp.trans (by decide)
  · by_cases h_j11 : x.j ≤ 11
    · have hp := corner x ⟨9,11,1⟩ 16 1 8 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 16 ≤ 20) (anchor60 ord ho))
      rw [fee9_11_1_16] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨9,13,1⟩ 27 1 10 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 27 ≤ 27) (anchor61 ord ho))
      rw [fee9_13_1_27] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup18

section Pack_Z6970CompanionGroup19

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group19 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 7 ord)
    (corner : Corners ord cost) : Within rule19 cost := by
  intro x hx hcap
  change x.b ≤ 8 ∧ x.j ≤ 13 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 2167821865059093
  by_cases h_j8 : x.j ≤ 8
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨8,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee8_4_1_1] at hp
        exact hp.trans (by decide)
      · by_cases h_b5 : x.b ≤ 5
        · have hp := corner x ⟨5,5,1⟩ 2 2 5 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor66 ord ho))
          rw [fee5_5_1_2] at hp
          exact hp.trans (by decide)
        · have hp := corner x ⟨8,5,1⟩ 3 3 5 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor68 ord ho))
          rw [fee8_5_1_3] at hp
          exact hp.trans (by decide)
    · have hp := corner x ⟨8,8,1⟩ 8 1 6 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 8 ≤ 9) (anchor63 ord ho))
      rw [fee8_8_1_8] at hp
      exact hp.trans (by decide)
  · by_cases h_j11 : x.j ≤ 11
    · have hp := corner x ⟨8,11,1⟩ 22 1 9 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 22 ≤ 25) (anchor64 ord ho))
      rw [fee8_11_1_22] at hp
      exact hp.trans (by decide)
    · by_cases h_j12 : x.j ≤ 12
      · have hp := corner x ⟨8,12,1⟩ 28 1 10 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤12 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 28 ≤ 28) (anchor65 ord ho))
        rw [fee8_12_1_28] at hp
        exact hp.trans (by decide)
      · by_cases h_b7 : x.b ≤ 7
        · by_cases h_b6 : x.b ≤ 6
          · have hp := corner x ⟨6,13,1⟩ 36 2 13 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 36 ≤ 36) (anchor67 ord ho))
            rw [fee6_13_1_36] at hp
            exact hp.trans (by decide)
          · have hp := corner x ⟨7,13,1⟩ 37 7 13 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 37 ≤ 37) (anchor62 ord ho))
            rw [fee7_13_1_37] at hp
            exact hp.trans (by decide)
        · have hp := corner x ⟨8,13,1⟩ 37 7 13 hx (by exact ⟨(show x.b≤8 by omega),(show x.j≤13 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 37 ≤ 37) (anchor62 ord ho))
          rw [fee8_13_1_37] at hp
          exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup19

section Pack_Z6970CompanionGroup20

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group20 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 8 ord)
    (corner : Corners ord cost) : Within rule20 cost := by
  intro x hx hcap
  change x.b ≤ 5 ∧ x.j ≤ 11 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1430783657172211
  by_cases h_j7 : x.j ≤ 7
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨5,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee5_4_1_1] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨5,5,1⟩ 3 2 5 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor72 ord ho))
        rw [fee5_5_1_3] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨5,7,1⟩ 8 1 6 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 8 ≤ 11) (anchor69 ord ho))
      rw [fee5_7_1_8] at hp
      exact hp.trans (by decide)
  · by_cases h_j9 : x.j ≤ 9
    · have hp := corner x ⟨5,9,1⟩ 18 1 8 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤9 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 18 ≤ 22) (anchor70 ord ho))
      rw [fee5_9_1_18] at hp
      exact hp.trans (by decide)
    · by_cases h_j10 : x.j ≤ 10
      · have hp := corner x ⟨5,10,1⟩ 25 1 9 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 25 ≤ 26) (anchor71 ord ho))
        rw [fee5_10_1_25] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨5,11,1⟩ 33 4 11 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 33 ≤ 33) (anchor73 ord ho))
        rw [fee5_11_1_33] at hp
        exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup20

section Pack_Z6970CompanionGroup21

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group21 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 9 ord)
    (corner : Corners ord cost) : Within rule21 cost := by
  intro x hx hcap
  change x.b ≤ 2 ∧ x.j ≤ 5 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1005118269738545
  by_cases h_j4 : x.j ≤ 4
  · have hp := corner x ⟨2,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
    rw [fee2_4_1_1] at hp
    exact hp.trans (by decide)
  · have hp := corner x ⟨2,5,1⟩ 3 1 5 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 3) (anchor74 ord ho))
    rw [fee2_5_1_3] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup21

section Pack_Z6970CompanionGroup22

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group22 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 10 ord)
    (corner : Corners ord cost) : Within rule22 cost := by
  intro x hx hcap
  change x.b ≤ 9 ∧ x.j ≤ 12 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1668452430029632
  by_cases h_j7 : x.j ≤ 7
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · by_cases h_j3 : x.j ≤ 3
        · have hp := corner x ⟨9,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
          rw [fee9_3_1_1] at hp
          exact hp.trans (by decide)
        · by_cases h_b5 : x.b ≤ 5
          · have hp := corner x ⟨5,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤5 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
            rw [fee5_4_1_1] at hp
            exact hp.trans (by decide)
          · by_cases h_b7 : x.b ≤ 7
            · by_cases h_b6 : x.b ≤ 6
              · have hp := corner x ⟨6,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
                rw [fee6_4_1_1] at hp
                exact hp.trans (by decide)
              · have hp := corner x ⟨7,4,1⟩ 2 7 4 hx (by exact ⟨(show x.b≤7 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor75 ord ho))
                rw [fee7_4_1_2] at hp
                exact hp.trans (by decide)
            · have hp := corner x ⟨9,4,1⟩ 2 7 4 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 2) (anchor75 ord ho))
              rw [fee9_4_1_2] at hp
              exact hp.trans (by decide)
      · have hp := corner x ⟨9,5,1⟩ 4 1 5 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 4 ≤ 5) (anchor76 ord ho))
        rw [fee9_5_1_4] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨9,7,1⟩ 9 1 6 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 9 ≤ 13) (anchor77 ord ho))
      rw [fee9_7_1_9] at hp
      exact hp.trans (by decide)
  · by_cases h_j10 : x.j ≤ 10
    · have hp := corner x ⟨9,10,1⟩ 21 1 8 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 21 ≤ 24) (anchor78 ord ho))
      rw [fee9_10_1_21] at hp
      exact hp.trans (by decide)
    · by_cases h_j11 : x.j ≤ 11
      · have hp := corner x ⟨9,11,1⟩ 28 1 9 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 28 ≤ 28) (anchor79 ord ho))
        rw [fee9_11_1_28] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨9,12,1⟩ 37 6 12 hx (by exact ⟨(show x.b≤9 by omega),(show x.j≤12 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 37 ≤ 37) (anchor80 ord ho))
        rw [fee9_12_1_37] at hp
        exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup22

section Pack_Z6970CompanionGroup23

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group23 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 11 ord)
    (corner : Corners ord cost) : Within rule23 cost := by
  intro x hx hcap
  change x.b ≤ 6 ∧ x.j ≤ 12 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1668445592710835
  by_cases h_j7 : x.j ≤ 7
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨6,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee6_4_1_1] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨6,5,1⟩ 3 2 5 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 7) (anchor81 ord ho))
        rw [fee6_5_1_3] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨6,7,1⟩ 7 2 5 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 7) (anchor81 ord ho))
      rw [fee6_7_1_7] at hp
      exact hp.trans (by decide)
  · by_cases h_j10 : x.j ≤ 10
    · have hp := corner x ⟨6,10,1⟩ 21 1 8 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 21 ≤ 25) (anchor82 ord ho))
      rw [fee6_10_1_21] at hp
      exact hp.trans (by decide)
    · by_cases h_j11 : x.j ≤ 11
      · have hp := corner x ⟨6,11,1⟩ 28 1 9 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 28 ≤ 29) (anchor83 ord ho))
        rw [fee6_11_1_28] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨6,12,1⟩ 37 2 12 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤12 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 37 ≤ 37) (anchor84 ord ho))
        rw [fee6_12_1_37] at hp
        exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup23

section Pack_Z6970CompanionGroup24

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group24 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 12 ord)
    (corner : Corners ord cost) : Within rule24 cost := by
  intro x hx hcap
  change x.b ≤ 2 ∧ x.j ≤ 5 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1005118269738545
  by_cases h_j4 : x.j ≤ 4
  · have hp := corner x ⟨2,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
    rw [fee2_4_1_1] at hp
    exact hp.trans (by decide)
  · have hp := corner x ⟨2,5,1⟩ 3 1 5 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 7) (anchor85 ord ho))
    rw [fee2_5_1_3] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup24

section Pack_Z6970CompanionGroup25

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group25 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 13 ord)
    (corner : Corners ord cost) : Within rule25 cost := by
  intro x hx hcap
  change x.b ≤ 6 ∧ x.j ≤ 12 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1589275447697825
  by_cases h_j7 : x.j ≤ 7
  · by_cases h_j5 : x.j ≤ 5
    · by_cases h_j4 : x.j ≤ 4
      · have hp := corner x ⟨6,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
        rw [fee6_4_1_1] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨6,5,1⟩ 3 1 5 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 9) (anchor86 ord ho))
        rw [fee6_5_1_3] at hp
        exact hp.trans (by decide)
    · have hp := corner x ⟨6,7,1⟩ 7 1 5 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤7 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 7 ≤ 9) (anchor86 ord ho))
      rw [fee6_7_1_7] at hp
      exact hp.trans (by decide)
  · by_cases h_j10 : x.j ≤ 10
    · have hp := corner x ⟨6,10,1⟩ 22 1 7 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤10 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 22 ≤ 22) (anchor87 ord ho))
      rw [fee6_10_1_22] at hp
      exact hp.trans (by decide)
    · by_cases h_j11 : x.j ≤ 11
      · have hp := corner x ⟨6,11,1⟩ 30 1 9 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤11 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 30 ≤ 30) (anchor88 ord ho))
        rw [fee6_11_1_30] at hp
        exact hp.trans (by decide)
      · have hp := corner x ⟨6,12,1⟩ 39 3 12 hx (by exact ⟨(show x.b≤6 by omega),(show x.j≤12 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 39 ≤ 39) (anchor89 ord ho))
        rw [fee6_12_1_39] at hp
        exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup25

section Pack_Z6970CompanionGroup26

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group26 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 14 ord)
    (corner : Corners ord cost) : Within rule26 cost := by
  intro x hx hcap
  change x.b ≤ 2 ∧ x.j ≤ 5 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 1005118269738545
  by_cases h_j4 : x.j ≤ 4
  · have hp := corner x ⟨2,4,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
    rw [fee2_4_1_1] at hp
    exact hp.trans (by decide)
  · have hp := corner x ⟨2,5,1⟩ 3 1 5 hx (by exact ⟨(show x.b≤2 by omega),(show x.j≤5 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 3 ≤ 5) (anchor90 ord ho))
    rw [fee2_5_1_3] at hp
    exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup26

section Pack_Z6970CompanionGroup27

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group27 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 17 ord)
    (corner : Corners ord cost) : Within rule27 cost := by
  intro x hx hcap
  change x.b ≤ 1 ∧ x.j ≤ 3 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 145518067411104
  have hp := corner x ⟨1,3,1⟩ 1 0 0 hx (by exact ⟨(show x.b≤1 by omega),(show x.j≤3 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (ho.1 0 0)
  rw [fee1_3_1_1] at hp
  exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup27

section Pack_Z6970CompanionGroup28

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 15000
set_option maxHeartbeats 1800000

namespace Height2307Companion
open K1_13 (Shape InBox)

theorem group28 (ord : ℕ → ℕ → ℕ) (cost : Shape → ℕ) (ho : Supports anchors 20 ord)
    (corner : Corners ord cost) : Within rule28 cost := by
  intro x hx hcap
  change x.b ≤ 4 ∧ x.j ≤ 9 ∧ x.t ≤ 1 at hcap
  obtain ⟨hB,hJ,hT⟩ := hcap
  obtain ⟨ha,hd,hc,he⟩ := (show legal x from hx)
  change 1 ≤ x.t at ha
  change 3*x.t ≤ x.j at hd
  change x.t ≤ x.b at hc
  change x.j ≤ 2*x.b+x.t at he
  change cost x ≤ 574383712170791
  by_cases h_j6 : x.j ≤ 6
  · by_cases h_j4 : x.j ≤ 4
    · have hp := corner x ⟨4,4,1⟩ 2 1 3 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤4 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 2 ≤ 8) (anchor91 ord ho))
      rw [fee4_4_1_2] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨4,6,1⟩ 11 1 4 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤6 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 11 ≤ 20) (anchor92 ord ho))
      rw [fee4_6_1_11] at hp
      exact hp.trans (by decide)
  · by_cases h_j8 : x.j ≤ 8
    · have hp := corner x ⟨4,8,1⟩ 31 1 6 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤8 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 31 ≤ 35) (anchor93 ord ho))
      rw [fee4_8_1_31] at hp
      exact hp.trans (by decide)
    · have hp := corner x ⟨4,9,1⟩ 46 1 9 hx (by exact ⟨(show x.b≤4 by omega),(show x.j≤9 by omega),(show x.t≤1 by omega)⟩) (by decide) (by omega) (by omega) (by decide) (le_trans (by decide : 46 ≤ 46) (anchor94 ord ho))
      rw [fee4_9_1_46] at hp
      exact hp.trans (by decide)

end Height2307Companion
end Pack_Z6970CompanionGroup28
