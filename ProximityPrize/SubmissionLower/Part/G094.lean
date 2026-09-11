import ProximityPrize.SubmissionLower.Part.G093


section Compact_SecondJetSingleCap
/-! Affine, conservatively rounded costs for the three concrete profiles. -/
namespace ProximityPrize.SubmissionLower.SecondJetSingleCap
open RCN095 LocatorFactorAggregate SecondJetRegularData SecondJetRegularData.Data
open SecondJetOwnShape SecondJetAffineCeiling
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
variable {nodes : I ↪ K} {u0 u1 : I → K}

def profile (B U L k n0 r v z : ℕ) : ℕ :=
  let q := SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0
  SecondJetNumericGeometry.normal r v z + 131076*
    ((moving r v (L+1) q+k)/(k+1)+(z-(L+1))*((movingSlope r v q+k)/(k+1)))+
      500000000000000

def activated (B U L k n0 : ℕ) (p : FlagDegree) : ℕ :=
  if 3 ≤ p.all ∧ 2 ≤ p.yz ∧ L < p.zOnly then
    profile B U L k n0 p.all p.yz p.zOnly
  else LocatorHybridCost.ordinaryCostOf p

def cap (p : FlagDegree) : ℕ :=
  min (LocatorHybridCost.ordinaryCostOf p)
    (min (activated 47 157 2233 5 7 p)
      (min (activated 38 130 2141 4 5 p) (activated 41 146 2111 4 7 p)))

def slope (B U L k n0 r v : ℕ) : ℕ :=
  (SecondJetNumericGeometry.normal r v 1-SecondJetNumericGeometry.normal r v 0) + 131076*
    ((movingSlope r v (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)+k)/(k+1))

theorem normal_add (r v z h : ℕ) :
    SecondJetNumericGeometry.normal r v (z+h) =
      SecondJetNumericGeometry.normal r v z+
        h*(SecondJetNumericGeometry.normal r v 1-SecondJetNumericGeometry.normal r v 0) := by
  have hid : SecondJetNumericGeometry.normal r v (z+h)+h*SecondJetNumericGeometry.normal r v 0 =
      SecondJetNumericGeometry.normal r v z+h*SecondJetNumericGeometry.normal r v 1 := by
    simp only [SecondJetNumericGeometry.normal,flagMixed]
    ring
  have hle : SecondJetNumericGeometry.normal r v 0 ≤ SecondJetNumericGeometry.normal r v 1 := by
    dsimp [SecondJetNumericGeometry.normal,flagMixed]
    gcongr <;> norm_num
  have hs := Nat.sub_add_cancel hle
  nlinarith

theorem profile_affine (B U L k n0 r v lo z : ℕ) (hlo : L+1 ≤ lo) (hz : lo ≤ z) :
    profile B U L k n0 r v z = profile B U L k n0 r v lo+
      slope B U L k n0 r v*(z-lo) := by
  have h1 : z = lo+(z-lo) := by omega
  have h2 : z-(L+1) = (lo-(L+1))+(z-lo) := by omega
  have hn := normal_add r v lo (z-lo)
  rw [←h1] at hn
  dsimp only [profile,slope]
  rw [hn,h2]
  ring

theorem moving_eq (S : Data nodes u0 u1) (hown : Own S) (B U L k n0 : ℕ) :
    S.moving B U L k n0 = moving S.r (S.y-S.r) (S.t-S.y)
      (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) := by
  have h3 : 2*(S.y-S.r-1)+2 = 2*(S.y-S.r) := by have := S.ry; omega
  have h4 : 2*(S.r-2)+2 = 2*(S.r-1) := by have := S.rpos; omega
  unfold Data.moving
  rw [hown,SecondJetIdentity.cell_first_eq]
  simp only [Lower80788.HybridIdentityC2.reducedABS,LocatorHybridCells.cellA,
    LocatorHybridCells.cellB,LocatorHybridCells.cellS,h3,h4,SecondJetAffineCeiling.moving,flagMixed]
  ring

theorem cost_le_profile (S : Data nodes u0 u1) (hown : Own S)
    (B U L k n0 : ℕ) (hL : L < S.t-S.y) :
    SecondJetProfileBounds.cost S B U L k n0 ≤
      profile B U L k n0 S.r (S.y-S.r) (S.t-S.y) := by
  have hz : S.t-S.y = (L+1)+(S.t-S.y-(L+1)) := by omega
  have h := moving_ceil_add_le S.r (S.y-S.r) (L+1) (S.t-S.y-(L+1)) k
    (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)
  rw [←hz] at h
  unfold SecondJetProfileBounds.cost profile
  rw [normal_eq S hown,moving_eq S hown]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 131076 h) _) _

theorem count_116 (S : Data nodes u0 u1) (hI : Fintype.card I=262144)
    (hown : Own S) (hL : 2233 < S.t-S.y) :
    S.seeds.card ≤ profile 47 157 2233 5 7 S.r (S.y-S.r) (S.t-S.y) :=
  (SecondJetProfileBounds.count_116 S hI hown hL).trans (cost_le_profile S hown _ _ _ _ _ hL)

theorem count_96 (S : Data nodes u0 u1) (hI : Fintype.card I=262144)
    (hown : Own S) (hL : 2141 < S.t-S.y) :
    S.seeds.card ≤ profile 38 130 2141 4 5 S.r (S.y-S.r) (S.t-S.y) :=
  (SecondJetProfileBounds.count_96 S hI hown hL).trans (cost_le_profile S hown _ _ _ _ _ hL)

theorem count_108 (S : Data nodes u0 u1) (hI : Fintype.card I=262144)
    (hown : Own S) (hL : 2111 < S.t-S.y) :
    S.seeds.card ≤ profile 41 146 2111 4 7 S.r (S.y-S.r) (S.t-S.y) :=
  (SecondJetProfileBounds.count_108 S hI hown hL).trans (cost_le_profile S hown _ _ _ _ _ hL)

end
end ProximityPrize.SubmissionLower.SecondJetSingleCap

end Compact_SecondJetSingleCap
