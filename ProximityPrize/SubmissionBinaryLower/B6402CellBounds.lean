import ProximityPrize.SubmissionBinaryLower.B6402EndpointBudget
import ProximityPrize.SubmissionBinaryLower.B6402HardBin

/-! Pass from the certified real profile interval to the integer load,
residual weight, gap and seed-degree premises at the actual factor. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402CellBounds
open B6401Params hiding A
open B6402HybridP64 (A)
open B6402EndpointBudget
set_option autoImplicit false
set_option maxHeartbeats 1200000

structure Side where
  least : ℕ
  mostBad : ℕ
  gap0 : ℕ
  delta : ℕ
  spatial : ℕ
  ordinate : ℕ
deriving Repr

def valid (p : Plan) (v : Side) : Bool :=
  decide (1≤p.s ∧ p.b<p.m ∧ 2≤p.J ∧ 2*p.m≤p.J+p.s ∧ p.W/(wY-1)≤p.J ∧
    p.W<2*((p.m-p.b)*A+p.b*v.least) ∧
    p.W+p.s*(p.WFhi-(wY-1))≤v.spatial+2*p.b*(v.least-v.mostBad) ∧
    v.spatial/wY≤v.ordinate ∧ v.gap0+2*p.b*v.mostBad≤v.delta ∧
    (p.s+1)*(1811+p.q)+p.q*max (p.J+1) (p.s+2*p.m)≤p.cap ∧ p.J+4*p.s≤51897)

theorem from_cell (p : Plan) (v : Side) (ok : valid p v=true) (sites good bad WF H : ℕ)
    (least : v.least≤sites) (most : bad≤v.mostBad) (split : good+bad=sites)
    (fw : WF≤p.WFhi) (height : H≤1811+p.q) :
    let T := p.cap-p.s*H
    1≤p.s ∧ p.b≤p.m ∧ 2≤p.J ∧ 2*p.m≤p.J+p.s ∧ p.W/(wY-1)≤p.J ∧
    p.W<2*((p.m-p.b)*A+p.b*sites) ∧
    p.W+p.s*(WF-(wY-1))≤v.spatial+2*p.b*good ∧
    v.spatial/wY≤v.ordinate ∧ v.gap0+2*p.b*bad≤v.delta ∧
    H≤T ∧ T+p.s*H=p.cap ∧ p.q*(p.W/(wY-1))≤T-H+1 ∧ p.q*(p.s+2*p.m)≤T-H+1 ∧ p.J+4*p.s≤51897 := by
  intro T
  simp only [valid,decide_eq_true_eq] at ok
  obtain ⟨s1,bm,j2,mj,wj,load,weight,yo,gap,budget,scalar⟩ := ok
  have hp := Nat.mul_le_mul_left p.b least
  have hg := Nat.mul_le_mul_left (2*p.b) (show v.least-v.mostBad≤good by omega)
  have hw := Nat.mul_le_mul_left p.s (Nat.sub_le_sub_right fw (wY-1))
  have hb := Nat.mul_le_mul_left (2*p.b) most
  have h1 := Nat.mul_le_mul_left (p.s+1) height
  simp only [Nat.add_mul,Nat.one_mul] at h1 budget
  have capG := Nat.mul_le_mul_left p.q (le_trans (a:=p.W/(wY-1)) (by omega : p.W/(wY-1)≤p.J+1) (le_max_left _ (p.s+2*p.m)))
  have capL := Nat.mul_le_mul_left p.q (le_max_right (p.J+1) (p.s+2*p.m))
  dsimp [T]
  exact ⟨s1,bm.le,j2,mj,wj,by omega,by omega,yo,by omega,by omega,by omega,by omega,by omega,scalar⟩

theorem round_profile (lo hi c : ℚ) (n l b h wf : ℕ)
    (p2 : lo≤(n:ℚ)/N) (bad : (b:ℚ)/N≤hi) (cw : (wf:ℚ)/wY≤c)
    (ceilLo : (l:ℚ)-1<lo*N) (floorHi : hi*N<(h:ℚ)+1)
    (WFhi : ℕ) (ceilWF : c*wY≤WFhi) : l≤n ∧ b≤h ∧ wf≤WFhi := by
  have hn : (0:ℚ)<N := by decide
  have hw : (0:ℚ)<wY := by decide
  have z1 := (le_div_iff₀ hn).mp p2
  have z2 := (div_le_iff₀ hn).mp bad
  have z3 := (div_le_iff₀ hw).mp cw
  have a : (l:ℤ)-1<n := by exact_mod_cast ceilLo.trans_le z1
  have b' : (b:ℤ)<(h:ℤ)+1 := by exact_mod_cast z2.trans_lt floorHi
  have c' : wf≤WFhi := by exact_mod_cast z3.trans ceilWF
  omega

#print axioms from_cell
#print axioms round_profile
end ProximityPrize.SubmissionBinaryLower.B6402CellBounds
