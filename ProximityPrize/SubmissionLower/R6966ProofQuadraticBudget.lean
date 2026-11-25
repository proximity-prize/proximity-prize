import Mathlib.Tactic
set_option Elab.async false
namespace Research6966.QuadraticBudget
/-- Seed ceiling and physical cutoff of the recorded quadratic rescue band. -/
def band (u:ℕ) : ℕ×ℕ :=
  if u≤1 then (1,308328) else if u≤3 then (3,308232) else if u≤8 then (8,307568)
  else if u≤15 then (15,305624) else if u≤25 then (25,300794) else if u≤40 then (40,289021)
  else if u≤50 then (50,278153) else if u≤70 then (70,257143) else (92,257143)

abbrev budget:ℕ:=12000000000000000
def votes (h L:ℕ):=179769-(L-(131071-h-1))
def price (d u:ℕ):=((262144-179769)*((2*d-1)*u)+(179769-d))^2/(179769-d)^2
private def upper (u:ℕ):=((262144-179769)*((2*133570-1)*u)+179769)^2/(179769-133570)^2
def fee (u:ℕ):=3*(u+2130706433*u)

private def valid (data:ℕ×ℕ) : Prop :=
  0<votes 2499 (data.2-1) ∧ fee data.1≤budget ∧
    262144*upper data.1 ≤ (budget-fee data.1)*votes 2499 (data.2-1)

private theorem b1 : valid (1,308328) := by unfold valid; decide +kernel
private theorem b3 : valid (3,308232) := by unfold valid; decide +kernel
private theorem b8 : valid (8,307568) := by unfold valid; decide +kernel
private theorem b15 : valid (15,305624) := by unfold valid; decide +kernel
private theorem b25 : valid (25,300794) := by unfold valid; decide +kernel
private theorem b40 : valid (40,289021) := by unfold valid; decide +kernel
private theorem b50 : valid (50,278153) := by unfold valid; decide +kernel
private theorem b70 : valid (70,257143) := by unfold valid; decide +kernel
private theorem b92 : valid (92,257143) := by unfold valid; decide +kernel

private theorem receipt {u:ℕ} (sm:u≤92) : u≤(band u).1 ∧ valid (band u) := by
  unfold band
  by_cases h1:u≤1
  · simp only [ite_eq_left h1]
    exact ⟨h1,b1⟩
  by_cases h3:u≤3
  · simp only [ite_eq_right h1,ite_eq_left h3]
    exact ⟨h3,b3⟩
  by_cases h8:u≤8
  · simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_left h8]
    exact ⟨h8,b8⟩
  by_cases h15:u≤15
  · simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_right h8,ite_eq_left h15]
    exact ⟨h15,b15⟩
  by_cases h25:u≤25
  · simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_right h8,ite_eq_right h15,ite_eq_left h25]
    exact ⟨h25,b25⟩
  by_cases h40:u≤40
  · simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_right h8,ite_eq_right h15,ite_eq_right h25,ite_eq_left h40]
    exact ⟨h40,b40⟩
  by_cases h50:u≤50
  · simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_right h8,ite_eq_right h15,ite_eq_right h25,ite_eq_right h40,ite_eq_left h50]
    exact ⟨h50,b50⟩
  by_cases h70:u≤70
  · simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_right h8,ite_eq_right h15,ite_eq_right h25,ite_eq_right h40,ite_eq_right h50,ite_eq_left h70]
    exact ⟨h70,b70⟩
  simp only [ite_eq_right h1,ite_eq_right h3,ite_eq_right h8,ite_eq_right h15,ite_eq_right h25,ite_eq_right h40,ite_eq_right h50,ite_eq_right h70]
  exact ⟨sm,b92⟩

private theorem per_node {d u v:ℕ} (hd:d≤133570) (hu:u≤v) : price d u≤upper v := by
  have power:(2*d-1)*u≤(2*133570-1)*v:=Nat.mul_le_mul (by omega) hu
  have top:(262144-179769)*((2*d-1)*u)+(179769-d)≤(262144-179769)*((2*133570-1)*v)+179769 :=
    Nat.add_le_add (Nat.mul_le_mul_left _ power) (Nat.sub_le ..)
  have bottom:(179769-133570)^2≤(179769-d)^2:=Nat.pow_le_pow_left (by omega) 2
  exact (Nat.div_le_div_right (Nat.pow_le_pow_left top 2)).trans (Nat.div_le_div_left bottom (by decide))

theorem from_votes {n h width Lw d:ℕ} (hi:h≤2499) (sm:width≤92) (maxD:d≤133570)
    (low:Lw<(band width).2)
    (cnt:n*votes h Lw≤fee width*votes h Lw+262144*price d width) : n≤budget := by
  obtain ⟨uw,positive,feeFit,paid⟩:=receipt sm
  have votesFit:votes 2499 ((band width).2-1)≤votes h Lw:=by
    unfold votes;omega
  have feeBound:fee width≤fee (band width).1:=
    Nat.mul_le_mul_left 3 (Nat.add_le_add uw (Nat.mul_le_mul_left 2130706433 uw))
  have bill:262144*price d width≤(budget-fee width)*votes h Lw:=
    (Nat.mul_le_mul_left _ (per_node maxD uw)).trans
      (paid.trans (Nat.mul_le_mul (Nat.sub_le_sub_left feeBound budget) votesFit))
  have fits:fee width≤budget:=feeBound.trans feeFit
  have total:n*votes h Lw≤budget*votes h Lw:=by
    apply cnt.trans
    calc
      _ ≤ fee width*votes h Lw+(budget-fee width)*votes h Lw:=Nat.add_le_add_left bill _
      _ = _ := by rw [←Nat.add_mul,Nat.add_sub_of_le fits]
  exact Nat.le_of_mul_le_mul_right total (positive.trans_le votesFit)


#print axioms from_votes

theorem numeric {h width:ℕ} (lo:2330≤h) (hi:h≤2499) (sm:width≤92) :
    0<h ∧ h≤131070 ∧ 3*width<2130706433 ∧ 131071+h<2130706433 ∧ 131071+h<179769 ∧
    131071+h≤133570 := by omega

theorem from_family {n h width Lw d length char:ℕ} (ln:length=262144) (ch:char=2130706433)
    (hi:h≤2499) (sm:width≤92) (maxD:d≤133570) (low:Lw<(band width).2)
    (cnt:n*(179769-(Lw-(131071-h-1)))≤(3*(width+char*width))*(179769-(Lw-(131071-h-1)))+
      length*((((length-179769)*((2*d-1)*width)+(179769-d))^2)/(179769-d)^2)) : n≤budget := by
  subst length;subst char
  exact from_votes hi sm maxD low cnt
end Research6966.QuadraticBudget
