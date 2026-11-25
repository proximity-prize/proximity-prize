import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.GroupTheory.GroupAction.Basic

set_option Elab.async false

-- merged module R6960CubicOdd
section Merged_R6960CubicOdd
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Lower6960.CubicOdd
open Polynomial Finset CurvatureSquares ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators Polynomial
def disc {R : Type*} [CommRing R] (a b c d : R) : R :=
  b^2*c^2-4*a*c^3-4*b^3*d-27*a^2*d^2+18*a*b*c*d
theorem disc_at_root {R : Type*} [CommRing R] (a b c d s : R)
    (root : a*s^3+b*s^2+c*s+d=0) :
    disc a b c d=((b+a*s)^2-4*a*(c+(b+a*s)*s))*(a*s^2+(b+a*s)*s+(c+(b+a*s)*s))^2 := by
  have eq : d=-(a*s^3+b*s^2+c*s) := by linear_combination root
  rw [eq]; unfold disc; ring
variable {L : Type} [Field L]
theorem complement_degree (a b c s : (Polynomial L)) {W d : ℕ} (room : 3*d≤W)
    (sa : a.natDegree≤W-3*d) (sb : b.natDegree≤W-2*d)
    (sc : c.natDegree≤W-d) (ss : s.natDegree≤d) :
    ((b+a*s)^2-4*a*(c+(b+a*s)*s)).natDegree ≤ 2*W-4*d := by
  have q1 : (b+a*s).natDegree≤W-2*d := (natDegree_add_le ..).trans
    (max_le sb ((natDegree_mul_le ..).trans (by omega)))
  have q0 : (c+(b+a*s)*s).natDegree≤W-d := (natDegree_add_le ..).trans
    (max_le sc ((natDegree_mul_le ..).trans (by omega)))
  apply (natDegree_sub_le ..).trans (max_le ?_ ?_)
  · rw [natDegree_pow]; omega
  · have const : (4*a).natDegree ≤ a.natDegree := natDegree_C_mul_le (4:L) a
    exact (natDegree_mul_le ..).trans (by omega)
variable [DecidableEq L]
theorem cancel_squares (H G R D : (Polynomial L)) (hn : H≠0) (eqn : H^2*G=R^2*D) :
    ∃ h t : (Polynomial L), G=h^2*t ∧ t.natDegree≤D.natDegree := by
  by_cases rn : R=0
  · have z : G=0 := by simpa [rn,hn] using eqn
    exact ⟨0,0,by simp [z],by simp⟩
  let l := GCDMonoid.gcd R H
  let u := R/l
  let v := H/l
  have ln : l≠0 := gcd_ne_zero_of_right hn
  have hu : l*u=R := EuclideanDomain.mul_div_cancel' ln (gcd_dvd_left _ _)
  have hv : l*v=H := EuclideanDomain.mul_div_cancel' ln (gcd_dvd_right _ _)
  have un : u≠0 := left_div_gcd_ne_zero rn
  have red : v^2*G=u^2*D := by
    apply mul_left_cancel₀ (pow_ne_zero 2 ln)
    simpa only [←mul_assoc,←mul_pow,hu,hv] using (show (l*v)^2*G=(l*u)^2*D by rw [hu,hv]; exact eqn)
  have cop : IsCoprime u v := isCoprime_div_gcd_div_gcd hn
  obtain ⟨t,ht⟩ := (cop.pow (m:=2) (n:=2)).dvd_of_dvd_mul_left (show u^2∣v^2*G from ⟨D,red⟩)
  have dt : D=v^2*t := by
    apply mul_left_cancel₀ (pow_ne_zero 2 un)
    calc u^2*D = v^2*G := red.symm
         _ = u^2*(v^2*t) := by rw [ht]; ring
  refine ⟨u,t,ht,?_⟩
  by_cases tn : t=0
  · simp [tn]
  · have vn : v≠0 := right_div_gcd_ne_zero hn
    rw [dt,natDegree_mul (pow_ne_zero _ vn) tn]
    omega
theorem marked_corank (Q : Polynomial (Polynomial L)) {r v t : ℕ} (hr : 0<r) (deg : Q.natDegree≤r)
    (seed : ∀ i,(Q.coeff i).natDegree≤v)
    (sep : Q.resultant Q.derivative r (r-1)≠0) (T : Finset L)
    (marks : ∀ z∈T, ∃ h a : (Polynomial L), Q.map (evalRingHom z)=h^2*a ∧ a.natDegree≤t) :
    T.card*((r-t+1)/2) ≤ (2*r-1)*v := by
  have each (z) (hz : z∈T) : (r-t+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,a,eq,da⟩:=marks z hz
    have fit : (h^2*a).natDegree≤r := by rw [←eq]; exact natDegree_map_le.trans deg
    rw [←derivative_map,eq]
    exact CurvatureSquares.cofactor_corank (L:=L) (r:=r) (e:=t) h a hr da fit
  have bound:=Finset.sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at bound
  have fee:=Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed (fun i=>by
    rw [coeff_derivative,mul_comm,show ((i:(Polynomial L))+1)=C ((i:L)+1) by simp]
    exact (natDegree_C_mul_le ..).trans (seed _))
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have sum_fee : T.card*((r-t+1)/2) ≤ r*v+(r-1)*v :=
    (bound.trans upper).trans (fee.trans_eq (Nat.add_comm ..))
  calc _ ≤ _ := sum_fee
       _ = (2*r-1)*v := by rw [←Nat.add_mul]; congr 1; omega
theorem first_band (r v marks : ℕ) (large : 278868≤r)
    (count : marks*((r-278468+1)/2)≤(2*r-1)*(4*v)) : marks+4*v≤11200*v := by
  let k := (r-278468+1)/2
  have pos : 0<k := by dsimp [k]; omega
  have rate : (2*r-1)*4≤11196*k := by dsimp [k]; omega
  have cap : marks*k≤(11196*v)*k := calc
    _ ≤ (2*r-1)*(4*v) := count
    _ = ((2*r-1)*4)*v := by ring
    _ ≤ (11196*k)*v := Nat.mul_le_mul_right v rate
    _ = _ := by ring
  have := Nat.le_of_mul_le_mul_right cap pos
  omega
private abbrev sp (z : L) := Polynomial.mapRingHom (evalRingHom z)
open CurvatureSquares (root_count)
theorem high_odd_cubics (A B C₁ D H G : Polynomial (Polynomial L)) (c : (Polynomial L)) (r v : ℕ)
    (factor : disc A B C₁ D=Polynomial.C c*H^2*G)
    (large : 278868≤r) (height : G.natDegree≤r)
    (seed : ∀ j,(G.coeff j).natDegree≤4*v)
    (sep : G.resultant G.derivative r (r-1)≠0)
    (j : ℕ) (proper : (disc A B C₁ D).coeff j≠0) (price : ((disc A B C₁ D).coeff j).natDegree≤4*v)
    (degrees : A.natDegree≤406446-3*133606 ∧ B.natDegree≤406446-2*133606 ∧ C₁.natDegree≤406446-133606)
    (T : Finset L) (words : ∀ z∈T,∃ s : (Polynomial L),s.natDegree≤133606 ∧
      sp z A*s^3+sp z B*s^2+sp z C₁*s+sp z D=0) :
    T.card≤11200*v := by
  classical
  let bad := T.filter (fun z => ((disc A B C₁ D).coeff j).eval z=0)
  have ex : bad.card≤4*v := (root_count (S:=bad) (z:=id) (fun _ _ _ _ h=>h)
    ((disc A B C₁ D).coeff j) proper (fun z hz=> (mem_filter.mp hz).2)).trans price
  have marks (z) (hz : z∈T \ bad) : ∃ h t : (Polynomial L),
      G.map (evalRingHom z)=h^2*t ∧ t.natDegree≤278468 := by
    obtain ⟨mem,nb⟩:=mem_sdiff.mp hz
    obtain ⟨s,ds,root⟩:=words z mem
    have nonzero : sp z (disc A B C₁ D) ≠ 0 := by
      intro eq
      apply nb
      apply mem_filter.mpr ⟨mem,?_⟩
      change (disc A B C₁ D).map (evalRingHom z)=0 at eq
      simpa only [coeff_map,coe_evalRingHom,coeff_zero] using congrArg (fun P : (Polynomial L)=>P.coeff j) eq
    have eval_factor := congrArg (sp z) factor
    simp only [map_mul,map_pow] at eval_factor
    have scalar : sp z (Polynomial.C c) = Polynomial.C (c.eval z) := Polynomial.map_C ..
    rw [scalar] at eval_factor
    have nn := nonzero
    rw [eval_factor] at nn
    have cn : c.eval z≠0 := fun eq => nn (by simp [eq])
    have hn : sp z H≠0 := fun eq => nn (by simp [eq])
    have mapped : sp z (disc A B C₁ D)=disc (sp z A) (sp z B) (sp z C₁) (sp z D) := by simp [disc]
    rw [mapped,disc_at_root _ _ _ _ _ root] at eval_factor
    let t := (sp z B+sp z A*s)^2-4*sp z A*(sp z C₁+(sp z B+sp z A*s)*s)
    let R := sp z A*s^2+(sp z B+sp z A*s)*s+(sp z C₁+(sp z B+sp z A*s)*s)
    change t*R^2=Polynomial.C (c.eval z)*(sp z H)^2*sp z G at eval_factor
    have eq : (sp z H)^2*sp z G = R^2*(Polynomial.C (c.eval z)⁻¹*t) := by
      calc _ = (Polynomial.C (c.eval z)⁻¹*Polynomial.C (c.eval z))*((sp z H)^2*sp z G) := by
                 rw [←map_mul,inv_mul_cancel₀ cn,map_one,one_mul]
           _ = Polynomial.C (c.eval z)⁻¹*(t*R^2) := by rw [eval_factor]; ring
           _ = _ := by ring
    obtain ⟨u,e,ue,de⟩:=cancel_squares _ _ _ _ hn eq
    refine ⟨u,e,ue,de.trans ((natDegree_C_mul_le ..).trans ?_)⟩
    exact complement_degree (W:=406446) (d:=133606) _ _ _ _ (by decide)
      (natDegree_map_le.trans degrees.1) (natDegree_map_le.trans degrees.2.1)
      (natDegree_map_le.trans degrees.2.2) ds
  have paid:=first_band r v (T \ bad).card large (marked_corank G (by omega) height seed sep _ marks)
  have total := card_sdiff_add_card_eq_card (show bad⊆T from filter_subset _ _)
  omega
#print axioms high_odd_cubics
#print axioms disc_at_root
#print axioms complement_degree
#print axioms cancel_squares
#print axioms marked_corank
#print axioms first_band
end Lower6960.CubicOdd

end
end Merged_R6960CubicOdd

-- merged module R6960CubicJump
section Merged_R6960CubicJump
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Lower6960.CubicJump
open Polynomial Finset CurvatureSquares ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open scoped BigOperators Polynomial
theorem sum_losses {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) (T : Finset L) (odd : L → ℕ) {r v : ℕ}
    (hr : 0 < r) (height : Q.natDegree ≤ r) (seed : ∀ j, (Q.coeff j).natDegree ≤ v)
    (sep : Q.resultant Q.derivative r (r-1) ≠ 0)
    (fact : ∀ z ∈ T, ∃ h a : (Polynomial L), Q.map (evalRingHom z) = h^2*a ∧ a.natDegree ≤ odd z) :
    (∑ z ∈ T, (r-odd z+1)/2) ≤ (2*r-1)*v := by
  have each (z) (hz : z ∈ T) : (r-odd z+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,a,eq,da⟩ := fact z hz
    have fit : (h^2*a).natDegree ≤ r := by rw [←eq]; exact natDegree_map_le.trans height
    rw [←derivative_map,eq]
    exact CurvatureSquares.cofactor_corank (L:=L) (r:=r) (e:=odd z) h a hr da fit
  have bound := Finset.sum_le_sum each
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have fee := Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed
    (fun j => by
      rw [coeff_derivative,mul_comm,show ((j:(Polynomial L))+1)=C ((j:L)+1) by simp]
      exact (natDegree_C_mul_le ..).trans (seed _))
  calc _ ≤ _ := (bound.trans upper).trans fee
       _ = (2*r-1)*v := by rw [←Nat.add_mul]; congr 1; omega
theorem marked_price {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial (Polynomial L)) (T : Finset L) (odd jump : L → ℕ) {r q s m v : ℕ}
    (large : 812 ≤ r) (thin : 1600*q ≤ r) (ramification : 2*s ≤ r+2*q+2) (weight : m ≤ 140915)
    (height : Q.natDegree ≤ r) (seed : ∀ j, (Q.coeff j).natDegree ≤ 4*v)
    (sep : Q.resultant Q.derivative r (r-1) ≠ 0)
    (fact : ∀ z ∈ T, ∃ h a : (Polynomial L), Q.map (evalRingHom z) = h^2*a ∧ a.natDegree ≤ odd z)
    (fibre : ∀ z ∈ T, odd z ≤ 2*(jump z + (2*s)/3))
    (global : (∑ z ∈ T, jump z) ≤ (6*m+s)*v) : T.card ≤ 6495*v := by
  let losses := fun z => (r-odd z+1)/2
  have det : (∑ z ∈ T, losses z) ≤ (2*r-1)*(4*v) :=
    sum_losses Q T odd (by omega) height seed sep fact
  let debit := 3*r-4*s
  have pos : 0 < debit := by dsimp [debit]; omega
  have local_bound (z) (mem : z ∈ T) : debit ≤ 6*(jump z+losses z) := by
    have := fibre z mem
    dsimp [debit,losses]
    omega
  have total := Finset.sum_le_sum local_bound
  simp only [sum_const,nsmul_eq_mul,←Finset.mul_sum,Finset.sum_add_distrib] at total
  have rate : 6*((6*m+s)+4*(2*r-1)) ≤ 6495*debit := by dsimp [debit]; omega
  refine Nat.le_of_mul_le_mul_right ?_ pos
  calc T.card*debit ≤ 6*((∑ z ∈ T, jump z)+(∑ z ∈ T, losses z)) := total
       _ ≤ 6*((6*m+s)*v+(2*r-1)*(4*v)) := Nat.mul_le_mul_left _ (Nat.add_le_add global det)
       _ = (6*((6*m+s)+4*(2*r-1)))*v := by ring
       _ ≤ (6495*debit)*v := Nat.mul_le_mul_right v rate
       _ = _ := by ring
theorem partition (r q : ℕ) :
    8*(r+q)+5 ≤ 6500 ∨ (0<q ∧ 4*r ≤ 6477*q) ∨ (812≤r ∧ 1600*q≤r) := by omega
#print axioms partition
#print axioms sum_losses
#print axioms marked_price
end Lower6960.CubicJump

end
end Merged_R6960CubicJump

-- merged module R6960CoverBudget
section Merged_R6960CoverBudget

/-! Whole-family arithmetic for the normalized-cover paper proof. -/
namespace Lower6960.CoverBudget

def triangular (f : ℕ) := f*(f-1)/2

def rate (e : ℕ) :=
  triangular e + 2*e-1 + (8*triangular e+e+1)*(e-1)

def constantCurveRate (e f : ℕ) :=
  2*e-1 + triangular f + (9*triangular f-f+4)*(e-1)

/-- The constant-field reduction cannot exceed the displayed primitive rate
in the profile range. The table is only 45 by 24. -/
theorem table :
    ∀ e : Fin 48, 3≤e.val →
      (12*e.val≤rate e.val) ∧
      (rate e.val≤31000 ↔ e.val≤20) ∧
      ∀ f : Fin 24, 2≤f.val → 2*f.val≤e.val →
        constantCurveRate e.val f.val≤rate e.val := by decide +kernel

theorem matched_shallow_uniform :
    (rate 18)*(2400*2130706433) + 48 + 143456202788540 + 143313454876987920 ≤
      266695718139456639 := by decide +kernel

theorem grade_twenty_four :
    rate 24*(2400+2130706433*1119) + 48 + 143456202788540 + 143313454876987920 ≤
      266695718139456639 := by decide +kernel

theorem grade_twenty_five :
    266695718139456639 <
      rate 25*(2400+2130706433*1029) + 48 + 143456202788540 + 143313454876987920 := by decide +kernel

#print axioms table
#print axioms grade_twenty_four
end Lower6960.CoverBudget

end Merged_R6960CoverBudget

-- merged module R6960MarkedSheet
section Merged_R6960MarkedSheet
open scoped BigOperators
open Finset
namespace Lower6960.MarkedSheet
theorem omission {G I : Type*} [Group G] [Fintype G] [Fintype I] [MulAction G I]
    [MulAction.IsPretransitive G I] [DecidableEq I] (S : Finset I) (point : I) :
    Fintype.card I * (∑ g : G, if g • point ∉ S then 1 else 0 : ℕ) =
      Fintype.card G * (Fintype.card I - S.card) := by
  classical
  let misses (x : I) : ℕ := ∑ g : G, if g • x ∉ S then 1 else 0
  have const (x : I) : misses x = misses point := by
    obtain ⟨h,ho⟩ := MulAction.exists_smul_eq G point x
    rw [←ho]
    dsimp only [misses]
    simp_rw [←mul_smul]
    exact Equiv.sum_comp (Equiv.mulRight h) (fun g : G => if g • point ∉ S then (1:ℕ) else 0)
  have row (g : G) : (∑ x : I, if g • x ∉ S then 1 else 0 : ℕ) = Fintype.card I-S.card := by
    calc _ = ∑ x : I, if x ∉ S then (1:ℕ) else 0 :=
                Equiv.sum_comp (MulAction.toPerm g) (fun x : I => if x ∉ S then (1:ℕ) else 0)
         _ = (univ \ S).card := by
                simp only [Finset.sum_boole, Finset.sdiff_eq_filter, Nat.cast_id]
         _ = _ := by rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]; simp
  calc _ = ∑ _x : I, misses point := by simp only [sum_const,card_univ,nsmul_eq_mul]; rfl
       _ = ∑ x : I, misses x := Finset.sum_congr rfl (fun x _ => (const x).symm)
       _ = ∑ g : G, ∑ x : I, if g • x ∉ S then 1 else 0 := Finset.sum_comm
       _ = _ := by simp_rw [row]; simp
def rate (e : ℕ) := (9*e-6)*(e-1)+2*e-1
theorem good_price (labels a e n s t loss torsion image : ℕ)
    (size : 0<a) (degree : s≤n*a) (positive : 0<e)
    (marked : labels*a≤loss+torsion+e*image)
    (collisions : loss≤8*s*t) (sections : torsion+image≤n+a*t) :
    labels≤(8*n+e)*t+e*n := by
  have h1 : 8*s*t≤8*(n*a)*t := Nat.mul_le_mul_right t (Nat.mul_le_mul_left 8 degree)
  have h2 : torsion+e*image≤e*(n+a*t) := calc
    _ ≤ e*torsion+e*image := Nat.add_le_add_right (Nat.le_mul_of_pos_left _ positive) _
    _ = e*(torsion+image) := (Nat.mul_add ..).symm
    _ ≤ _ := Nat.mul_le_mul_left e sections
  refine Nat.le_of_mul_le_mul_right ?_ size
  calc labels*a ≤ loss+(torsion+e*image) := by simpa only [Nat.add_assoc] using marked
       _ ≤ 8*(n*a)*t+e*(n+a*t) := Nat.add_le_add (collisions.trans h1) h2
       _ = ((8*n+e)*t)*a+e*n := by ring
       _ ≤ ((8*n+e)*t)*a+(e*n)*a := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ size) _
       _ = _ := (Nat.add_mul ..).symm
theorem endpoint :
    rate 47 = 19275 ∧
    (∀ e : Fin 48, 3≤e.val → 12*e.val≤rate e.val ∧ rate e.val≤rate 47) ∧
    143313454876987920 + 143456202788540 + (rate 47)*(2400*2130706433) +
      47*46 + 48 < 266695718139456639 := by decide +kernel
#print axioms omission
#print axioms good_price
#print axioms endpoint
private def paidOrder : Array ℕ := #[0,1167,1162,1157,1152,1147,1142,1137,1132,1126,1121,1115,1110,1104,1099,1093,1087,1081,1075,1069,1063,1056,1050,1043,1037,1030,1023,1015,1008,1000,993,984,976,967,958,949,939,928,917,905,891,874,835,757,649,516,362,189,0]
theorem graded_endpoint :
    (∀ e : Fin 48, 3≤e.val →
      rate e.val * (2130706433+1) * (paidOrder[e.val]!-1) + e.val*(e.val-1) ≤
        27250435559936982) ∧
    rate 42 * (2130706433+1) * (paidOrder[42]!-1) + 42*41 = 27250435559936982 ∧
    95520157607632002 + 143314245927361932 + 143456202788540 + 48 +
      27250435559936982 = 266228295297719504 := by decide +kernel
#print axioms graded_endpoint
end Lower6960.MarkedSheet

end Merged_R6960MarkedSheet
