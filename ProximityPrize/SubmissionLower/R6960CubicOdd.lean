import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.RingTheory.EuclideanDomain

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

theorem complement_degree (a b c s : L[X]) {W d : ℕ} (room : 3*d≤W)
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

/-- Removing a generic square from a discriminant preserves the specialized
bound on the degree outside its square part. The two squares can share roots. -/
theorem cancel_squares (H G R D : L[X]) (hn : H≠0) (eqn : H^2*G=R^2*D) :
    ∃ h t : L[X], G=h^2*t ∧ t.natDegree≤D.natDegree := by
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

/-- A specialization count with residual degree t. Simultaneous degree
loss and repeated roots both contribute to the rank defect. -/
theorem marked_corank (Q : Polynomial L[X]) {r v t : ℕ} (hr : 0<r) (deg : Q.natDegree≤r)
    (seed : ∀ i,(Q.coeff i).natDegree≤v)
    (sep : Q.resultant Q.derivative r (r-1)≠0) (T : Finset L)
    (marks : ∀ z∈T, ∃ h a : L[X], Q.map (evalRingHom z)=h^2*a ∧ a.natDegree≤t) :
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
    rw [coeff_derivative,mul_comm,show ((i:L[X])+1)=C ((i:L)+1) by simp]
    exact (natDegree_C_mul_le ..).trans (seed _))
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have sum_fee : T.card*((r-t+1)/2) ≤ r*v+(r-1)*v :=
    (bound.trans upper).trans (fee.trans_eq (Nat.add_comm ..))
  calc _ ≤ _ := sum_fee
       _ = (2*r-1)*v := by rw [←Nat.add_mul]; congr 1; omega

/-- First high band. The separate parameter-content charge is at most 4v. -/
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

open private root_count from ProximityPrize.SubmissionLower.R6960QuadraticProjection

/-- Count a scalar family from its discriminant, including parameter-content
zeros, abscissa degree drops and nonmonic cubic fibres. -/
theorem high_odd_cubics (A B C₁ D H G : Polynomial L[X]) (c : L[X]) (r v : ℕ)
    (factor : disc A B C₁ D=Polynomial.C c*H^2*G)
    (large : 278868≤r) (height : G.natDegree≤r)
    (seed : ∀ j,(G.coeff j).natDegree≤4*v)
    (sep : G.resultant G.derivative r (r-1)≠0)
    (j : ℕ) (proper : (disc A B C₁ D).coeff j≠0) (price : ((disc A B C₁ D).coeff j).natDegree≤4*v)
    (degrees : A.natDegree≤406446-3*133606 ∧ B.natDegree≤406446-2*133606 ∧ C₁.natDegree≤406446-133606)
    (T : Finset L) (words : ∀ z∈T,∃ s : L[X],s.natDegree≤133606 ∧
      sp z A*s^3+sp z B*s^2+sp z C₁*s+sp z D=0) :
    T.card≤11200*v := by
  classical
  let bad := T.filter (fun z => ((disc A B C₁ D).coeff j).eval z=0)
  have ex : bad.card≤4*v := (root_count (S:=bad) (z:=id) (fun _ _ _ _ h=>h)
    ((disc A B C₁ D).coeff j) proper (fun z hz=> (mem_filter.mp hz).2)).trans price
  have marks (z) (hz : z∈T \ bad) : ∃ h t : L[X],
      G.map (evalRingHom z)=h^2*t ∧ t.natDegree≤278468 := by
    obtain ⟨mem,nb⟩:=mem_sdiff.mp hz
    obtain ⟨s,ds,root⟩:=words z mem
    have nonzero : sp z (disc A B C₁ D) ≠ 0 := by
      intro eq
      apply nb
      apply mem_filter.mpr ⟨mem,?_⟩
      change (disc A B C₁ D).map (evalRingHom z)=0 at eq
      simpa only [coeff_map,coe_evalRingHom,coeff_zero] using congrArg (fun P : L[X]=>P.coeff j) eq
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
