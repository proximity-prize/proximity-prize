import ProximityPrize.Benchmark.TargetLower

section Merged6967_R6966ProofProtocolProfile
set_option Elab.async false



set_option Elab.async false

namespace Research6966.ProtocolProfile
open ProximityPrize.Benchmark ToyProblem CoreDefinitions ProximityGap
open scoped NNReal
abbrev p : ℕ := 164771
abbrev q : ℕ := 524288
abbrev agreement : ℕ := 179759
abbrev listCap : ℕ := 51967810913705
abbrev scalarCap : ℕ := 274928760300481382

private theorem of_cross_power {x : ℝ≥0} {a d : ℕ} (hd : 0 < d)
    (h : x ^ d * 2 ^ a ≤ 1) : x ≤ (2 : ℝ≥0) ^ (-(a : ℝ) / d) := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  apply (NNReal.rpow_le_rpow_iff hd').mp
  rw [← NNReal.rpow_mul, div_mul_cancel₀ _ hd'.ne', NNReal.rpow_natCast,
    NNReal.rpow_neg, NNReal.rpow_natCast, ← one_div]
  exact (le_div_iff₀ (by positivity)).mpr h
theorem score :
    (1 - claimedRadius p q) ^ IRSProfile.repetitions ≤ (2 : ℝ≥0) ^ (-((6967 : ℝ) / 100)) := by
  let x : ℝ≥0 := (1 - claimedRadius p q) ^ 128
  have small : claimedRadius p q ≤ 1 := by
    unfold claimedRadius
    exact (div_le_one (by positivity)).mpr (by norm_num)
  have diff : 1 - claimedRadius p q = (359517 : ℝ≥0) / q := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub small]
    norm_num [claimedRadius]
  have upper : x * 2 ^ 69 ≤ (628358403722 : ℝ≥0) / 1000000000000 := by
    dsimp only [x]
    rw [diff, div_pow, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (359517 : ℕ) ^ 128 * 2 ^ 69 * 1000000000000 ≤
      628358403722 * q ^ 128 by decide +kernel)
  change x ≤ _
  rw [← neg_div]
  apply of_cross_power (a := 6967) (d := 100) (by decide)
  calc
    x ^ 100 * 2 ^ 6967 = (x * 2 ^ 69) ^ 100 * 2 ^ 67 := by
      rw [mul_pow, mul_assoc, ← pow_mul (2 : ℝ≥0), ← pow_add]
    _ ≤ ((628358403722 : ℝ≥0) / 1000000000000) ^ 100 * 2 ^ 67 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left' upper _) (by positivity)
    _ ≤ 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
      exact_mod_cast (show (628358403722 : ℕ) ^ 100 * 2 ^ 67 ≤ 1000000000000 ^ 100 by decide +kernel)

theorem admissible : claimedRadius p q ∈ Set.Ioo (0:ℝ≥0) IRSProfile.minRelativeDistance := by
  constructor <;> norm_num [claimedRadius,IRSProfile.minRelativeDistance]

theorem threshold {s:ℕ} (h:(262144:ℝ)*(1-((claimedRadius p q:ℝ≥0):ℝ))≤s) : agreement≤s := by
  have strict:(179758:ℝ)<262144*(1-((claimedRadius p q:ℝ≥0):ℝ)) := by norm_num [claimedRadius]
  exact (show 179758<s by exact_mod_cast strict.trans_le h)

theorem field_budget : (scalarCap+listCap)*2^128≤(0x7f000001:ℕ)^6 := by decide +kernel
theorem reduced : Nat.Coprime p q := by decide +kernel
#print axioms score
#print axioms threshold
end Research6966.ProtocolProfile

end Merged6967_R6966ProofProtocolProfile

section Merged6967_R6966ProofQuadraticBudget
set_option Elab.async false

set_option Elab.async false
namespace Research6966.QuadraticBudget
/-- Seed ceiling and physical cutoff of the recorded quadratic rescue band. -/
def band (u:ℕ) : ℕ×ℕ :=
  if u≤1 then (1,308303) else if u≤3 then (3,308232) else if u≤8 then (8,307568)
  else if u≤15 then (15,305624) else if u≤25 then (25,300794) else if u≤40 then (40,289021)
  else if u≤50 then (50,278153) else if u≤70 then (70,257143) else (92,257143)

abbrev budget:ℕ:=12000000000000000
def votes (h L:ℕ):=179759-(L-(131071-h-1))
def price (d u:ℕ):=((262144-179759)*((2*d-1)*u)+(179759-d))^2/(179759-d)^2
private def upper (u:ℕ):=((262144-179759)*((2*133593-1)*u)+179759)^2/(179759-133593)^2
def fee (u:ℕ):=3*(u+2130706433*u)

private def valid (data:ℕ×ℕ) : Prop :=
  0<votes 2522 (data.2-1) ∧ fee data.1≤budget ∧
    262144*upper data.1 ≤ (budget-fee data.1)*votes 2522 (data.2-1)

private theorem b1 : valid (1,308303) := by unfold valid; decide +kernel
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

private theorem per_node {d u v:ℕ} (hd:d≤133593) (hu:u≤v) : price d u≤upper v := by
  have power:(2*d-1)*u≤(2*133593-1)*v:=Nat.mul_le_mul (by omega) hu
  have top:(262144-179759)*((2*d-1)*u)+(179759-d)≤(262144-179759)*((2*133593-1)*v)+179759 :=
    Nat.add_le_add (Nat.mul_le_mul_left _ power) (Nat.sub_le ..)
  have bottom:(179759-133593)^2≤(179759-d)^2:=Nat.pow_le_pow_left (by omega) 2
  exact (Nat.div_le_div_right (Nat.pow_le_pow_left top 2)).trans (Nat.div_le_div_left bottom (by decide))

theorem from_votes {n h width Lw d:ℕ} (hi:h≤2522) (sm:width≤92) (maxD:d≤133593)
    (low:Lw<(band width).2)
    (cnt:n*votes h Lw≤fee width*votes h Lw+262144*price d width) : n≤budget := by
  obtain ⟨uw,positive,feeFit,paid⟩:=receipt sm
  have votesFit:votes 2522 ((band width).2-1)≤votes h Lw:=by
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

theorem numeric {h width:ℕ} (lo:2317≤h) (hi:h≤2522) (sm:width≤92) :
    0<h ∧ h≤131070 ∧ 3*width<2130706433 ∧ 131071+h<2130706433 ∧ 131071+h<179759 ∧
    131071+h≤133593 := by omega

theorem from_family {n h width Lw d length char:ℕ} (ln:length=262144) (ch:char=2130706433)
    (hi:h≤2522) (sm:width≤92) (maxD:d≤133593) (low:Lw<(band width).2)
    (cnt:n*(179759-(Lw-(131071-h-1)))≤(3*(width+char*width))*(179759-(Lw-(131071-h-1)))+
      length*((((length-179759)*((2*d-1)*width)+(179759-d))^2)/(179759-d)^2)) : n≤budget := by
  subst length;subst char
  exact from_votes hi sm maxD low cnt
end Research6966.QuadraticBudget

end Merged6967_R6966ProofQuadraticBudget

section Merged6967_R6966ProofQuadraticWeight
set_option Elab.async false





set_option Elab.async false

namespace Research6966.QuadraticWeight
open Polynomial
open scoped Polynomial Differential
noncomputable section

/-- The cleared numerator for the (j+1)st derivative of an ODE solution. -/
def numerator {R : Type*} [CommRing R] [Differential R] (A B : R[X]) :
    ℕ → R[X]
  | 0 => B
  | j+1 =>
    let Q := numerator A B j
    let v := fun F : R[X] => A * Differential.mapCoeffs F + B * F.derivative
    A * v Q - ((2*j+1:ℕ):R[X]) * Q * v A

private theorem power_rule {S : Type*} [CommRing S] [Differential S] (a:S) (n:ℕ) :
    a * Differential.deriv (a^n) = n * a^n * Differential.deriv a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Differential.deriv.leibniz,Nat.cast_succ]
    simp only [smul_eq_mul] at *
    linear_combination a*ih

/-- Differential identity before specialization at a physical coordinate.
No divisions, including by a possibly vanishing separant, are performed. -/
theorem cleared {R S : Type*} [CommRing R] [Differential R] [CommRing S] [Differential S]
    [Algebra R S] [DifferentialAlgebra R S] (A B : R[X]) (y:S)
    (law : aeval y A * Differential.deriv y = aeval y B) (j:ℕ) :
    (aeval y A)^(2*j+1) * Differential.deriv^[j+1] y = aeval y (numerator A B j) := by
  let a := aeval y A
  let v (F : R[X]) := A*Differential.mapCoeffs F+B*F.derivative
  have chain (F:R[X]) : a*Differential.deriv (aeval y F) = aeval y (v F) := by
    rw [Differential.deriv_aeval_eq]
    dsimp [a,v]
    simp only [map_add,map_mul]
    linear_combination (aeval y F.derivative)*law
  induction j with
  | zero => simpa [numerator] using law
  | succ j ih =>
    let q := numerator A B j
    let z := Differential.deriv^[j+1] y
    let k := 2*j+1
    change a^k*z=aeval y q at ih
    have diff := congrArg (fun t:S => Differential.deriv t) ih
    simp only [Differential.deriv.leibniz,smul_eq_mul] at diff
    have target : 2*(j+1)+1=k+2 := by dsimp [k];omega
    rw [target, pow_add,Function.iterate_succ_apply' (n:=j+1),numerator]
    change a^k*a^2*Differential.deriv z=aeval y (A*v q-(k:R[X])*q*v A)
    simp only [map_sub,map_mul,map_natCast]
    change a^k*a^2*Differential.deriv z=a*aeval y (v q)-(k:S)*aeval y q*aeval y (v A)
    linear_combination a^2*diff + a*chain q - a*z*power_rule a k
      - (k:S)*z*a^k*chain A - (k:S)*aeval y (v A)*ih

/-- A word whose raw separant is nonzero has at most its physical degree
many singular agreements, irrespective of how many received nodes are base points. -/
theorem regular_hits {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (nodes:I→F) (distinct:Function.Injective nodes) (T:Finset I)
    (separant:F[X]) (nz:separant≠0) :
    T.card ≤ (T.filter (fun i => separant.eval (nodes i) ≠ 0)).card + separant.natDegree := by
  let bad:=T.filter (fun i=>separant.eval (nodes i)=0)
  have sub : bad.image nodes ⊆ separant.roots.toFinset := by
    intro x hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (Finset.mem_filter.mp hi).2)
  have bound : bad.card ≤ separant.natDegree := by
    rw [←Finset.card_image_of_injective bad distinct]
    exact (Finset.card_le_card sub).trans
      ((Multiset.toFinset_card_le _).trans (card_roots' _))
  have split:=T.card_filter_add_card_filter_not (fun i=>separant.eval (nodes i)=0)
  change (T.filter (fun i=>separant.eval (nodes i)=0)).card ≤ _ at bound
  rw [← split, Nat.add_comm (T.filter (fun i=>separant.eval (nodes i)=0)).card]
  exact Nat.add_le_add_left bound _

#print axioms cleared
#print axioms regular_hits

/-- Applying the raw slope coefficient to a degree-w word charges just its
physical weight after removing the slope-variable weight. Zero coefficients
are allowed even if the budget contains no slot of their nominal weight. -/
theorem regular_hits_of_raw_line {F I : Type*} [Field F] [DecidableEq F] [DecidableEq I]
    (nodes:I→F) (distinct:Function.Injective nodes) (T:Finset I) (a b R:F[X]) (w cap:ℕ)
    (word:R.natDegree≤w) (hw:a=0 ∨ a.natDegree+w≤cap)
    (constant:b.natDegree≤cap) (nz:a*R+b≠0) :
    T.card ≤ (T.filter (fun i=>(a*R+b).eval (nodes i)≠0)).card + cap := by
  apply (regular_hits nodes distinct T _ nz).trans
  apply Nat.add_le_add_left
  apply (natDegree_add_le ..).trans
  apply max_le _ constant
  rcases hw with rfl|bound
  · simp
  · exact (natDegree_mul_le ..).trans ((Nat.add_le_add_left word _).trans bound)

/-- The determinant used to charge the identically singular words, valid
even at labels where the leading ordinate coefficient drops. -/
theorem exceptional_determinant {R : Type*} [CommRing R] (a c b₂ b₁ b₀ y:R)
    (singular:a*y+c=0) (root:b₂*y^2+b₁*y+b₀=0) :
    a^2*b₀-a*c*b₁+c^2*b₂=0 := by
  linear_combination a^2*root - (a*b₂*y+a*b₁-c*b₂)*singular

#print axioms regular_hits_of_raw_line
#print axioms exceptional_determinant

section SeedDegrees
variable {σ k : Type*} [CommRing k] [Nontrivial k]
abbrev Seeds := MvPolynomial σ k
private abbrev Row := (Seeds (σ:=σ) (k:=k))[X]
private def Bounded (Q : Row (σ:=σ) (k:=k)) (u:ℕ) := ∀ i, (Q.coeff i).totalDegree ≤ u

private theorem bound_add {F G : Row (σ:=σ) (k:=k)} {u : ℕ}
    (hf:Bounded F u) (hg:Bounded G u) : Bounded (F+G) u := by
  intro i
  rw [coeff_add]
  exact (MvPolynomial.totalDegree_add ..).trans (max_le (hf i) (hg i))

private theorem bound_sub {F G : Row (σ:=σ) (k:=k)} {u : ℕ}
    (hf:Bounded F u) (hg:Bounded G u) : Bounded (F-G) u := by
  intro i
  rw [coeff_sub]
  exact (MvPolynomial.totalDegree_sub ..).trans (max_le (hf i) (hg i))

private theorem bound_mul {F G : Row (σ:=σ) (k:=k)} {u v : ℕ}
    (hf:Bounded F u) (hg:Bounded G v) : Bounded (F*G) (u+v) := by
  intro i
  rw [coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij _
  exact (MvPolynomial.totalDegree_mul ..).trans (Nat.add_le_add (hf ij.1) (hg ij.2))

private theorem cast_degree (n:ℕ) : (n:Seeds (σ:=σ) (k:=k)).totalDegree=0 := by
  rw [← map_natCast (MvPolynomial.C : k →+* Seeds) n,MvPolynomial.totalDegree_C]

private theorem bound_dy {F : Row (σ:=σ) (k:=k)} {u:ℕ} (hf:Bounded F u) :
    Bounded F.derivative u := by
  intro i
  rw [coeff_derivative,← Nat.cast_succ]
  apply (MvPolynomial.totalDegree_mul ..).trans
  rw [cast_degree,Nat.add_zero]
  exact hf (i+1)

private theorem bound_const_mul (n:ℕ) {F : Row (σ:=σ) (k:=k)} {u:ℕ} (hf:Bounded F u) :
    Bounded ((n:Row)*F) u := by
  intro i
  rw [← map_natCast (C : Seeds →+* Row) n,coeff_C_mul]
  exact (MvPolynomial.totalDegree_mul ..).trans (by simpa [cast_degree] using hf i)

variable [Differential (Seeds (σ:=σ) (k:=k))]

/-- Degrees of all ordinate coefficients in the actual rational ODE numerator.
Physical coefficient differentiation fixes the two seeds. -/
theorem coefficient_degree (A B : Row (σ:=σ) (k:=k)) (u : ℕ)
    (dx:∀ f:Seeds (σ:=σ) (k:=k), (Differential.deriv f).totalDegree ≤ f.totalDegree)
    (ha:∀ i,(A.coeff i).totalDegree≤u) (hb:∀ i,(B.coeff i).totalDegree≤u)
    (j i:ℕ) : ((numerator A B j).coeff i).totalDegree≤(2*j+1)*u := by
  have direction {F : Row (σ:=σ) (k:=k)} {v:ℕ} (hf:Bounded F v) :
      Bounded (A*Differential.mapCoeffs F+B*F.derivative) (u+v) := by
    apply bound_add
    · apply bound_mul ha
      intro n
      simpa only [Differential.coeff_mapCoeffs] using (dx (F.coeff n)).trans (hf n)
    · exact bound_mul hb (bound_dy hf)
  suffices h:Bounded (numerator A B j) ((2*j+1)*u) from h i
  induction j with
  | zero => simpa [numerator,Bounded] using hb
  | succ j ih =>
    rw [numerator]
    apply bound_sub
    · convert bound_mul ha (direction ih) using 1
      ring
    · convert bound_mul (bound_const_mul (2*j+1) ih) (direction ha) using 1
      ring

#print axioms coefficient_degree
end SeedDegrees
end
end Research6966.QuadraticWeight

end Merged6967_R6966ProofQuadraticWeight

section Merged6967_R6966ProofTerminalProjection
set_option Elab.async false





set_option Elab.async false

namespace Research6966.TerminalProjection
open Polynomial
open scoped Polynomial
noncomputable section

/-- Restrict a slope polynomial to A V = B, clearing the same denominator
for every coefficient. The index is the bank's slope cap. -/
def cleared {R : Type*} [CommRing R] (A B : R) (Q : R[X]) (J : ℕ) : R :=
  Q.sum (fun j c => c * B^j * A^(J-j))

theorem map_cleared {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B:R) (v:S) (hv:f A*v=f B) (Q:R[X]) (J:ℕ) (bound:Q.natDegree≤J) :
    f (cleared A B Q J) = (f A)^J * Q.eval₂ f v := by
  rw [cleared,Polynomial.sum_def,map_sum,eval₂_eq_sum,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have le: i≤J := (le_natDegree_of_mem_supp i hi).trans bound
  rw [map_mul,map_mul,map_pow,map_pow,←hv,mul_pow]
  have full : (f A)^i*(f A)^(J-i)=(f A)^J := by rw [←pow_add];congr 1;omega
  linear_combination (f (Q.coeff i))*v^i*full

variable {K:Type*} [Field K]
private abbrev R := K[X]

/-- Avoiding the primitive graph makes the cleared projection nonzero. -/
theorem integral_nonzero_of_avoids {S:Type*} [CommRing S] [IsDomain S] [NormalizedGCDMonoid S]
    (A B:S) (Q:S[X]) (J:ℕ)
    (cap:Q.natDegree≤J) (nz:A≠0) (prim:(C A*«X»-C B).IsPrimitive)
    (avoid:¬ C A*«X»-C B ∣ Q) : cleared A B Q J ≠ 0 := by
  let F:=FractionRing S
  let f:=algebraMap S F
  have an : f A≠0 := (map_ne_zero_iff _ (IsFractionRing.injective _ F)).mpr nz
  let v:=f B/f A
  have av:f A*v=f B := by dsimp [v];field_simp
  intro z
  have eq:=map_cleared f A B v av Q J cap
  rw [z,map_zero] at eq
  have root : IsRoot (Q.map f) v := by
    rw [IsRoot,eval_map]
    exact (mul_eq_zero.mp eq.symm).resolve_left (pow_ne_zero _ an)
  obtain ⟨H,fac⟩ := dvd_iff_isRoot.mpr root
  apply avoid
  apply prim.dvd_of_fraction_map_dvd_fraction_map (K:=F)
  refine ⟨C (f A)⁻¹ * H,?_⟩
  rw [fac,Polynomial.map_sub,Polynomial.map_mul,map_C,map_X,map_C]
  have one : C (f A) * C (f A)⁻¹ = (1:F[X]) := by rw [←C_mul,mul_inv_cancel₀ an,C_1]
  have point : C (f B)*C (f A)⁻¹ = (C v:F[X]) := by rw [←C_mul];rfl
  linear_combination -(«X»*H)*one + H*point

theorem nonzero_of_avoids (A B:K[X]) (Q:K[X][X]) (J:ℕ)
    (cap:Q.natDegree≤J) (nz:A≠0) (prim:(C A*«X»-C B).IsPrimitive)
    (avoid:¬ C A*«X»-C B ∣ Q) : cleared A B Q J ≠ 0 := by
  classical
  exact integral_nonzero_of_avoids A B Q J cap nz prim avoid

def fibrePoint (y v:K) : Ideal K[X][X] :=
  Ideal.span {C («X»-C y), «X»-C (C v)}

/-- Restriction along the graph preserves every order at a smooth graph
point. The quotient modulo (X-y)^k handles all powers at once. -/
theorem restriction_order (A B:K[X]) (Q:K[X][X]) (y v:K) (J k:ℕ)
    (cap:Q.natDegree≤J) (regular:A.eval y≠0) (onGraph:A.eval y*v=B.eval y)
    (order:Q∈(fibrePoint y v)^k) : («X»-C y)^k ∣ cleared A B Q J := by
  classical
  cases k with
  | zero => simp
  | succ k =>
    let p:K[X]:=«X»-C y
    have atY : p ∣ A-C (A.eval y) := by apply dvd_iff_isRoot.mpr; simp [IsRoot]
    obtain ⟨d,hd⟩:=atY
    have cop : IsCoprime A p := by
      refine ⟨C (A.eval y)⁻¹,-C (A.eval y)⁻¹*d,?_⟩
      have inv : C (A.eval y)⁻¹*C (A.eval y)=(1:K[X]) := by rw [←C_mul,inv_mul_cancel₀ regular,C_1]
      linear_combination C (A.eval y)⁻¹*hd + inv
    obtain ⟨c,b,bez⟩:=cop.pow_right (n:=k+1)
    let W:=c*B
    have value : W.eval y=v := by
      have H:=congrArg (eval y) bez
      simp [p] at H
      dsimp [W];rw [eval_mul,←onGraph,←mul_assoc,H,one_mul]
    let ev:=evalRingHom W
    have mapped : (fibrePoint y v).map ev ≤ Ideal.span {p} := by
      apply Ideal.map_le_iff_le_comap.mpr
      apply Ideal.span_le.mpr
      intro F hF
      rcases hF with hF|hF
      · subst F;simp [ev,p]
      · have F_eq:F=«X»-C (C v):=Set.mem_singleton_iff.mp hF
        subst F;change («X»-C (C v)).eval W∈Ideal.span {p}
        rw [eval_sub,eval_X,eval_C,Ideal.mem_span_singleton]
        apply dvd_iff_isRoot.mpr;simp [IsRoot,value]
    have orderW : Q.eval W ∈ Ideal.span {p^(k+1)} := by
      have h:=Ideal.mem_map_of_mem ev order
      rw [Ideal.map_pow] at h
      rw [← Ideal.span_singleton_pow]
      have incl : ((fibrePoint y v).map ev)^(k+1) ≤ (Ideal.span {p})^(k+1) := by gcongr
      exact incl h
    let I:Ideal K[X]:=Ideal.span {p^(k+1)}
    let f:=Ideal.Quotient.mk I
    have dead:f (p^(k+1))=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    have active : f A*f W=f B := by
      have H:=congrArg f bez
      simp only [map_add,map_mul,dead,mul_zero,add_zero,map_one] at H
      dsimp only [W];rw [map_mul]
      linear_combination f B*H
    have res:=map_cleared f A B (f W) active Q J cap
    have compat : f (Q.eval W)=Q.eval₂ f (f W) := by
      simp
    rw [←compat] at res
    have wz:f (Q.eval W)=0:=Ideal.Quotient.eq_zero_iff_mem.mpr orderW
    rw [wz,mul_zero] at res
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp res)

#print axioms map_cleared
#print axioms nonzero_of_avoids
#print axioms restriction_order

/-- One avoiding row bounds the entire on-graph ordinate product, including
its order. A different row is allowed for each seed axis. -/
theorem all_sheets (A B : K[X]) (Q : K[X][X]) (ys : Finset K) (v : K → K) (J k : ℕ)
    (cap : Q.natDegree ≤ J)
    (sheets : ∀ y ∈ ys, A.eval y ≠ 0 ∧ A.eval y*v y = B.eval y ∧
      Q ∈ (fibrePoint y (v y))^k) :
    (∏ y ∈ ys, («X»-C y : K[X]))^k ∣ cleared A B Q J := by
  classical
  rw [← Finset.prod_pow]
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj h
    exact ((isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit).pow_left).pow_right
  · intro y hy
    obtain ⟨reg,onG,van⟩ := sheets y hy
    exact restriction_order A B Q _ _ _ _ cap reg onG van

/-- Projection width in either seed, viewing the other variables as
coefficients. Physical differentiation is not needed for this estimate. -/
theorem seed_width (A B : K[X]) (Q : K[X][X]) (J u U : ℕ)
    (cap : Q.natDegree ≤ J) (a : A.natDegree ≤ u) (b : B.natDegree ≤ u)
    (coeff : ∀ i ∈ Q.support, (Q.coeff i).natDegree ≤ U) :
    (cleared A B Q J).natDegree ≤ U+J*u := by
  rw [cleared, Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have ij := (le_natDegree_of_mem_supp i hi).trans cap
  calc
    _ ≤ ((Q.coeff i).natDegree+i*u)+(J-i)*u := by
      apply natDegree_mul_le.trans;apply Nat.add_le_add
      · apply natDegree_mul_le.trans
        exact Nat.add_le_add_left (natDegree_pow_le.trans (Nat.mul_le_mul_left i b)) _
      · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ a)
    _ ≤ U+J*u := by
      rw [Nat.add_assoc,←Nat.add_mul, Nat.add_sub_of_le ij]
      exact Nat.add_le_add_right (coeff i hi) _

/-- A total-jet cap B₀ saves one ordinate degree per slope exponent. -/
theorem ordinate_width {F:Type*} [CommRing F] [Nontrivial F] (A B : F[X]) (Q : F[X][X]) (J a B₀ : ℕ)
    (cap : Q.natDegree ≤ J) (positive : 0<a)
    (degA : A.natDegree ≤ a-1) (degB : B.natDegree ≤ a)
    (coeff : ∀ i ∈ Q.support, (Q.coeff i).natDegree+i ≤ B₀) :
    (cleared A B Q J).natDegree ≤ B₀+(a-1)*J := by
  rw [cleared, Polynomial.sum_def]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have ij := (le_natDegree_of_mem_supp i hi).trans cap
  have ident : i*a + (J-i)*(a-1) = i + (a-1)*J := by
    have split : J = i+(J-i) := by omega
    have s : (a-1)+1=a := by omega
    calc
      _ = i*((a-1)+1)+(J-i)*(a-1) := by rw [s]
      _ = i+(a-1)*(i+(J-i)) := by ring
      _ = _ := by rw [←split]
  calc
    _ ≤ ((Q.coeff i).natDegree+i*a)+(J-i)*(a-1) := by
      apply natDegree_mul_le.trans;apply Nat.add_le_add
      · apply natDegree_mul_le.trans
        exact Nat.add_le_add_left (natDegree_pow_le.trans (Nat.mul_le_mul_left _ degB)) _
      · exact natDegree_pow_le.trans (Nat.mul_le_mul_left _ degA)
    _ ≤ B₀+(a-1)*J := by
      rw [Nat.add_assoc,ident,←Nat.add_assoc]
      exact Nat.add_le_add_right (coeff i hi) _

#print axioms all_sheets
#print axioms seed_width
#print axioms ordinate_width
end
end Research6966.TerminalProjection

end Merged6967_R6966ProofTerminalProjection

section Merged6967_RingHomShortcuts
set_option Elab.async false

set_option Elab.async false

/-! On Lean 4.36 Mathlib the generic search for `AddMonoidHomClass` / `MonoidHomClass` on ring
homs between quotient and polynomial rings exceeds the synthesis budget; these shortcuts resolve
it directly. -/

@[instance high] abbrev ringHomAddMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : AddMonoidHomClass (α →+* β) α β := RingHomClass.toAddMonoidHomClass

@[instance high] abbrev ringHomMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : MonoidHomClass (α →+* β) α β := RingHomClass.toMonoidHomClass

@[instance high] abbrev ringEquivAddMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : AddMonoidHomClass (α ≃+* β) α β := RingHomClass.toAddMonoidHomClass

@[instance high] abbrev ringEquivMonoidHomClassShortcut {α β : Type*} [NonAssocSemiring α]
    [NonAssocSemiring β] : MonoidHomClass (α ≃+* β) α β := RingHomClass.toMonoidHomClass

end Merged6967_RingHomShortcuts

section Merged6967_Shared50ShapeRankBase
set_option Elab.async false


set_option Elab.async false

open scoped BigOperators

namespace Shared50ShapeRankBase

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A rank balance forces an element in one of the small support spaces. -/
theorem exists_nonzero_overlap (s : Finset ι) (V M : ι → Submodule 𝕜 E)
    (h : (∑ i ∈ s, (Module.finrank 𝕜 E - Module.finrank 𝕜 (M i))) <
      ∑ i ∈ s, Module.finrank 𝕜 (V i)) :
    ∃ i ∈ s, ∃ v : E, v ≠ 0 ∧ v ∈ V i ∧ v ∈ M i := by
  classical
  by_contra! hn
  apply (Nat.not_lt_of_ge ?_) h
  change (∑ i ∈ s, Module.finrank 𝕜 (V i)) ≤
    (∑ i ∈ s, (Module.finrank 𝕜 E - Module.finrank 𝕜 (M i)))
  refine Finset.sum_le_sum (s := s) (f := fun i => Module.finrank 𝕜 (V i))
    (g := fun i => Module.finrank 𝕜 E - Module.finrank 𝕜 (M i)) fun i hi => ?_
  have hmeet : V i ⊓ M i = ⊥ := by
    apply bot_unique
    intro v hv
    have hz : v = 0 := by
      by_contra hzero
      exact (hn i hi v hzero hv.1) hv.2
    rw [hz]
    exact Submodule.zero_mem _
  have he := (V i).finrank_sup_add_finrank_inf_eq (M i)
  rw [hmeet, finrank_bot, add_zero] at he
  have hsup := (V i ⊔ M i).finrank_le
  omega



theorem residual_order_pos {b f r k s : ℕ}
    (hr : 0 < r) (hf : s * b < f) (hG : k * f ≤ r * b) :
    0 < r - s*k := by
  by_contra! hs
  have hsr : r ≤ s*k := by omega
  have hk : 0 < k := by
    by_contra! hn
    interval_cases k
    simp at hsr
    omega
  have hprod := Nat.mul_lt_mul_of_pos_left hf hk
  have he : (s * k) * b = k * (s * b) := by ac_rfl
  rw [← he] at hprod
  exact (not_lt_of_ge hG) ((Nat.mul_le_mul_right b hsr).trans_lt hprod)

#print axioms exists_nonzero_overlap
#print axioms residual_order_pos
end Shared50ShapeRankBase

end Merged6967_Shared50ShapeRankBase
