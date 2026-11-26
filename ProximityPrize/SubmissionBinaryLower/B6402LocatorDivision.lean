import ProximityPrize.SubmissionBinaryLower.B6402RegularLocator
import ProximityPrize.SubmissionBinaryLower.P64Cofactor

/-! Divide by the simultaneous regular-fibre locator and account for
the exact weight removed, line orders and original-label specializations. -/
namespace ProximityPrize.SubmissionBinaryLower.B6402LocatorDivision
open Polynomial B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402MixedDegree
open P64Caps.Weighted P64LineOrder BCHKSSubstitutionVanish
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {K I : Type*} [Field K] [CharP K 2] [DecidableEq I]
local notation "Tri" => BiPoly (Polynomial K)

noncomputable def fibre (x : K) : Tri := C (Polynomial.X-C (C x))
noncomputable def locator (x : I ↪ K) (S : Finset I) (b : ℕ) : Tri := ∏ i∈S,(fibre (x i))^(2*b)

theorem fibre_ne (x : K) : fibre x≠0 := C_ne_zero.mpr (X_sub_C_ne_zero _)
theorem loc_ne (x : I ↪ K) (S : Finset I) (b : ℕ) : locator x S b≠0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (fibre_ne (x i))

theorem factored (x : I ↪ K) (S : Finset I) (b : ℕ) (p : Tri) (hp : p≠0)
    (hd : ∀ i∈S, fibre (x i)^(2*b) ∣ p) :
    ∃ q : Tri, q≠0 ∧ p=locator x S b*q := by
  have h : locator x S b ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hne
      have hu : IsUnit (x i-x j) := (sub_ne_zero.mpr (x.injective.ne hne)).isUnit
      have hu' : IsUnit (C (x i)-C (x j)) := by rw [←map_sub]; exact hu.map C
      exact ((isCoprime_X_sub_C_of_isUnit_sub hu').map C).pow
    · exact hd
  obtain ⟨q,eq⟩ := h
  exact ⟨q,fun hz => hp (by rw [eq,hz,mul_zero]),eq⟩

theorem weight_C (w : ℕ) (p : (Polynomial K)[X]) (hn : p≠0) :
    weightedSupportDegree (C p) w=p.natDegree := by
  unfold weightedSupportDegree
  rw [support_C hn]
  simp

private theorem weight_one (w : ℕ) : weightedSupportDegree (1 : Tri) w=0 := by
  rw [show (1:Tri)=C (1 : (Polynomial K)[X]) by simp,weight_C _ _ one_ne_zero,natDegree_one]

theorem weighted_fibre (x : K) (w : ℕ) : weightedSupportDegree (fibre x) w=1 := by
  unfold fibre; rw [weight_C _ _ (X_sub_C_ne_zero _),natDegree_X_sub_C]

theorem weighted_locator (x : I ↪ K) (S : Finset I) (b w : ℕ) :
    weightedSupportDegree (locator x S b) w=2*b*S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [locator,weight_one]
  | insert i S hi ih =>
    rw [Finset.card_insert_of_notMem hi,Nat.mul_add,Nat.mul_one]
    change weightedSupportDegree (∏ j∈insert i S,fibre (x j)^(2*b)) w=_
    rw [Finset.prod_insert hi]
    change weightedSupportDegree (fibre (x i)^(2*b)*locator x S b) w=_
    rw [weightedSupportDegree_mul _ _ _ (pow_ne_zero _ (fibre_ne _)) (loc_ne x S b)]
    have hpow (n : ℕ) : weightedSupportDegree (fibre (x i)^n) w=n := by
      induction n with
      | zero => simp [weight_one]
      | succ n h => rw [pow_succ,weightedSupportDegree_mul _ _ _ (pow_ne_zero _ (fibre_ne _)) (fibre_ne _),h,weighted_fibre]
    rw [hpow]; change 2*b+weightedSupportDegree (locator x S b) w=_
    rw [ih,add_comm]

theorem fibre_curve (x z : K) (P : K[X]) : BCHKSSubstitutionVanish.triEval (fibre x) z P=Polynomial.X-C x := by
  rw [←P64Cofactor.triEvalHom_apply]
  simp [fibre,P64Cofactor.triEvalHom]

theorem curve_ne (x : I ↪ K) (S : Finset I) (b : ℕ) (z : K) (P : K[X]) :
    BCHKSSubstitutionVanish.triEval (locator x S b) z P≠0 := by
  rw [←P64Cofactor.triEvalHom_apply]
  simp only [locator,map_prod,map_pow]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (by
    rw [P64Cofactor.triEvalHom_apply,fibre_curve]; exact X_sub_C_ne_zero _))

theorem quotient_seed (p l r : Tri) (hp : p≠0) (eq : p=l*r) (H : ℕ)
    (hcap : ∀ j a, ((p.coeff j).coeff a).natDegree≤H) :
    ∀ j a, ((r.coeff j).coeff a).natDegree≤H := by
  have hl : l≠0 := fun hz => hp (by rw [eq,hz,zero_mul])
  have hr : r≠0 := fun hz => hp (by rw [eq,hz,mul_zero])
  have hCp : mixed 0 (C p)≤H := by
    rw [mixed_le_iff]; intro k j a hn
    by_cases hz : k=0
    · subst k; simpa using hcap j a
    · simp [coeff_C,hz] at hn
  have hmul : mixed 0 (C p)=mixed 0 (C l : ContactPoly (Polynomial K))+mixed 0 (C r) := by
    rw [eq,map_mul,mixed_mul 0 (C_ne_zero.mpr hl) (C_ne_zero.mpr hr)]
  have hCr : mixed 0 (C r)≤H := by omega
  intro j a; by_cases hz : (r.coeff j).coeff a=0
  · simp [hz]
  · have hn : (((C r : ContactPoly (Polynomial K)).coeff 0).coeff j).coeff a≠0 := by simpa using hz
    simpa using (mixed_le_iff 0 H (C r)).mp hCr 0 j a hn

#print axioms factored
#print axioms weighted_locator
#print axioms curve_ne
#print axioms quotient_seed
end ProximityPrize.SubmissionBinaryLower.B6402LocatorDivision
