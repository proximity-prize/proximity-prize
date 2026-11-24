import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.RingTheory.AdjoinRoot
import ArkLib.Data.Polynomial.FractionFieldResultant

-- merged module R6960BranchCollisions
section Merged_R6960BranchCollisions
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace Lower6960.BranchCollisions
open Polynomial Finset
open ProximityPrize.SubmissionLower.MatrixRootMultiplicity
open CurvatureSquares (mulBox)
open scoped Polynomial BigOperators
variable {K : Type} [Field K] [DecidableEq K]
omit [DecidableEq K] in
theorem divisor_corank {f g d : (Polynomial K)} {m n : ℕ}
    (hf : f≠0) (df : d∣f) (dg : d∣g) (fm : f.natDegree≤m) (gn : g.natDegree≤n) :
    d.natDegree≤m+n-(sylvester f g m n).rank := by
  obtain ⟨a,fa⟩ := df
  obtain ⟨b,gb⟩ := dg
  have prod : d*a≠0 := fa ▸ hf
  have dn := left_ne_zero_of_mul prod
  have an := right_ne_zero_of_mul prod
  have afit : a.natDegree+d.natDegree≤m := by
    rw [Nat.add_comm,←natDegree_mul dn an,←fa]; exact fm
  let U := mulBox (L:=K) a d.natDegree m (fun _=>afit)
  have bfit (hb : (-b)≠0) : (-b).natDegree+d.natDegree≤n := by
    have bn : b≠0 := fun hz=>hb (by simp [hz])
    rw [gb,natDegree_mul dn bn] at gn
    rw [natDegree_neg]; omega
  let V := mulBox (L:=K) (-b) d.natDegree n bfit
  let S := sylvesterMap f g fm gn
  let B := U.prod V
  have ker (u : degreeLT K d.natDegree) : B u∈LinearMap.ker S := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change f*(-b*(u:(Polynomial K)))+g*(a*(u:(Polynomial K)))=0
    rw [fa,gb]; ring
  let L := B.codRestrict (LinearMap.ker S) ker
  have inj : Function.Injective L := by
    intro x y eq
    apply Subtype.ext
    exact mul_left_cancel₀ an (congrArg (fun v : LinearMap.ker S=>(v.val.1 : (Polynomial K))) eq)
  let := Module.Finite.of_basis (degreeLT.basis K m)
  let := Module.Finite.of_basis (degreeLT.basis K n)
  have h := LinearMap.finrank_le_finrank_of_injective (f:=L) inj
  have dim (t : ℕ) : Module.finrank K (degreeLT K t)=t := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis K t)
  rw [dim] at h
  have rank := S.finrank_range_add_finrank_ker
  rw [Module.finrank_prod,dim,dim] at rank
  have eq : (sylvester f g m n).rank=Module.finrank K (LinearMap.range S) := by
    let dom := ((degreeLT.basis K m).prod (degreeLT.basis K n)).reindex finSumFinEquiv
    rw [Matrix.rank_eq_finrank_range_toLin _ (degreeLT.basis K _) dom,
      ←toMatrix_sylvesterMap' f g fm gn, Matrix.toLin_toMatrix]
  rw [eq]; omega
def collisionMass (f branch : (Polynomial K)) (points : Finset K) : ℕ :=
  ∑ x ∈ points, if 2≤branch.rootMultiplicity x then f.rootMultiplicity x else 0
theorem collision_le_twice_gcd {f branch : (Polynomial K)} (nonzero : branch≠0)
    (divisor : f∣branch) (points : Finset K) :
    collisionMass f branch points ≤ 2*(gcd f branch.derivative).natDegree := by
  have fn : f≠0 := fun z=>nonzero (zero_dvd_iff.mp (z ▸ divisor))
  have gn : gcd f branch.derivative≠0 := fun z=>fn (zero_dvd_iff.mp (z ▸ gcd_dvd_left f branch.derivative))
  apply le_trans _ (Nat.mul_le_mul_left 2
    (sum_rootMultiplicity_le_natDegree (gcd f branch.derivative) points))
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  split_ifs with hx
  · let k := min (f.rootMultiplicity x) (branch.rootMultiplicity x-1)
    have kf : ((Polynomial.X : (Polynomial K))-C x)^k∣f := (le_rootMultiplicity_iff fn).mp (min_le_left ..)
    have kb : ((Polynomial.X : (Polynomial K))-C x)^k∣branch.derivative :=
      (pow_dvd_pow _ (min_le_right ..)).trans
        (pow_sub_one_dvd_derivative_of_pow_dvd (branch.pow_rootMultiplicity_dvd x))
    have lower : k≤(gcd f branch.derivative).rootMultiplicity x :=
      (le_rootMultiplicity_iff gn).mpr (dvd_gcd kf kb)
    have hle : f.rootMultiplicity x≤branch.rootMultiplicity x :=
      (le_rootMultiplicity_iff nonzero).mpr ((f.pow_rootMultiplicity_dvd x).trans divisor)
    dsimp [k] at lower
    omega
  · omega
theorem stratum {F B : Polynomial (Polynomial K)} (divisor : F∣B)
    (T : Finset K) (places : K→Finset K)
    (good : ∀z∈T,B.map (evalRingHom z)≠0)
    (sep : F.resultant B.derivative F.natDegree (B.natDegree-1)≠0)
    {u v : ℕ} (fu : ∀ j,(F.coeff j).natDegree≤u) (bv : ∀ j,(B.coeff j).natDegree≤v) :
    (∑ z∈T, collisionMass (F.map (evalRingHom z)) (B.map (evalRingHom z)) (places z)) ≤
      2*((B.natDegree-1)*u+F.natDegree*v) := by
  have point (z : K) (hz : z∈T) := good z hz
  have single (z : K) (hz : z∈T) := collision_le_twice_gcd (point z hz)
    (map_dvd (mapRingHom (evalRingHom z)) divisor) (places z)
  have per (z : K) (hz : z∈T) : collisionMass (F.map (evalRingHom z)) (B.map (evalRingHom z)) (places z)
      ≤ 2*(F.natDegree+(B.natDegree-1) -
        (sylvester (F.map (evalRingHom z)) (B.derivative.map (evalRingHom z)) F.natDegree (B.natDegree-1)).rank) := by
    have d := single z hz
    change collisionMass (F.map _) (B.map _) _ ≤ 2*(gcd (F.map _) (B.map _).derivative).natDegree at d
    rw [derivative_map] at d
    have fn : F.map (evalRingHom z)≠0 := by
      intro eq
      apply point z hz
      obtain ⟨a,ha⟩ := divisor
      simp [ha,eq,Polynomial.map_mul]
    exact d.trans (Nat.mul_le_mul_left 2 (divisor_corank fn (gcd_dvd_left ..) (gcd_dvd_right ..)
      natDegree_map_le (natDegree_map_le.trans (natDegree_derivative_le _))))
  have total := sum_le_sum per
  rw [←mul_sum] at total
  have cor := sum_sylvester_coranks_le_resultant_natDegree F B.derivative F.natDegree (B.natDegree-1) T sep
  have fee := natDegree_resultant_le_of_coeff_natDegree_le F B.derivative F.natDegree (B.natDegree-1) u v fu
    (fun j=>by rw [coeff_derivative,mul_comm,show ((j:(Polynomial K))+1)=C ((j:K)+1) by simp]
               exact (natDegree_C_mul_le ..).trans (bv _))
  exact total.trans (Nat.mul_le_mul_left 2 (cor.trans fee))
#print axioms stratum
omit [DecidableEq K] in
private theorem nonzero_resultant {F B : Polynomial (Polynomial K)} (dvd : F∣B)
    (sep : (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable) :
    F.resultant B.derivative F.natDegree (B.natDegree-1)≠0 := by
  let a:=algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have inj : Function.Injective a := IsFractionRing.injective _ _
  have hf : F.map a≠0 := fun hz=>sep.ne_zero (zero_dvd_iff.mp (by
    have h := Polynomial.map_dvd a dvd
    rwa [hz] at h))
  have cop : IsCoprime (F.map a) (B.derivative.map a) := by
    rw [←derivative_map]
    exact (show IsCoprime (B.map a) (B.map a).derivative from sep).of_isCoprime_of_dvd_left
      (Polynomial.map_dvd a dvd)
  have actual := resultant_ne_zero (F.map a) (B.derivative.map a) cop
  have bound := natDegree_derivative_le B
  have padded : (F.map a).resultant (B.derivative.map a) F.natDegree (B.natDegree-1) ≠ 0 := by
    rw [←Nat.add_sub_of_le bound,←natDegree_map_eq_of_injective inj B.derivative,
      ←natDegree_map_eq_of_injective inj F,
      resultant_add_right_deg _ _ _ _ _ le_rfl,coeff_natDegree]
    exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf)) actual
  rw [resultant_map_map] at padded
  exact fun hz=>padded (by rw [hz,map_zero])
theorem weighted {ι : Type*} [Fintype ι] (F : ι→Polynomial (Polynomial K)) (w : ι→ℕ)
    (positive : ∀ i, 0<w i) (B : Polynomial (Polynomial K)) (prod : B=∏i,F i)
    (sep : (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable)
    (T : Finset K) (places : K→Finset K) (good : ∀ z∈T,B.map (evalRingHom z)≠0)
    {s t : ℕ} (xcap : (∑ i,w i*(F i).natDegree)≤2*s)
    (zcap : (∑ i,w i*CurvatureSquares.height (F i))≤2*t) :
    (∑ i,w i*(∑ z∈T,collisionMass ((F i).map (evalRingHom z)) (B.map (evalRingHom z)) (places z)))
       ≤ 16*s*t := by
  classical
  let u := ∑i,CurvatureSquares.height (F i)
  have xsum : (∑ i,(F i).natDegree)≤2*s :=
    (sum_le_sum (fun i _=>Nat.le_mul_of_pos_left _ (positive i))).trans xcap
  have bcap : B.natDegree≤2*s := by rw [prod]; exact (natDegree_prod_le ..).trans xsum
  have ucap : u≤2*t :=
    (sum_le_sum (fun i _=>Nat.le_mul_of_pos_left _ (positive i))).trans zcap
  have total : CurvatureSquares.height B≤u := by
    dsimp only [CurvatureSquares.height,u]
    rw [prod,map_prod]
    exact natDegree_prod_le ..
  let v := fun i=>CurvatureSquares.height (F i)
  have calc1 (i : ι) : (∑ z∈T,collisionMass ((F i).map (evalRingHom z)) (B.map (evalRingHom z)) (places z))
        ≤ 2*((B.natDegree-1)*v i+(F i).natDegree*u) := by
    have div : F i∣B := prod ▸ dvd_prod_of_mem F (mem_univ i)
    exact stratum div T places good (nonzero_resultant div sep)
      (CurvatureSquares.coeff_height (F i)) (fun j=>(CurvatureSquares.coeff_height B j).trans total)
  calc _ ≤ ∑ i,w i*(2*((B.natDegree-1)*v i+(F i).natDegree*u)) :=
             sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (calc1 i))
       _ = ∑ i, ((2*(B.natDegree-1))*(w i*v i)+(2*u)*(w i*(F i).natDegree)) := by
             apply sum_congr rfl; intro i _; ring
       _ = 2*(B.natDegree-1)*(∑i,w i*v i)+2*u*(∑i,w i*(F i).natDegree) := by
             rw [sum_add_distrib,←mul_sum,←mul_sum]
       _ ≤ (2*(2*s))*(2*t)+(2*(2*t))*(2*s) :=
             Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) zcap)
               (Nat.mul_le_mul (Nat.mul_le_mul_left _ ucap) xcap)
       _ = 16*s*t := by ring
#print axioms weighted
omit [DecidableEq K] in
theorem tame_separable (p : ℕ) [CharP (FractionRing (Polynomial K)) p]
    {B : Polynomial (Polynomial K)} (sf : Squarefree B) (small : B.natDegree<p) :
    (B.map (algebraMap (Polynomial K) (FractionRing (Polynomial K)))).Separable := by
  let a:=algebraMap (Polynomial K) (FractionRing (Polynomial K))
  have inj : Function.Injective a := IsFractionRing.injective _ _
  apply CurvatureSquares.separable_kernel B sf
  intro q _ div pos
  have bound := (natDegree_le_of_dvd div sf.ne_zero).trans_lt small
  have degree := natDegree_map_eq_of_injective inj q
  have ne := CurvatureSquares.derivative_ne_zero_of_natDegree_pos_lt_char p (q.map a)
    (by simpa only [degree] using pos) (by simpa only [degree] using bound)
  intro h
  exact ne (by rw [derivative_map,h,Polynomial.map_zero])
#print axioms tame_separable
end Lower6960.BranchCollisions

end
end Merged_R6960BranchCollisions

-- merged module R6960MarkedRoot
section Merged_R6960MarkedRoot
noncomputable section
set_option Elab.async false
namespace Lower6960.MarkedRoot
open Polynomial Finset
open scoped Polynomial
variable {K : Type} [Field K] [DecidableEq K]
theorem sheet {F : (Polynomial K)} (degree : 2≤F.natDegree) (y : K) (root : F.eval y=0)
    (simple : F.derivative.eval y≠0) :
    ∃ H Q : (Polynomial K),F=(Polynomial.X-C y)*Q ∧ H.eval y=1 ∧ Q∣H ∧
      let e:=AdjoinRoot.mk F H
      e^2=e ∧ e≠0 ∧ e≠1 := by
  have fn : F≠0 := by intro eq; simp [eq] at degree
  obtain ⟨Q,eq⟩ := dvd_iff_isRoot.mpr root
  have qn : Q≠0 := fun h=>fn (by rw [eq,h,mul_zero])
  have qdeg : F.natDegree=1+Q.natDegree := by
    rw [eq,natDegree_mul (X_sub_C_ne_zero _) qn,natDegree_X_sub_C]
  have qy : Q.eval y≠0 := by
    rw [eq,derivative_mul] at simple
    simpa using simple
  let H:=C (Q.eval y)⁻¹*Q
  have value : H.eval y=1 := by simp [H,qy]
  have hd : H.natDegree=Q.natDegree := natDegree_C_mul (inv_ne_zero qy)
  have hn : H≠0 := by intro h; simp [h] at value
  have div : Polynomial.X-C y∣H-1 := dvd_iff_isRoot.mpr (by simp [Polynomial.IsRoot,value])
  obtain ⟨G,fac⟩ := div
  have rel : F∣H*(H-1) := by
    refine ⟨C (Q.eval y)⁻¹*G,?_⟩
    rw [fac,eq]; unfold H; ring
  let e:=AdjoinRoot.mk F H
  have idemp : e^2=e := by
    have zero := AdjoinRoot.mk_eq_zero.mpr rel
    rw [map_mul,map_sub,map_one] at zero
    change e*(e-1)=0 at zero
    linear_combination zero
  refine ⟨H,Q,eq,value,dvd_mul_left ..,idemp,?_,?_⟩
  · intro zero
    have h := natDegree_le_of_dvd (AdjoinRoot.mk_eq_zero.mp zero) hn
    omega
  · intro one
    have zero : AdjoinRoot.mk F (H-1)=0 := by rw [map_sub,map_one,one,sub_self]
    have dv := AdjoinRoot.mk_eq_zero.mp zero
    by_cases h : H-1=0
    · have he := sub_eq_zero.mp h
      rw [he,natDegree_one] at hd; omega
    · have hle := natDegree_le_of_dvd dv h
      have upper := natDegree_sub_le H 1
      rw [natDegree_one,_root_.max_zero] at upper; omega
theorem good_marks (F : Polynomial (Polynomial K)) (p : ℕ) [CharP (FractionRing (Polynomial K)) p]
    (ir : Irreducible F) (large : 2≤F.natDegree) (tame : F.natDegree<p)
    (v : ℕ) (seed : ∀j,(F.coeff j).natDegree≤v)
    (T : Finset K) (word : K→K) (root : ∀z∈T,(F.map (evalRingHom z)).eval (word z)=0) :
    ∃ bad ⊆ T, bad.card≤(2*F.natDegree-1)*v ∧
      ∀ z∈T, z∉bad → let f:=F.map (evalRingHom z)
        f.natDegree=F.natDegree ∧ f.Separable ∧
        ∃ H Q : (Polynomial K), f=(Polynomial.X-C (word z))*Q ∧ H.eval (word z)=1 ∧ Q∣H ∧
          let e:=AdjoinRoot.mk f H
          e^2=e ∧ e≠0 ∧ e≠1 := by
  classical
  let R:=F.resultant F.derivative F.natDegree (F.natDegree-1)
  have rn : R≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField F
    (BranchCollisions.tame_separable p ir.squarefree tame)
  have deg := natDegree_resultant_le_of_coeff_natDegree_le F F.derivative F.natDegree
    (F.natDegree-1) v v seed (fun j=>by
      rw [coeff_derivative,mul_comm,show ((j:(Polynomial K))+1)=C ((j:K)+1) by simp]
      exact (natDegree_C_mul_le _ _).trans (seed _))
  let bad:=T.filter fun z=>R.eval z=0
  have incl : bad⊆R.roots.toFinset := fun z hz => Multiset.mem_toFinset.mpr
    ((mem_roots rn).mpr (mem_filter.mp hz).2)
  refine ⟨bad,filter_subset _ _,?_,?_⟩
  · refine ((card_le_card incl).trans ((Multiset.toFinset_card_le _).trans (card_roots' _))).trans ?_
    exact deg.trans_eq (by rw [←Nat.add_mul]; congr 1; omega)
  · intro z hz keep
    have unit : (evalRingHom z) R≠0 := fun h=>keep (mem_filter.mpr ⟨hz,h⟩)
    have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
      le_rfl unit
    have sep := separable_map_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
      le_rfl (by omega) unit
    exact ⟨full,sep,sheet (full ▸ large) (word z) (root z hz)
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (evalRingHom z) F
        le_rfl (by omega) unit (word z) (root z hz))⟩
#print axioms good_marks
end Lower6960.MarkedRoot

end
end Merged_R6960MarkedRoot
