import ProximityPrize.SubmissionLower.R6966ProofWordSurfaceInterpolation

set_option Elab.async false

-- merged module R6966ProofWordSurfaceCount
section Merged_R6966ProofWordSurfaceCount

namespace Research6966.WordSurfaceCount
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation
variable {σ K ι:Type*} [Fintype σ] [DecidableEq σ] [Field K] [Fintype ι]
noncomputable section
set_option maxHeartbeats 700000

/-- The global multiples of H have at most one fewer Taylor degree of
local image at each marked lift. This subtracts the common surface from
the count even at singular lifts. -/
theorem jet_budget (p:ι→σ→K) (k:ℕ) (cap small:σ→ℕ) (H:Pol σ K) (hn:H≠0)
    (fits:∀ j,H.degreeOf j+small j≤cap j) (vanish:∀ i,eval (p i) H=0)
    (onto:Function.Surjective ((atPoints p (k+1)).domRestrict (rect σ K cap))) :
    Fintype.card ι*finrank K (Local σ K (k+1)) + (∏j,(small j+1)) ≤
      (∏j,(cap j+1)) + Fintype.card ι*finrank K (low σ K k) := by
  classical
  let V:=rect σ K cap
  let V₀:=rect σ K small
  let A:↥V→ₗ[K](ι→Local σ K (k+1)):=(atPoints p (k+1)).domRestrict V
  let mul:↥V₀→ₗ[K]V := ((Algebra.lmul K (Pol σ K) H).comp V₀.subtype).codRestrict V (fun Q=>
    in_rect.mpr (fun j=>(degreeOf_mul_le j H Q.val).trans
      ((Nat.add_le_add_left (in_rect.mp Q.property j) _).trans (fits j))))
  let test:=A.comp mul
  let localMul (i:ι) : low σ K k →ₗ[K] Local σ K (k+1) :=
    (Ideal.Quotient.mkₐ K (high σ K (k+1))).toLinearMap.comp
      ((Algebra.lmul K (Pol σ K) (shift (p i) H)).comp (low σ K k).subtype)
  let lifting:(ι→low σ K k)→ₗ[K](ι→Local σ K (k+1)) :=
    LinearMap.pi (fun i=>(localMul i).comp (LinearMap.proj i))
  have image:test.range≤lifting.range := by
    rintro _ ⟨Q,rfl⟩
    refine ⟨fun i=>trunc k (shift (p i) Q.val),?_⟩
    funext i
    change Ideal.Quotient.mk _ (shift (p i) H*(trunc k (shift (p i) Q.val)).val)=
      Ideal.Quotient.mk _ (shift (p i) (H*Q.val))
    rw [map_mul (shift (p i))]
    exact (relation_image k _ _ ((shift_origin _ _).trans (vanish i))).symm
  have irank:finrank K test.range≤finrank K (ι→low σ K k):=
    (Submodule.finrank_mono image).trans (LinearMap.finrank_range_le lifting)
  let embed:test.ker→ₗ[K]A.ker:=(mul.comp test.ker.subtype).codRestrict _ (fun Q=>Q.property)
  have inject:Function.Injective embed := fun a b eq=>Subtype.ext (Subtype.ext
    (mul_left_cancel₀ hn (congrArg (fun x:↥A.ker=>(x.val:Pol σ K)) eq)))
  have krank:=LinearMap.finrank_le_finrank_of_injective inject
  have dimA:=LinearMap.finrank_range_add_finrank_ker A
  have dimT:=LinearMap.finrank_range_add_finrank_ker test
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,Module.finrank_pi_fintype] at dimA
  rw [Module.finrank_pi_fintype] at irank
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at dimA irank
  have big:finrank K V=∏j,(cap j+1):=rectangle_dimension (K:=K) cap
  have little:finrank K V₀=∏j,(small j+1):=rectangle_dimension (K:=K) small
  omega

/-- A three-variable surface needs two independent Taylor directions
per marked lift. -/
theorem trivariate_budget (p:ι→Fin 3→K) (k:ℕ) (cap small:Fin 3→ℕ)
    (H:Pol (Fin 3) K) (hn:H≠0) (fits:∀ j,H.degreeOf j+small j≤cap j)
    (vanish:∀ i,eval (p i) H=0)
    (onto:Function.Surjective ((atPoints p (k+2)).domRestrict (rect (Fin 3) K cap))) :
    Fintype.card ι*((k+3).choose 2)+(∏j,(small j+1))≤∏j,(cap j+1) := by
  have count:=jet_budget p (k+1) cap small H hn fits vanish onto
  rw [(LinearEquiv.ofBijective _ (read_bijective (σ:=Fin 3) (K:=K) (k+1))).finrank_eq,
    local_dimension,local_dimension] at count
  simp only [Fintype.card_fin] at count
  have step:(k+1+3).choose 3=(k+3).choose 2+(k+3).choose 3 := by
    rw [show k+1+3=(k+3)+1 by omega,Nat.choose_succ_succ]
  rw [step,Nat.mul_add] at count
  omega

end
end Research6966.WordSurfaceCount

end Merged_R6966ProofWordSurfaceCount

-- merged module R6966ProofWordSurfaceMarks
section Merged_R6966ProofWordSurfaceMarks

namespace Research6966.WordSurfaceMarks
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceCount
variable {σ K ι I :Type*} [Fintype σ] [DecidableEq σ] [Field K] [Fintype I] [DecidableEq I]
noncomputable section
set_option maxHeartbeats 500000

def hits (x:σ→K) (rows:I→Pol σ K) : Finset I := by
  classical
  exact univ.filter (fun i=>eval x (rows i)=0)

theorem hit {x:σ→K} {rows:I→Pol σ K} {i:I} : i∈hits x rows ↔ eval x (rows i)=0 := by
  classical
  simp [hits]

def separator (p:ι→σ→K) (rows:I→Pol σ K) (t:ℕ) (x:ι) : Pol σ K :=
  (∏i∈(univ\hits (p x) rows),rows i)^t

/-- A mark's missed rows provide its own separator. Other marks hit
at least A-d of these rows, so the separator has the claimed local order. -/
theorem separator_spec (p:ι→σ→K) (rows:I→Pol σ K) (D:σ→ℕ) (cap:∀ i j,(rows i).degreeOf j≤D j)
    (A d t:ℕ) (enough:∀ z,A≤(hits (p z) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    let sep:=separator p rows t
    (∀ x j,(sep x).degreeOf j≤t*(Fintype.card I-A)*D j) ∧
      (∀ x,eval (p x) (sep x)≠0) ∧
      (∀ x y,x≠y → shift (p x) (sep y)∈high σ K (t*(A-d))) := by
  classical
  let misses (x:ι):=univ\hits (p x) rows
  let product (x:ι):=∏i∈misses x,rows i
  change (∀ x j,((product x)^t).degreeOf j≤_) ∧ (∀ x,eval (p x) ((product x)^t)≠0) ∧ _
  refine ⟨?_,?_,?_⟩
  · intro x j
    have pair:=card_sdiff_add_card_eq_card (subset_univ (hits (p x) rows))
    have n:(misses x).card≤Fintype.card I-A := by dsimp only [misses];rw [card_univ] at pair;have:=enough x;omega
    have deg:(product x).degreeOf j≤(misses x).card*D j :=
      (degreeOf_prod_le j _ _).trans ((sum_le_sum (s:=misses x) (fun i _=>cap i j)).trans_eq (by simp))
    exact (degreeOf_pow_le j _ t).trans (by
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left t (deg.trans (Nat.mul_le_mul_right (D j) n)))
  · intro x
    rw [map_pow]
    apply pow_ne_zero
    rw [show eval (p x) (product x)=∏i∈misses x,eval (p x) (rows i) from map_prod ..]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi;exact fun eq=>(mem_sdiff.mp hi).2 (hit.mpr eq)
  · intro x y ne
    have close:(hits (p x) rows\hits (p y) rows).card≥A-d := by
      have := card_sdiff_add_card_inter (hits (p x) rows) (hits (p y) rows)
      have n:=enough x
      have join:=shared x y ne
      omega
    let order:I→ℕ:=fun i=>if i∈hits (p x) rows then 1 else 0
    have covered: (∑i∈misses y,order i) = (hits (p x) rows\hits (p y) rows).card := by
      dsimp [order]
      rw [Finset.sum_boole]
      have eq:((misses y).filter (fun i=>i∈hits (p x) rows)) = hits (p x) rows\hits (p y) rows := by
        ext i;simp [misses];tauto
      rw [eq];rfl
    have rowOrder (i:I) : shift (p x) (rows i) ∈
        restrictWeightedOrder (fun _:σ=>1) (order i) := by
      by_cases inside:i∈hits (p x) rows
      · rw [show order i=1 by simp [order,inside],←high_eq]
        exact high_one.mpr ((shift_origin _ _).trans (hit.mp inside))
      · simp [order,inside]
    have all:=prod_mem_restrictWeightedOrder (R:=K) (w:=fun _:σ=>1) (misses y)
      (a:=order) (p:=fun i=>shift (p x) (rows i)) (fun i _=>rowOrder i)
    have base:shift (p x) (product y)∈high σ K (A-d) := by
      change _∈(high σ K (A-d)).restrictScalars K
      rw [high_eq]
      dsimp only [product];rw [map_prod]
      exact restrictWeightedOrder_anti _ (covered ▸ close) all
    change shift (p x) ((product y)^t) ∈ _
    rw [map_pow]
    exact high_pow base t

theorem separators (p:ι→σ→K) (rows:I→Pol σ K) (D:σ→ℕ) (cap:∀ i j,(rows i).degreeOf j≤D j)
    (A d t:ℕ) (enough:∀ z,A≤(hits (p z) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    ∃ sep:ι→Pol σ K,
      (∀ x j,(sep x).degreeOf j≤t*(Fintype.card I-A)*D j) ∧
      (∀ x,eval (p x) (sep x)≠0) ∧
      (∀ x y,x≠y → shift (p x) (sep y)∈high σ K (t*(A-d))) := by
  exact ⟨separator p rows t,separator_spec p rows D cap A d t enough shared⟩

end
end Research6966.WordSurfaceMarks

end Merged_R6966ProofWordSurfaceMarks
