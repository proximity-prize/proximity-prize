import ProximityPrize.SubmissionLower.Fast055
import ArkLib.Data.Polynomial.ResultantDegree
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! Lower-track projected ordinate counts. The determinant proof originated in
the Proximity Prize archive at b3fac81ad. The voting, square-fibre and projection
proofs come from the anchor-linear-system research worktree. -/

set_option Elab.async false
set_option maxHeartbeats 1600000

namespace RetainedShortening
open K1 Polynomial
open scoped Polynomial

structure Word (A d : ℕ) (w : I → K) (s : K → K[X]) (T : Finset K) : Prop where
  distinct : Set.InjOn s (T : Set K)
  degree : ∀ z ∈ T, (s z).natDegree ≤ d
  hits : ∀ z ∈ T, ∃ B : Finset I, A ≤ B.card ∧ ∀ i ∈ B, (s z).eval (node i) = w i


end RetainedShortening

namespace CurvatureVotes
noncomputable section
open K1 Finset Polynomial RetainedShortening
open scoped BigOperators

/-- The second alternative retains the factor m-L in the minority product. -/
def VoteScale (A d k : ℕ) : Prop :=
  262144≤k*(A-d) ∨ (k=5 ∧ 4*262144≤25*(A-d))

private theorem side_product {h m L n : ℕ} (total : h+m=n) (room : 2*L≤n) (hit : h≤L) :
    h*m≤L*(n-L) := by
  obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le hit
  obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le (by omega : L≤m)
  have hn : n-L=h+y := by omega
  rw [hn,hy,hx]
  nlinarith [Nat.zero_le (x*y)]

/-- Every ordered pair of distinct scalar polynomials has at least A-d
coordinates hit by its first member and missed by the second. -/
theorem minority_count {A d w s T} (W : Word A d w s T) {L k : ℕ}
    (hd : d<A) (scale : VoteScale A d k)
    (minor : ∀ i : I,
      (T.filter fun z => (s z).eval (node i)=w i).card≤L ∨
      (T.filter fun z => (s z).eval (node i)≠w i).card≤L) :
    T.card≤k*L+1 := by
  classical
  let H (z : K) (i : I) := (s z).eval (node i)=w i
  let hits (z : K) := univ.filter (H z)
  have many (z) (hz : z∈T) : A≤(hits z).card := by
    obtain ⟨B,hB,hw⟩ := W.hits z hz
    exact hB.trans (card_le_card fun i hi => mem_filter.mpr ⟨mem_univ _,hw i hi⟩)
  have pair (z) (hz : z∈T) (y) (hy : y∈T) (ne : z≠y) :
      A-d ≤ (hits z \ hits y).card := by
    have nd : s z-s y ≠ 0 := sub_ne_zero.mpr fun h => ne (W.distinct hz hy h)
    have same := FrobeniusLocator.Strata.root_nodes_card_le node
      ProximityPrize.Benchmark.IRSProfile.domain.injective (s z-s y) nd (hits z ∩ hits y) (by
        intro i hi
        have hz' : (s z).eval (node i)=w i := (mem_filter.mp (mem_inter.mp hi).1).2
        have hy' : (s y).eval (node i)=w i := (mem_filter.mp (mem_inter.mp hi).2).2
        simp [eval_sub,hz',hy'])
    have deg := (natDegree_sub_le _ _).trans (max_le (W.degree _ hz) (W.degree _ hy))
    have split := card_sdiff_add_card_inter (hits z) (hits y)
    have h := many z hz
    omega
  let count (z y : K) := ∑ i : I, (if H z i then 1 else 0)*(if H y i then 0 else 1 : ℕ)
  have cv (z y) : count z y = (hits z \ hits y).card := by
    have eq : hits z \ hits y = univ.filter fun i => H z i ∧ ¬ H y i := by
      ext i; simp [hits]
    rw [eq,card_filter]
    apply sum_congr rfl
    intro i _
    by_cases hz : H z i <;> by_cases hy : H y i <;> simp [hz,hy]
  have row (z) (hz : z∈T) : (T.card-1)*(A-d) ≤ ∑ y∈T,count z y := by
    calc
      _ = ∑ _y∈T.erase z, (A-d) := by simp [card_erase_of_mem hz]
      _ ≤ ∑ y∈T.erase z,count z y := sum_le_sum fun y hy => (pair z hz y
        (mem_of_mem_erase hy) (ne_of_mem_erase hy).symm).trans_eq (cv z y).symm
      _ ≤ _ := sum_le_sum_of_subset (erase_subset _ _)
  have upper (i : I) : (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) ≤ T.card*L := by
    have hc := card_le_card (filter_subset (fun z => H z i) T)
    have mc := card_le_card (filter_subset (fun z => ¬ H z i) T)
    rcases minor i with h|h
    · change (T.filter fun z => H z i).card≤L at h
      rw [card_filter] at h mc
      simp only [ite_not] at mc
      simpa only [Nat.mul_comm T.card] using Nat.mul_le_mul h mc
    · change (T.filter fun z => ¬H z i).card≤L at h
      rw [card_filter] at h hc
      simp only [ite_not] at h
      exact Nat.mul_le_mul hc h
  have full (C : ℕ) (hu : ∀ i : I, (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) ≤ C) :
        T.card*((T.card-1)*(A-d)) ≤ 262144*C := calc
    _ = ∑ _z∈T, (T.card-1)*(A-d) := by simp
    _ ≤ ∑ z∈T, ∑ y∈T, count z y := sum_le_sum row
    _ = ∑ i : I, (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) := by
      unfold count
      simp_rw [show ∀ z, (∑ y∈T, ∑ i : I, (if H z i then 1 else 0)*
          (if H y i then 0 else 1 : ℕ)) = _ from fun z => sum_comm]
      rw [sum_comm]
      simp [sum_mul_sum]
    _ ≤ ∑ _i : I, C := sum_le_sum fun i _ => hu i
    _ = _ := by simp
  rcases scale with scale | ⟨rfl,scale⟩
  ·
    by_cases empty : T.card=0
    · omega
    have h := (full _ upper).trans (Nat.mul_le_mul_right (T.card*L) scale)
    have rearranged : T.card*((T.card-1)*(A-d)) ≤ T.card*((k*L)*(A-d)) := by
      simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
    have step := Nat.le_of_mul_le_mul_left rearranged (by omega : 0<T.card)
    have last := Nat.le_of_mul_le_mul_right step (by omega : 0<A-d)
    omega
  · by_contra! bad
    have hr : 2*L≤T.card := by omega
    have hu (i : I) : (∑ z∈T, if H z i then 1 else 0) *
        (∑ y∈T, if H y i then 0 else 1 : ℕ) ≤ L*(T.card-L) := by
      let h := T.filter fun z => H z i
      let m := T.filter fun z => ¬H z i
      have eqn : h.card + m.card=T.card := by
        dsimp [h,m]; exact card_filter_add_card_filter_not ..
      have side : h.card*m.card≤L*(T.card-L) := by
        rcases minor i with hit|miss
        · exact side_product eqn hr hit
        · rw [Nat.mul_comm]
          exact side_product ((Nat.add_comm ..).trans eqn) hr miss
      simpa only [h,m,card_filter,ite_not] using side
    have counted := full _ hu
    let t := T.card-(5*L+2)
    have eqn : T.card=5*L+2+t := by dsimp [t]; omega
    have lt : 25*(L*(T.card-L)) < 4*(T.card*(T.card-1)) := by
      rw [show T.card-L=4*L+2+t by omega,show T.card-1=5*L+1+t by omega,eqn]
      nlinarith [Nat.zero_le (L*t),Nat.zero_le (t*t)]
    have left := Nat.mul_lt_mul_of_pos_right lt (by omega : 0<A-d)
    have right := Nat.mul_le_mul_right (L*(T.card-L)) scale
    nlinarith only [left,right,Nat.mul_le_mul_left 4 counted]

end
end CurvatureVotes

namespace ProximityPrize.SubmissionLower.MatrixRootMultiplicity

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K] [DecidableEq K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Vanishing of a chosen collection of entire columns at a scalar gives
one factor per column in every determinant permutation product. -/
theorem pow_card_dvd_det_of_eval_columns_eq_zero
    (M : Matrix ι ι (Polynomial K)) (alpha : K) (columns : Finset ι)
    (hzero : ∀ j ∈ columns, ∀ i, (M i j).eval alpha = 0) :
    (Polynomial.X - Polynomial.C alpha) ^ columns.card ∣ M.det := by
  classical
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro permutation _
  have hpart :
      (∏ j ∈ columns, (Polynomial.X - Polynomial.C alpha)) ∣
        ∏ j ∈ columns, M (permutation j) j := by
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    exact Polynomial.dvd_iff_isRoot.mpr (hzero j hj (permutation j))
  have hfull :
      (∏ j ∈ columns, M (permutation j) j) ∣
        ∏ j : ι, M (permutation j) j :=
    Finset.prod_dvd_prod_of_subset columns Finset.univ
      (fun j => M (permutation j) j) (Finset.subset_univ columns)
  have hproduct :
      (Polynomial.X - Polynomial.C alpha) ^ columns.card ∣
        ∏ j : ι, M (permutation j) j := by
    simpa using hpart.trans hfull
  exact dvd_mul_of_dvd_right hproduct _

/-- General rank-loss divisibility, including a zero determinant. The
constant changes of basis are constructed by the actual rank-normal-form
theorem; they are not supplied as an extra hypothesis. -/
theorem pow_corank_dvd_det
    (M : Matrix ι ι (Polynomial K)) (alpha : K) :
    (Polynomial.X - Polynomial.C alpha) ^
        (Fintype.card ι - ((Polynomial.evalRingHom alpha).mapMatrix M).rank) ∣
      M.det := by
  classical
  let evalMatrix : Matrix ι ι (Polynomial K) →+* Matrix ι ι K :=
    (Polynomial.evalRingHom alpha).mapMatrix
  let constMatrix : Matrix ι ι K →+* Matrix ι ι (Polynomial K) :=
    (Polynomial.C : K →+* Polynomial K).mapMatrix
  let evaluated : Matrix ι ι K := evalMatrix M
  obtain ⟨V, U, e, hV, hU, hnormal⟩ := Matrix.exists_rank_normal_form evaluated
  let transformed : Matrix ι ι (Polynomial K) := constMatrix V * M * constMatrix U
  have heval_const (B : Matrix ι ι K) : evalMatrix (constMatrix B) = B := by
    ext i j
    simp [evalMatrix, constMatrix, RingHom.mapMatrix_apply, Matrix.map_apply]
  have heval : evalMatrix transformed =
      (Matrix.fromBlocks 1 0 0 0).submatrix e e := by
    change evalMatrix (constMatrix V * M * constMatrix U) = _
    rw [map_mul, map_mul, heval_const, heval_const]
    exact hnormal
  let zeroEmbedding : Fin (Fintype.card ι - evaluated.rank) ↪ ι := {
    toFun := fun j => e.symm (Sum.inr j)
    inj' := by
      intro i j hij
      exact Sum.inr.inj (e.symm.injective hij)
  }
  let zeroColumns : Finset ι := Finset.univ.map zeroEmbedding
  have hcard : zeroColumns.card = Fintype.card ι - evaluated.rank := by
    simp [zeroColumns]
  have hzero : ∀ j ∈ zeroColumns, ∀ i, (transformed i j).eval alpha = 0 := by
    intro j hj i
    obtain ⟨j0, _, rfl⟩ := Finset.mem_map.mp hj
    change evalMatrix transformed i (e.symm (Sum.inr j0)) = 0
    rw [heval]
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
    cases e i <;> rfl
  have hVdet : IsUnit (constMatrix V).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hV.map constMatrix)
  have hUdet : IsUnit (constMatrix U).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hU.map constMatrix)
  have hdiv := pow_card_dvd_det_of_eval_columns_eq_zero
    transformed alpha zeroColumns hzero
  rw [hcard] at hdiv
  change (Polynomial.X - Polynomial.C alpha) ^
      (Fintype.card ι - evaluated.rank) ∣
        (constMatrix V * M * constMatrix U).det at hdiv
  rw [Matrix.det_mul, Matrix.det_mul] at hdiv
  exact hVdet.dvd_mul_left.mp (hUdet.dvd_mul_right.mp hdiv)

/-- A nonzero determinant has root multiplicity at least the actual
corank of the matrix evaluated at that root. -/
theorem corank_le_rootMultiplicity_det
    (M : Matrix ι ι (Polynomial K)) (alpha : K) (hdet : M.det ≠ 0) :
    Fintype.card ι - ((Polynomial.evalRingHom alpha).mapMatrix M).rank ≤
      M.det.rootMultiplicity alpha := by
  exact (Polynomial.le_rootMultiplicity_iff hdet).mpr
    (pow_corank_dvd_det M alpha)

/-- The total multiplicity on any finite set is bounded by polynomial
degree. This uses the actual root multiset, without a splitting hypothesis. -/
theorem sum_rootMultiplicity_le_natDegree
    (P : Polynomial K) (points : Finset K) :
    (∑ alpha ∈ points, P.rootMultiplicity alpha) ≤ P.natDegree := by
  classical
  have hselected :
      (∑ alpha ∈ points, Multiset.count alpha P.roots) ≤ P.roots.card := by
    let all := points ∪ P.roots.toFinset
    calc
      (∑ alpha ∈ points, Multiset.count alpha P.roots) ≤
          ∑ alpha ∈ all, Multiset.count alpha P.roots :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (by simp)
      _ = ∑ alpha ∈ P.roots.toFinset, Multiset.count alpha P.roots := by
        symm
        apply Finset.sum_subset (Finset.subset_union_right)
        intro alpha _ hnot
        exact Multiset.count_eq_zero.mpr (by simpa using hnot)
      _ = P.roots.card := Multiset.toFinset_sum_count_eq P.roots
  calc
    (∑ alpha ∈ points, P.rootMultiplicity alpha) =
        ∑ alpha ∈ points, Multiset.count alpha P.roots := by
      apply Finset.sum_congr rfl
      intro alpha _
      exact (Polynomial.count_roots P).symm
    _ ≤ P.roots.card := hselected
    _ ≤ P.natDegree := Polynomial.card_roots' P

/-- Specialized Sylvester corank is a genuine lower bound on resultant
root multiplicity. Fixed original degrees are retained under specialization. -/
theorem sylvester_corank_le_rootMultiplicity_resultant
    (P Q : Polynomial (Polynomial K)) (m n : ℕ) (alpha : K)
    (hresultant : Polynomial.resultant P Q m n ≠ 0) :
    m + n - (Polynomial.sylvester
      (P.map (Polynomial.evalRingHom alpha))
      (Q.map (Polynomial.evalRingHom alpha)) m n).rank ≤
      (Polynomial.resultant P Q m n).rootMultiplicity alpha := by
  simpa only [Fintype.card_fin, Polynomial.resultant,
    ← Polynomial.sylvester_map_map] using
    corank_le_rootMultiplicity_det (Polynomial.sylvester P Q m n) alpha hresultant

/-- The summed coranks of specialized Sylvester matrices are bounded by
the actual degree of the nonzero resultant. -/
theorem sum_sylvester_coranks_le_resultant_natDegree
    (P Q : Polynomial (Polynomial K)) (m n : ℕ) (points : Finset K)
    (hresultant : Polynomial.resultant P Q m n ≠ 0) :
    (∑ alpha ∈ points, (m + n - (Polynomial.sylvester
      (P.map (Polynomial.evalRingHom alpha))
      (Q.map (Polynomial.evalRingHom alpha)) m n).rank)) ≤
      (Polynomial.resultant P Q m n).natDegree := by
  calc
    _ ≤ ∑ alpha ∈ points, (Polynomial.resultant P Q m n).rootMultiplicity alpha :=
      Finset.sum_le_sum fun alpha _ =>
        sylvester_corank_le_rootMultiplicity_resultant P Q m n alpha hresultant
    _ ≤ (Polynomial.resultant P Q m n).natDegree :=
      sum_rootMultiplicity_le_natDegree (Polynomial.resultant P Q m n) points


end
end ProximityPrize.SubmissionLower.MatrixRootMultiplicity

noncomputable section
namespace CurvatureSquares
open Polynomial Finset
open scoped Polynomial BigOperators
open ProximityPrize.SubmissionLower.MatrixRootMultiplicity

/-- The space of scalar multiples of a polynomial in a truncated degree box. -/
private def mulBox {L : Type} [Field L] (h : L[X]) (k n : ℕ)
    (fit : h≠0 → h.natDegree+k≤n) : degreeLT L k →ₗ[L] degreeLT L n where
  toFun u := ⟨h*(u:L[X]),by
    by_cases zero : h=0
    · simp [zero]
    by_cases uz : (u:L[X])=0
    · simp [uz]
    have hu := (natDegree_lt_iff_degree_lt uz).mpr (mem_degreeLT.mp u.2)
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero zero uz)).mp
    rw [natDegree_mul zero uz]; have := fit zero; omega⟩
  map_add' a b := by ext1; exact mul_add ..
  map_smul' a b := by ext1; exact mul_smul_comm ..

/-- A square factor leaves at most e degrees outside it. A simultaneous
degree drop at specialization counts toward the same corank. -/
theorem cofactor_corank {L : Type} [Field L] [DecidableEq L] (h t : L[X]) {r e : ℕ}
    (hr : 0<r) (dt : t.natDegree≤e) (fit : (h^2*t).natDegree≤r) :
    (r-e+1)/2 ≤ r+(r-1)-(sylvester (h^2*t) (h^2*t).derivative r (r-1)).rank := by
  classical
  let f:=h^2*t
  let g:=f.derivative
  by_cases zero : f=0
  · change _≤r+(r-1)-(sylvester f f.derivative r (r-1)).rank
    have hz : sylvester (0:L[X]) 0 r (r-1)=0 := by
      ext i j; cases j using Fin.addCases <;> simp [sylvester]
    rw [zero,derivative_zero,hz,Matrix.rank_zero]; omega
  have hn : h≠0 := fun h => zero (by simp [f,h])
  have tn : t≠0 := fun h => zero (by simp [f,h])
  let D:=h*t
  have dn : D≠0 := mul_ne_zero hn tn
  have df : f.natDegree=2*h.natDegree+t.natDegree := by
    rw [show f=h^2*t from rfl,natDegree_mul (pow_ne_zero _ hn) tn,natDegree_pow]
  have dD : D.natDegree=h.natDegree+t.natDegree := natDegree_mul hn tn
  let s:=D.natDegree
  let k:=r-s
  have ds : f.natDegree≤r := fit
  have gd : g.natDegree≤r-1 := (natDegree_derivative_le f).trans (Nat.sub_le_sub_right ds 1)
  have divides : h∣g := by
    refine ⟨2*h.derivative*t+h*t.derivative,?_⟩
    dsimp [f,g]; rw [derivative_mul,pow_two,derivative_mul]; ring
  obtain ⟨a,da⟩:=divides
  let S:=sylvesterMap f g ds gd
  let U:=mulBox D k r (fun _ => by dsimp [k,s]; omega)
  let V:=mulBox (-a) k (r-1) (fun ne => by
    have an : a≠0 := fun hz => ne (by simp [hz])
    have eq := natDegree_mul hn an
    rw [←da] at eq
    have gt : f.natDegree≠0 := by
      intro zz
      have zf : g=0 := by change f.derivative=0; conv_lhs => rw [eq_C_of_natDegree_eq_zero zz,derivative_C]
      exact (mul_ne_zero hn an) (da ▸ zf)
    have lt := natDegree_derivative_lt gt
    change g.natDegree<f.natDegree at lt
    rw [natDegree_neg]; dsimp [k,s]; omega)
  let lift:=U.prod V
  have inKer (u : degreeLT L k) : lift u∈LinearMap.ker S := by
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change f*((-a)*(u:L[X]))+g*(D*(u:L[X]))=0
    rw [da]; dsimp [f,D]; ring
  let Kmap:=lift.codRestrict (LinearMap.ker S) inKer
  have inject : Function.Injective Kmap := by
    intro x y hxy
    apply Subtype.ext
    exact mul_left_cancel₀ dn (congrArg (fun v : LinearMap.ker S => (v.val.1 : L[X])) hxy)
  have : FiniteDimensional L (degreeLT L r) := Module.Finite.of_basis (degreeLT.basis L r)
  have : FiniteDimensional L (degreeLT L (r-1)) := Module.Finite.of_basis (degreeLT.basis L (r-1))
  have hk := LinearMap.finrank_le_finrank_of_injective (f:=Kmap) inject
  have dim (q : ℕ) : Module.finrank L (degreeLT L q)=q := by
    simpa using Module.finrank_eq_card_basis (degreeLT.basis L q)
  rw [dim] at hk
  have rank := S.finrank_range_add_finrank_ker
  rw [Module.finrank_prod,dim,dim] at rank
  have eq : (sylvester f g r (r-1)).rank=Module.finrank L (LinearMap.range S) := by
    let dom := ((degreeLT.basis L r).prod (degreeLT.basis L (r-1))).reindex finSumFinEquiv
    rw [Matrix.rank_eq_finrank_range_toLin _ (degreeLT.basis L _) dom,
      ← toMatrix_sylvesterMap' f g ds gd, Matrix.toLin_toMatrix]
  change _ ≤ r+(r-1)-(sylvester f g r (r-1)).rank
  rw [eq]; dsimp [k,s] at hk; omega

theorem square_corank {L : Type} [Field L] [DecidableEq L] (h : L[X]) {r : ℕ}
    (hr : 0<r) (fit : (h^2).natDegree≤r) :
    (r+1)/2 ≤ r+(r-1)-(sylvester (h^2) (h^2).derivative r (r-1)).rank := by
  simpa using cofactor_corank (e:=0) h 1 hr (by simp) (by simpa using fit)

/-- A family of degree r in the abscissa has at most 4v square fibres,
where v is its coefficient degree in the parameter. -/
theorem square_fibres {L : Type} [Field L] [DecidableEq L]
    (Q : Polynomial L[X]) {r v : ℕ} (hr : 0<r) (d : Q.natDegree≤r)
    (seed : ∀ i,(Q.coeff i).natDegree≤v)
    (sep : Q.resultant Q.derivative r (r-1)≠0) (T : Finset L)
    (square : ∀ z∈T, ∃ h:L[X], Q.map (evalRingHom z)=h^2) :
    T.card≤4*v := by
  have each (z) (hz : z∈T) : (r+1)/2 ≤ r+(r-1)-
      (sylvester (Q.map (evalRingHom z)) (Q.derivative.map (evalRingHom z)) r (r-1)).rank := by
    obtain ⟨h,hh⟩ := square z hz
    have fit : (h^2).natDegree≤r := by rw [← hh]; exact natDegree_map_le.trans d
    have hcor := square_corank h hr fit
    rw [← hh,derivative_map] at hcor
    exact hcor
  have bound := Finset.sum_le_sum each
  simp only [sum_const,nsmul_eq_mul] at bound
  have upper := sum_sylvester_coranks_le_resultant_natDegree Q Q.derivative r (r-1) T sep
  have fee := Polynomial.natDegree_resultant_le_of_coeff_natDegree_le Q Q.derivative r (r-1) v v seed (fun i => by
    rw [coeff_derivative, mul_comm]
    rw [show ((i:L[X])+1)=C ((i:L)+1) by simp]
    exact (natDegree_C_mul_le ..).trans (seed _))
  have hh : T.card*((r+1)/2) ≤ r*v+(r-1)*v := (bound.trans upper).trans (fee.trans_eq (Nat.add_comm ..))
  have ceil : r≤2*((r+1)/2) := by omega
  have less : r-1≤r := Nat.sub_le _ _
  have a := Nat.mul_le_mul_left T.card ceil
  have b := Nat.mul_le_mul_right v less
  have rr : T.card*r≤4*v*r := by nlinarith only [a,b,hh]
  exact Nat.le_of_mul_le_mul_right rr hr
end CurvatureSquares
end

noncomputable section
namespace CurvatureSquares
open K1 K1_14 Polynomial Finset RetainedShortening CurvatureVotes
open scoped BigOperators Polynomial Classical
variable {F : Type} [Field F]

abbrev Bi (F : Type) [Field F] := Polynomial F[X]


def height (Q : Bi F) : ℕ := (Bivariate.swap Q).natDegree

theorem coeff_swap {R : Type} [CommRing R] (Q : Polynomial R[X]) (i j : ℕ) :
    ((Bivariate.swap Q).coeff i).coeff j=(Q.coeff j).coeff i := by
  induction Q using Polynomial.induction_on' with
  | add f g hf hg => simp [hf,hg]
  | monomial n a =>
    rw [Bivariate.swap_monomial,coeff_mul_C,coeff_map,C_mul_X_pow_eq_monomial]
    by_cases h : n=j <;> simp [coeff_monomial,h]

theorem coeff_height (Q : Bi F) (i : ℕ) : (Q.coeff i).natDegree≤height Q := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← coeff_swap Q, coeff_eq_zero_of_natDegree_lt hj, coeff_zero]


private theorem factor_height {A B : Bi F} (hn : A*B≠0) :
    height (A*B)=height A+height B := by
  have hA := left_ne_zero_of_mul hn
  have hB := right_ne_zero_of_mul hn
  unfold height
  rw [map_mul,natDegree_mul ((map_ne_zero_iff _ Bivariate.swap.injective).mpr hA)
    ((map_ne_zero_iff _ Bivariate.swap.injective).mpr hB)]

private theorem square_div {L : Type} [Field L] {x y : L[X]} (h : x^2 ∣ y^2) : x ∣ y :=
  (IsIntegrallyClosed.pow_dvd_pow_iff (by decide : (2:ℕ)≠0)).mp h

/-- A nonzero scalar-square factor in a polynomial fibre can be cancelled. -/
private theorem cancel_sq {L : Type} [Field L] [IsAlgClosed L]
    (c : L) (h w q : L[X]) (hc : c≠0) (hh : h≠0)
    (eq : C c*h^2*q=w^2) : ∃ s:L[X], q=s^2 := by
  obtain ⟨r,rc⟩ := IsAlgClosed.exists_pow_nat_eq (k:=L) c (n:=2) (by decide)
  have rn : r≠0 := by intro hz; simp [hz] at rc; exact hc rc.symm
  let D := C r*h
  have dn : D≠0 := mul_ne_zero (C_ne_zero.mpr rn) hh
  have sqD : D^2=C c*h^2 := by
    exact (mul_pow (C r) h 2).trans (by rw [← C_pow,rc])
  have he : D^2*q=w^2 := by rw [sqD]; exact eq
  have dv : D^2∣w^2 := ⟨q,he.symm⟩
  have divides : D∣w := square_div dv
  obtain ⟨v,hv⟩ := divides
  refine ⟨v,?_⟩
  have eq2 : D^2*q=D^2*v^2 := he.trans ((congrArg (fun x:L[X] => x^2) hv).trans (mul_pow D v 2))
  exact mul_left_cancel₀ (pow_ne_zero _ dn) eq2

/-- Strip a parameter-only factor and the entire polynomial square part before
charging the discriminant. Both vertical base loci and degree drops are included. -/
theorem squareclass_count {L : Type} [Field L] [IsAlgClosed L] [DecidableEq L]
    (D H R : Bi L) (c : L[X]) (hn : D≠0) (fac : D=C c*H^2*R)
    (hr : 0<R.natDegree) (sep : R.resultant R.derivative R.natDegree (R.natDegree-1)≠0)
    (T : Finset L) (marks : ∀ z∈T,∃ w:L[X],D.map (evalRingHom z)=w^2) :
    T.card≤4*height D := by
  classical
  have prod : C c*H^2*R≠0 := fac ▸ hn
  have hch := left_ne_zero_of_mul prod
  have hc : c≠0 := fun h => by simp [h] at hch
  have hH : H≠0 := fun h => by simp [h] at hch
  have qne : H.coeff H.natDegree≠0 := by rw [coeff_natDegree]; exact leadingCoeff_ne_zero.mpr hH
  let B := c*H.leadingCoeff
  have Bne : B≠0 := mul_ne_zero hc (by rwa [coeff_natDegree] at qne)
  let E := T.filter fun z => B.eval z=0
  have exc : E.card≤c.natDegree+height H := by
    have sub : E⊆B.roots.toFinset := by
      intro z hz
      exact Multiset.mem_toFinset.mpr ((mem_roots Bne).mpr (mem_filter.mp hz).2)
    have card := (card_le_card sub).trans ((Multiset.toFinset_card_le ..).trans (card_roots' B))
    have ch := coeff_height H H.natDegree
    rw [coeff_natDegree] at ch
    exact card.trans ((natDegree_mul_le (p:=c) (q:=H.leadingCoeff)).trans (Nat.add_le_add_left ch _))
  have reg := square_fibres R hr le_rfl (coeff_height R) sep (T \ E) (by
    intro z hz
    have hmem := (mem_sdiff.mp hz).1
    have be : B.eval z≠0 := fun h => (mem_sdiff.mp hz).2 (mem_filter.mpr ⟨hmem,h⟩)
    have cg : c.eval z≠0 ∧ H.leadingCoeff.eval z≠0 := by simpa [B] using be
    have hh : H.map (evalRingHom z)≠0 := by
      intro h
      have h' := congrArg (fun q:L[X] => q.coeff H.natDegree) h
      exact cg.2 (by simpa only [coeff_map,coeff_zero,coeff_natDegree,coe_evalRingHom] using h')
    obtain ⟨w,ew⟩ := marks z hmem
    rw [fac,Polynomial.map_mul,Polynomial.map_mul,Polynomial.map_pow,map_C] at ew
    exact cancel_sq _ _ w _ cg.1 hh ew)
  have hsq := factor_height (A:=H) (B:=H) (mul_ne_zero hH hH)
  rw [← pow_two] at hsq
  have tot : height D=c.natDegree+(height H+height H)+height R := by
    rw [fac,factor_height prod,factor_height hch,hsq]
    simp [height,Bivariate.swap_C,natDegree_map_eq_of_injective C_injective]
  have hcard := card_sdiff_add_card_eq_card (filter_subset (fun z => B.eval z=0) T)
  change (T \ E).card+E.card=T.card at hcard
  omega

private theorem root_count {ι : Type*} {S : Finset ι} {z : ι→F} (inj : Set.InjOn z (S:Set ι))
    (q : F[X]) (nz : q≠0) (van : ∀ i∈S,q.eval (z i)=0) : S.card ≤ q.natDegree := by
  classical
  have sub : S.image z⊆q.roots.toFinset := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (van _ hi))
  exact (card_image_of_injOn inj).symm ▸ (card_le_card sub).trans
    ((Multiset.toFinset_card_le ..).trans (card_roots' q))


/-- A square-free bivariate polynomial stays separable as an abscissa
polynomial whenever every nonvertical prime factor has nonzero X derivative. -/
theorem separable_kernel {L : Type} [Field L] (Q : Bi L) (sf : Squarefree Q)
    (tame : ∀ q : Bi L, Irreducible q → q∣Q → 0<q.natDegree → q.derivative≠0) :
    (Q.map (algebraMap L[X] (FractionRing L[X]))).Separable := by
  classical
  let ι:=algebraMap L[X] (FractionRing L[X])
  have inj : Function.Injective ι := IsFractionRing.injective _ _
  induction Q using WfDvdMonoid.induction_on_irreducible with
  | zero => exact False.elim (sf.ne_zero rfl)
  | unit u hu =>
    simpa using (separable_one (R:=FractionRing L[X])).unit_mul (hu.map (mapRingHom ι))
  | mul a q ha hq ih =>
    have facts := squarefree_mul_iff.mp sf
    have other := ih facts.2.2 (fun f irr dv => tame f irr (dv.trans (dvd_mul_left ..)))
    rw [Polynomial.map_mul]
    by_cases h0 : q.natDegree=0
    · have cc:=eq_C_of_natDegree_eq_zero h0
      have cpos : q.coeff 0≠0 := fun h => hq.ne_zero (by rw [cc,h,map_zero])
      rw [cc,map_C]
      exact other.unit_mul (isUnit_C.mpr ((map_ne_zero_iff _ inj).mpr cpos).isUnit)
    · have hp := hq.isPrimitive h0
      have ir := (hp.irreducible_iff_irreducible_map_fraction_map (K:=FractionRing L[X])).mp hq
      have deriv := tame q hq (dvd_mul_right ..) (Nat.pos_of_ne_zero h0)
      have sep : (q.map ι).Separable := (separable_iff_derivative_ne_zero ir).mpr (by
        rw [derivative_map]; exact (Polynomial.map_ne_zero_iff inj).mpr deriv)
      apply sep.mul other
      apply ir.coprime_iff_not_dvd.mpr
      intro divides
      have dv := hp.dvd_of_fraction_map_dvd_fraction_map divides
      exact hq.not_isUnit (facts.1 dvd_rfl dv)

/-- Factor out squares before evaluating the characteristic guard.
An inseparable, nonvertical odd prime is the sole unresolved case in this test. -/
theorem kernel_test {L : Type} [Field L] (disc : Bi L) :
    ∃ H R : Bi L, disc=H^2*R ∧ Squarefree R ∧
      (R.natDegree=0 ∨ (0<R.natDegree ∧ R.resultant R.derivative R.natDegree (R.natDegree-1)≠0) ∨
        ∃ q:Bi L, Irreducible q ∧ q∣R ∧ 0<q.natDegree ∧ q.derivative=0) := by
  classical
  obtain ⟨H,R,fac,sf⟩ := exists_sq_mul_squarefree disc
  refine ⟨H,R,fac.symm,sf,?_⟩
  by_cases h0 : R.natDegree=0
  · exact Or.inl h0
  right
  by_cases tame : ∀ q:Bi L, Irreducible q → q∣R → 0<q.natDegree → q.derivative≠0
  · left
    refine ⟨Nat.pos_of_ne_zero h0,?_⟩
    let ι:=algebraMap L[X] (FractionRing L[X])
    have inj : Function.Injective ι:=IsFractionRing.injective _ _
    have sep:=separable_kernel R sf tame
    have hres:=Polynomial.resultant_derivative_ne_zero_of_separable _ sep
    rw [natDegree_map_eq_of_injective inj,derivative_map,Polynomial.resultant_map_map] at hres
    exact fun h => hres (by rw [h,map_zero])
  · push Not at tame
    exact Or.inr tame


abbrev Ordinate := Polynomial (Bi K1_14.L)
abbrev Slope := Polynomial Ordinate

/-- Reorder variables to make each finite budget a univariate degree. -/
def xView : Ordinate →+* Ordinate := Bivariate.swap.toRingHom
def zView : Ordinate →+* Ordinate :=
  Bivariate.swap.toRingHom.comp (mapRingHom Bivariate.swap.toRingHom)

theorem xView_inj : Function.Injective xView := Bivariate.swap.injective
theorem zView_inj : Function.Injective zView :=
  Bivariate.swap.injective.comp (Polynomial.map_injective _ Bivariate.swap.injective)

private theorem inner_degree {R : Type} [CommRing R] (Q : Polynomial R[X]) (i : ℕ) :
    (Q.coeff i).natDegree ≤ (Bivariate.swap Q).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [← coeff_swap Q,coeff_eq_zero_of_natDegree_lt hj,coeff_zero]

theorem coeff_caps (Q : Ordinate) (i : ℕ) :
    (Q.coeff i).natDegree≤(xView Q).natDegree ∧ height (Q.coeff i)≤(zView Q).natDegree := by
  refine ⟨inner_degree Q i,?_⟩
  have h:=inner_degree (Q.map (Bivariate.swap (R:=K1_14.L)).toRingHom) i
  rw [coeff_map] at h
  exact h

def ordEval (z : K1_14.L) (y : K1_14.L[X]) : Ordinate →+* K1_14.L[X] :=
  eval₂RingHom (mapRingHom (evalRingHom z)) y

private theorem native_quad (f : Ordinate) (hf : f.natDegree=2) :
    f=C (f.coeff 2)*Polynomial.X^2+C (f.coeff 1)*Polynomial.X+C (f.coeff 0) := by
  have e:=f.as_sum_range_C_mul_X_pow' (n:=3) (by omega)
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one] at e
  exact e.trans (by ac_rfl)

private theorem no_square (f : Ordinate) (irr : Irreducible f) (hf : f.natDegree=2)
    (two : (2:Bi L)≠0) (h : Bi L) :
    f.coeff 1^2-4*f.coeff 2*f.coeff 0≠h^2 := by
  intro sqr
  let a:=f.coeff 2
  let b:=f.coeff 1
  have an : a≠0 := by simpa [a,← hf] using leadingCoeff_ne_zero.mpr irr.ne_zero
  let B : Ordinate:=C (2*a)*Polynomial.X+C b
  have identity : (B-C h)*(B+C h) = f*C (4*a) := by
    conv_rhs => rw [native_quad f hf]
    have he:=congrArg (C : Bi L→+*Ordinate) sqr
    simp only [map_sub,map_pow,map_mul,map_ofNat] at he
    rw [show (B-C h)*(B+C h)=B^2-(C h)^2 by ring,←he]
    dsimp only [B,a,b]
    simp only [map_mul,map_ofNat]
    ring
  have pr : Prime f:=UniqueFactorizationMonoid.irreducible_iff_prime.mp irr
  have div:=pr.dvd_mul.mp (show f∣(B-C h)*(B+C h) from ⟨C (4*a),identity⟩)
  have deg (t : Bi L) : (C (2*a)*Polynomial.X+C t).natDegree=1 := by
    exact natDegree_linear (mul_ne_zero two an)
  rcases div with d|d
  · have e : B-C h=C (2*a)*Polynomial.X+C (b-h) := by simp [B,map_sub]; ring
    rw [e] at d
    have one:=deg (b-h)
    have ne : C (2*a)*Polynomial.X+C (b-h)≠0 := fun Hz => by rw [Hz,natDegree_zero] at one; contradiction
    have := natDegree_le_of_dvd d ne
    omega
  · have e : B+C h=C (2*a)*Polynomial.X+C (b+h) := by simp [B,map_add,add_assoc]
    rw [e] at d
    have one:=deg (b+h)
    have ne : C (2*a)*Polynomial.X+C (b+h)≠0 := fun Hz => by rw [Hz,natDegree_zero] at one; contradiction
    have := natDegree_le_of_dvd d ne
    omega

private theorem node_ne (f : Ordinate) (irr : Irreducible f) (pos : 0<f.natDegree) (x : L) :
    f.map (evalRingHom (C x))≠0 := by
  intro zero
  let q : Bi L:=Polynomial.X-C (C x)
  have d : C q∣f := (C_dvd_iff_dvd_coeff ..).mpr (fun i => by
    change Polynomial.X-C (C x)∣f.coeff i
    apply (dvd_iff_isRoot (p:=f.coeff i)).mpr
    have hz:=congrArg (fun g:Polynomial L[X] => g.coeff i) zero
    change (f.coeff i).eval (C x)=0
    simpa only [coeff_map,coe_evalRingHom,coeff_zero] using hz)
  obtain ⟨g,eqn⟩:=d
  have nu : ¬IsUnit (C q : Ordinate) := by
    intro u
    have z:=natDegree_eq_zero_of_isUnit (isUnit_C.mp u)
    simp [q] at z
  have gu:=(irr.isUnit_or_isUnit eqn).resolve_left nu
  have h:=natDegree_mul_le (p:=C q) (q:=g)
  rw [←eqn,natDegree_C,natDegree_eq_zero_of_isUnit gu] at h
  omega

private theorem node_height (q : Bi L) (x : L) : (q.eval (C x)).natDegree≤height q := by
  rw [eval_eq_sum,sum_def]
  apply (natDegree_sum_le ..).trans
  apply Finset.sup_le
  intro i _
  change ((q.coeff i)*C x^i).natDegree≤_
  rw [← C_pow]
  exact (natDegree_mul_C_le ..).trans (coeff_height q i)

private theorem node_eval (q : Bi L) (x z : L) :
    (q.eval (C x)).eval z=(q.map (evalRingHom z)).eval x := by
  have e:=eval₂_hom (p:=q) (evalRingHom z) (C x)
  simpa only [coe_evalRingHom,eval_C,eval_map] using e.symm

/-- An irreducible quadratic with discriminant c(z)H(X,z)^2 has at most
five times its label degree plus one marks at the 70.00 vote rate. A node
with a generic received root has a double received root. -/
theorem irreducible_constant_node {A d w s T} (W : Word A d w s T)
    (φ : K →+* L) (z : K→L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (f : Ordinate) (irr : Irreducible f)
    (hf : f.natDegree=2) (two : (2:Bi L)≠0) (c : L[X]) (h : Bi L)
    (disc : f.coeff 1^2-4*f.coeff 2*f.coeff 0=C c*h^2)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) f=0) :
    T.card≤k*(zView f).natDegree+1 := by
  classical
  have ns : ¬∃ t:L[X],c=t^2 := by
    rintro ⟨t,ht⟩
    apply no_square f irr hf two (C t*h)
    rw [disc,ht,map_pow,mul_pow]
  apply minority_count W hd scale
  intro i
  let x:=φ (node i)
  let a:=C (φ (w i))
  let g (n:ℕ):=(f.coeff n).eval (C x)
  let q:=g 2*a^2+g 1*a+g 0
  have height_g (n:ℕ) : (g n).natDegree≤(zView f).natDegree :=
    (node_height ..).trans (coeff_caps f n).2
  have qd : q.natDegree≤(zView f).natDegree := by
    change (g 2*C (φ (w i))^2+g 1*C (φ (w i))+g 0).natDegree≤_
    rw [←C_pow]
    exact (natDegree_add_le ..).trans (max_le ((natDegree_add_le ..).trans
      (max_le ((natDegree_mul_C_le ..).trans (height_g 2)) ((natDegree_mul_C_le ..).trans (height_g 1)))) (height_g 0))
  have eqn (γ) (mem : γ∈T) : (g 2).eval (z γ)*(φ ((s γ).eval (node i)))^2+
      (g 1).eval (z γ)*(φ ((s γ).eval (node i)))+(g 0).eval (z γ)=0 := by
    have e:=marks γ mem
    rw [native_quad f hf] at e
    simp only [map_add,map_mul,map_pow,ordEval,coe_eval₂RingHom,eval₂_C,eval₂_X] at e
    have atx:=congrArg (eval x) e
    simpa only [g,node_eval,eval_add,eval_mul,eval_pow,eval_zero,eval_map_apply,x,
      coe_mapRingHom] using atx
  by_cases proper : q≠0
  · left
    apply (root_count (inj.mono (filter_subset _ _)) q proper _).trans qd
    intro γ mem
    obtain ⟨hm,hit⟩:=mem_filter.mp mem
    simpa [q,a,hit] using eqn γ hm
  · have zero : q=0:=not_ne_iff.mp proper
    have dx := congrArg (eval (C x)) disc
    simp only [eval_sub,eval_pow,eval_mul,eval_ofNat,eval_C] at dx
    change g 1^2-4*g 2*g 0=c*(h.eval (C x))^2 at dx
    have sq : (2*g 2*a+g 1)^2=c*(h.eval (C x))^2 := by
      change g 2*a^2+g 1*a+g 0=0 at zero
      linear_combination dx + 4*g 2*zero
    have hzero : h.eval (C x)=0 := by
      by_contra hn
      have dv : (h.eval (C x))^2∣(2*g 2*a+g 1)^2 := ⟨c,by rw [sq,mul_comm]⟩
      obtain ⟨t,ht⟩:=(IsIntegrallyClosed.pow_dvd_pow_iff (by decide : (2:ℕ)≠0)).mp dv
      apply ns
      exact ⟨t,mul_left_cancel₀ (pow_ne_zero 2 hn) (by rw [←mul_pow,←ht,sq,mul_comm])⟩
    have root : 2*g 2*a+g 1=0 := by simpa [hzero] using sq
    have gn : g 2≠0 := by
      intro h2
      have h1 : g 1=0 := by simpa [h2] using root
      have h0 : g 0=0 := by simpa [q,h2,h1] using zero
      apply node_ne f irr (by omega) x
      rw [native_quad f hf]
      change (f.coeff 2).eval (C x)=0 at h2
      change (f.coeff 1).eval (C x)=0 at h1
      change (f.coeff 0).eval (C x)=0 at h0
      simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,map_C,map_X,coe_evalRingHom,
        h2,h1,h0,map_zero,zero_mul,zero_add]
    right
    apply (root_count (inj.mono (filter_subset _ _)) (g 2) gn _).trans (height_g 2)
    intro γ mem
    obtain ⟨hm,miss⟩:=mem_filter.mp mem
    have e:=eqn γ hm
    have ez:=congrArg (eval (z γ)) zero
    have er:=congrArg (eval (z γ)) root
    simp only [q,a,eval_add,eval_mul,eval_pow,eval_C,eval_ofNat,eval_zero] at ez er
    have val : (g 2).eval (z γ)*(φ ((s γ).eval (node i))-φ (w i))^2=0 := by
      linear_combination e - ez - (φ ((s γ).eval (node i))-φ (w i))*er
    exact (mul_eq_zero.mp val).resolve_right (pow_ne_zero _ (sub_ne_zero.mpr (φ.injective.ne miss)))

/-- The alternative is exactly an odd inseparable abscissa prime. Both
square classes use the original marked ordinate polynomial. -/
theorem irreducible_quadratic_chart {A d w s T} (W : Word A d w s T)
    (φ : K →+* L) (z : K→L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (f : Ordinate) (irr : Irreducible f)
    (hf : f.natDegree=2) (two : (2:Bi L)≠0)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) f=0) :
    T.card≤max 8 k*(zView f).natDegree+1 ∨
      let Δ:=f.coeff 1^2-4*f.coeff 2*f.coeff 0
      Δ≠0 ∧ ∃ H R q : Bi L, Δ=H^2*R ∧ Squarefree R ∧ Irreducible q ∧ q∣R ∧
        0<q.natDegree ∧ q.derivative=0 := by
  classical
  let Δ:=f.coeff 1^2-4*f.coeff 2*f.coeff 0
  have nz : Δ≠0 := by simpa [Δ] using no_square f irr hf two 0
  obtain ⟨H,R,fac,sf,test⟩:=kernel_test Δ
  rcases test with vert|sep|wild
  · left
    have eqn : Δ=C (R.coeff 0)*H^2 := by
      calc Δ = H^2*R := fac
           _ = C (R.coeff 0)*H^2 := by conv_lhs => rw [eq_C_of_natDegree_eq_zero vert]; rw [mul_comm]
    have h:=irreducible_constant_node W φ z inj hd scale f irr hf two _ _ eqn marks
    exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (le_max_right 8 k)) 1)
  · left
    have weight : height Δ≤2*(zView f).natDegree := by
      unfold Δ height
      simp only [map_sub,map_pow,map_mul,map_ofNat]
      apply (natDegree_sub_le ..).trans
      apply max_le
      · rw [natDegree_pow]; have := (coeff_caps f 1).2; unfold height at this; omega
      · have a:=natDegree_mul_le (p:=(4:Bi L)*Bivariate.swap (f.coeff 2)) (q:=Bivariate.swap (f.coeff 0))
        have b:=natDegree_mul_le (p:=(4:Bi L)) (q:=Bivariate.swap (f.coeff 2))
        rw [natDegree_ofNat] at b
        have h2:=(coeff_caps f 2).2
        have h0:=(coeff_caps f 0).2
        unfold height at h2 h0
        omega
    have count:=squareclass_count Δ H R 1 nz (by simpa using fac) sep.1 sep.2 (T.image z) (by
      intro x hx
      obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hx
      let m:=evalRingHom (z γ)
      let y:=(s γ).map φ
      have e:=marks γ hγ
      rw [native_quad f hf] at e
      simp only [map_add,map_mul,map_pow,ordEval,coe_eval₂RingHom,eval₂_C,eval₂_X,coe_mapRingHom] at e
      refine ⟨2*((f.coeff 2).map m)*y+(f.coeff 1).map m,?_⟩
      simp only [Δ,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_ofNat]
      dsimp only [m,y]
      linear_combination -4*((f.coeff 2).map (evalRingHom (z γ)))*e)
    rw [card_image_of_injOn inj] at count
    exact (count.trans (Nat.mul_le_mul_left 4 weight)).trans (by
      have h:=Nat.mul_le_mul_right (zView f).natDegree (le_max_left 8 k)
      omega)
  · exact Or.inr ⟨nz,H,R,wild.choose,fac,sf,wild.choose_spec⟩
/-- On a linear component the specialized equation detects hits or misses
at each physical node with one polynomial of the original label degree. -/
theorem irreducible_linear_node {A d w s T} (W : Word A d w s T)
    (φ : K →+* L) (z : K→L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (f : Ordinate) (irr : Irreducible f)
    (hf : f.natDegree=1) (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) f=0) :
    T.card≤k*(zView f).natDegree+1 := by
  classical
  apply minority_count W hd scale
  intro i
  let x:=φ (node i)
  let g (n:ℕ):=(f.coeff n).eval (C x)
  let q:=g 1*C (φ (w i))+g 0
  have cap (n:ℕ) : (g n).natDegree≤(zView f).natDegree := (node_height ..).trans (coeff_caps f n).2
  have eqn (γ) (hm : γ∈T) : (g 1).eval (z γ)*φ ((s γ).eval (node i))+(g 0).eval (z γ)=0 := by
    have e:=marks γ hm
    rw [eq_X_add_C_of_natDegree_le_one hf.le] at e
    simp only [map_add,map_mul,ordEval,coe_eval₂RingHom,eval₂_C,eval₂_X,coe_mapRingHom] at e
    simpa only [g,node_eval,eval_add,eval_mul,eval_zero,x,eval_map_apply] using congrArg (eval x) e
  by_cases proper : q≠0
  · left
    apply (root_count (inj.mono (filter_subset _ _)) q proper _).trans
        ((natDegree_add_le ..).trans (max_le ((natDegree_mul_C_le ..).trans (cap 1)) (cap 0)))
    intro γ mem
    obtain ⟨hm,hit⟩:=mem_filter.mp mem
    simpa [q,hit] using eqn γ hm
  · right
    have zero:=not_ne_iff.mp proper
    have nz : g 1≠0 := by
      intro ho
      have hz : g 0=0 := by simpa [q,ho] using zero
      apply node_ne f irr (by omega) x
      rw [eq_X_add_C_of_natDegree_le_one hf.le]
      change (f.coeff 1).eval (C x)=0 at ho
      change (f.coeff 0).eval (C x)=0 at hz
      simp only [Polynomial.map_add,Polynomial.map_mul,map_C,map_X,coe_evalRingHom,
        ho,hz,map_zero,zero_mul,zero_add]
    apply (root_count (inj.mono (filter_subset _ _)) (g 1) nz _).trans (cap 1)
    intro γ mem
    obtain ⟨hm,miss⟩:=mem_filter.mp mem
    have ez:=congrArg (eval (z γ)) zero
    simp only [q,eval_add,eval_mul,eval_C,eval_zero] at ez
    have h : (g 1).eval (z γ)*(φ ((s γ).eval (node i))-φ (w i))=0 := by
      linear_combination eqn γ hm - ez
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr (φ.injective.ne miss))

variable {E : Type*} [Field E]

theorem derivative_ne_zero_of_natDegree_pos_lt_char
    (p : ℕ) [CharP E p] (f : E[X])
    (hpos : 0 < f.natDegree) (hlt : f.natDegree < p) : f.derivative ≠ 0 := by
  intro hzero
  have hf : f ≠ 0 := by
    intro heq
    simp [heq] at hpos
  have hn : f.natDegree - 1 + 1 = f.natDegree := by omega
  have hcoeff : f.coeff f.natDegree * (f.natDegree : E) = 0 := by
    have heq := congrArg (fun q : E[X] ↦ q.coeff (f.natDegree - 1)) hzero
    simpa only [coeff_derivative, coeff_zero, ← Nat.cast_add_one, hn] using heq
  have hlead : f.coeff f.natDegree ≠ 0 := by
    simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hf
  have hcast : (f.natDegree : E) ≠ 0 := by
    intro hz
    have hdiv : p ∣ f.natDegree := (CharP.cast_eq_zero_iff E p _).mp hz
    have hd : f.natDegree = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
    omega
  exact (mul_ne_zero hlead hcast) hcoeff


private theorem degree_two_count {A d w s T} (W : Word A d w s T)
    (φ : K →+* K1_14.L) (z : K→K1_14.L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k)
    (F : Ordinate) (irr : Irreducible F) (deg : F.natDegree=2) (tame : 2*(xView F).natDegree<p)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) F=0) :
    T.card≤max 8 k*(zView F).natDegree+2 := by
  have two : (2:K1_14.L)≠0 := by
    have h : ((2:ℕ):K)≠0 := fun a => (by decide : ¬p∣2) ((CharP.cast_eq_zero_iff K p 2).mp a)
    have hn : (2:K)≠0 := by exact_mod_cast h
    simpa only [map_ofNat,map_zero] using φ.injective.ne hn
  have large : (2:Bi K1_14.L)≠0 := by
    simpa only [map_ofNat] using (C_ne_zero.mpr (C_ne_zero.mpr two))
  have alt:=irreducible_quadratic_chart W φ z inj hd scale F irr deg large marks
  apply (alt.resolve_right ?_).trans (by omega)
  rintro ⟨nonzero,H,R,q,fac,_,_,div,pos,dzero⟩
  have small := natDegree_le_of_dvd (div.trans (fac ▸ dvd_mul_left ..)) nonzero
  have bound : (F.coeff 1^2-4*F.coeff 2*F.coeff 0).natDegree≤2*(xView F).natDegree := by
    apply (natDegree_sub_le ..).trans
    apply max_le
    · rw [natDegree_pow]; have := (coeff_caps F 1).1; omega
    · have h:=natDegree_mul_le (p:=(4:Bi K1_14.L)*F.coeff 2) (q:=F.coeff 0)
      have h':=natDegree_mul_le (p:=(4:Bi K1_14.L)) (q:=F.coeff 2)
      rw [natDegree_ofNat] at h'
      have := (coeff_caps F 2).1; have := (coeff_caps F 0).1; omega
  let ι:=algebraMap K1_14.L[X] (FractionRing K1_14.L[X])
  let : CharP (FractionRing K1_14.L[X]) p := charP_of_injective_ringHom
    ((ι.comp Polynomial.C).comp φ).injective p
  have eq:= natDegree_map_eq_of_injective (IsFractionRing.injective K1_14.L[X] (FractionRing K1_14.L[X])) q
  exact derivative_ne_zero_of_natDegree_pos_lt_char p (q.map ι)
    (eq ▸ pos) (eq ▸ (small.trans bound).trans_lt tame) (by rw [derivative_map,dzero,Polynomial.map_zero])

private theorem low_factor {A d w s T} (W : Word A d w s T)
    (φ : K →+* K1_14.L) (z : K→K1_14.L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k)
    (F : Ordinate) (irr : Irreducible F) (deg : F.natDegree≤2) (tame : 2*(xView F).natDegree<p)
    (marks : ∀ γ∈T,ordEval (z γ) ((s γ).map φ) F=0) :
    T.card≤(max 8 k)*(zView F).natDegree+2*F.natDegree := by
  have nz:=irr.ne_zero
  by_cases zero : F.natDegree=0
  · have cn : F.coeff 0≠0 := by simpa only [← coeff_natDegree,zero] using leadingCoeff_ne_zero.mpr nz
    have hn:=leadingCoeff_ne_zero.mpr cn
    let P:=(F.coeff 0).leadingCoeff
    have dz : P.natDegree≤(zView F).natDegree := by
      apply le_trans _ (coeff_caps F 0).2
      simpa only [P,← coeff_natDegree] using coeff_height (F.coeff 0) (F.coeff 0).natDegree
    have sub : T.image z ⊆ P.roots.toFinset := by
      intro x hx
      obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hx
      apply Multiset.mem_toFinset.mpr ((mem_roots hn).mpr ?_)
      have m:=marks γ hγ
      rw [eq_C_of_natDegree_eq_zero zero] at m
      simp only [ordEval,coe_eval₂RingHom,eval₂_C,coe_mapRingHom] at m
      have hc:=congrArg (fun b : K1_14.L[X] => b.coeff (F.coeff 0).natDegree) m
      simpa only [coeff_map,coe_evalRingHom,coeff_natDegree,coeff_zero,P,IsRoot] using hc
    have h:=(card_le_card sub).trans ((Multiset.toFinset_card_le ..).trans (card_roots' P))
    rw [card_image_of_injOn inj] at h
    have le:=Nat.mul_le_mul_right (zView F).natDegree (show 1≤max 8 k by omega)
    exact (h.trans dz).trans (by omega)
  by_cases two : F.natDegree=2
  · have h:=degree_two_count W φ z inj hd scale F irr two tame marks; omega
  have one : F.natDegree=1 := by omega
  have h:=irreducible_linear_node W φ z inj hd scale F irr one marks
  have c:=Nat.mul_le_mul_right (zView F).natDegree (le_max_right 8 k)
  omega

/-- All labels covered by constant, linear or quadratic ordinate factors of
one nonzero projected polynomial. Both degree budgets are shared before
factorization; the theorem itself selects and prices the factors. -/
theorem projected_low_count {A d w s T} (W : Word A d w s T)
    (φ : K →+* K1_14.L) (z : K→K1_14.L) (inj : Set.InjOn z (T:Set K)) {k : ℕ}
    (hd : d<A) (scale : VoteScale A d k) (P : Ordinate) :
    P≠0 → 2*(xView P).natDegree<p →
    (∀ γ∈T,∃ f:Ordinate, Irreducible f ∧ f∣P ∧ f.natDegree≤2 ∧ ordEval (z γ) ((s γ).map φ) f=0) →
    T.card≤(max 8 k)*(zView P).natDegree+2*P.natDegree := by
  classical
  induction P using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit P unit =>
    intro _ _ cov
    have emp : T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ; obtain ⟨f,irr,dv,_⟩:=cov γ hγ
      exact irr.not_isUnit (isUnit_of_dvd_unit dv unit)
    simp [emp]
  | mul a q ha irr ih =>
    intro _ tame cov
    let U:=T.filter (fun γ => ∃ f:Ordinate, Irreducible f ∧ f∣a ∧
      f.natDegree≤2 ∧ ordEval (z γ) ((s γ).map φ) f=0)
    have usub : U⊆T := filter_subset _ _
    have subword (V) (h : V⊆T) : Word A d w s V :=
      ⟨W.distinct.mono h,fun γ hm => W.degree γ (h hm),fun γ hm => W.hits γ (h hm)⟩
    have eqx : (xView (q*a)).natDegree=(xView q).natDegree+(xView a).natDegree := by
      rw [map_mul,natDegree_mul ((map_ne_zero_iff _ xView_inj).mpr irr.ne_zero) ((map_ne_zero_iff _ xView_inj).mpr ha)]
    rw [eqx] at tame
    have reg := ih (subword U usub) (inj.mono usub) ha (by omega) (fun γ h => (mem_filter.mp h).2)
    let V:=T \ U
    have vsub : V⊆T := sdiff_subset
    have rest (γ) (hγ : γ∈V) : q.natDegree≤2 ∧ ordEval (z γ) ((s γ).map φ) q=0 := by
      have mem:=vsub hγ
      obtain ⟨f,ir,dv,degree,zero⟩:=cov γ mem
      have fp : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp ir
      have fq : f∣q := (fp.dvd_mul.mp dv).resolve_right (fun fa =>
        (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨mem, f,ir,fa,degree,zero⟩))
      have assoc := ir.associated_of_dvd irr fq
      refine ⟨(natDegree_le_of_dvd assoc.symm.dvd ir.ne_zero).trans degree,?_⟩
      obtain ⟨b,hb⟩:=fq
      rw [hb,map_mul,zero,zero_mul]
    have rem : V.card≤(max 8 k)*(zView q).natDegree+2*q.natDegree := by
      obtain em|⟨γ,hγ⟩ := V.eq_empty_or_nonempty
      · simp [em]
      exact low_factor (subword V vsub) φ z (inj.mono vsub) hd scale q irr (rest _ hγ).1
        (by omega) (fun x hx => (rest x hx).2)
    have sc:=card_sdiff_add_card_eq_card usub
    change V.card+U.card=T.card at sc
    rw [map_mul,natDegree_mul ((map_ne_zero_iff _ zView_inj).mpr irr.ne_zero) ((map_ne_zero_iff _ zView_inj).mpr ha),
        natDegree_mul irr.ne_zero ha]
    nlinarith only [sc,reg,rem]


end CurvatureSquares
end
#print axioms CurvatureSquares.projected_low_count
