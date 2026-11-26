import ProximityPrize.SubmissionLower.R6966ProofWordSurfacePrice
import ArkLib.ToMathlib.RingTheory.MvPolynomial.Bidegree

set_option Elab.async false

namespace Research6966.WordUnconstrainedPrice
open Finset Module MvPolynomial WordSurfaceJets WordSurfaceInterpolation WordSurfaceMarks
variable {σ K ι I:Type*} [Fintype σ] [DecidableEq σ] [Field K] [Fintype I] [DecidableEq I] [Fintype ι]
noncomputable section
set_option maxHeartbeats 600000

private theorem low_shift (p:σ→K) (k:ℕ) (pos:0<k) (Q:low σ K k) (w:σ→ℕ) (hw:∀ j,w j≤1) :
    shift p Q.val ∈ restrictWeightAtMost w (k-1) := by
  have h:Q.val∈restrictWeightAtMost (fun _:σ=>1) (k-1) := by
    apply mem_restrictWeightAtMost.mpr
    intro e he
    have d:e.degree<k:=Q.property he
    have eq:e.weight (fun _:σ=>1)=e.degree:=by rw [Finsupp.degree_eq_weight_one]
    omega
  apply bind₁_mem_restrictWeightAtMost (w:=fun _:σ=>1) _ h
  intro i
  exact (restrictWeightAtMost w 1).add_mem (X_mem_restrictWeightAtMost _ _ (hw i))
    (C_mem_restrictWeightAtMost _ (Nat.zero_le 1) _)

private theorem sep_weight (p:ι→σ→K) (rows:I→Pol σ K) (A D:ℕ) (w:σ→ℕ)
    (h:∀ i,rows i∈restrictWeightAtMost w D) (enough:∀ x,A≤(hits (p x) rows).card) (x:ι) :
    separator p rows 1 x∈restrictWeightAtMost w ((Fintype.card I-A)*D) := by
  classical
  let miss:=univ\hits (p x) rows
  have count:miss.card≤Fintype.card I-A := by
    have sz:=card_sdiff_add_card_eq_card (subset_univ (hits (p x) rows))
    rw [card_univ] at sz;dsimp [miss];have:=enough x;omega
  have tot: (∑_i∈miss,D)≤(Fintype.card I-A)*D := by simpa using Nat.mul_le_mul_right D count
  change (∏i∈miss,rows i)^1∈_
  rw [pow_one]
  exact restrictWeightAtMost_mono _ tot (prod_mem_restrictWeightAtMost (w:=w) miss (a:=fun _=>D)
    (p:=rows) (fun i _=>h i))

private theorem separator_orders (p:ι→σ→K) (rows:I→Pol σ K) (A d:ℕ) (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    (∀ x,eval (p x) (separator p rows 1 x)≠0) ∧
      (∀ x y,x≠y → shift (p x) (separator p rows 1 y)∈high σ K (A-d)) := by
  have s:=separator_spec p rows (fun j=>∑i,(rows i).degreeOf j)
    (fun i j=>single_le_sum (fun u _=>Nat.zero_le ((rows u).degreeOf j)) (mem_univ i)) A d 1 enough shared
  simpa only [one_mul] using s.2

private theorem choose2 (k:ℕ) : (k+1).choose 2*2=k*(k+1) := by
  have eq:=Nat.choose_succ_right_eq (k+1) 1
  simpa only [Nat.choose_one_right,Nat.add_sub_cancel,Nat.mul_comm] using eq

private theorem choose3 (k:ℕ) : (k+2).choose 3*6=k*(k+1)*(k+2) := by
  have e:=Nat.choose_succ_right_eq (k+2) 2
  rw [Nat.add_sub_cancel] at e
  have b:=choose2 (k+1)
  nlinarith only [congrArg (·*2) e,congrArg (·*k) b]

/-- With a fixed initial value, the seed plane has one total-degree cap,
so its leading coefficient is half that of the two-axis rectangle. -/
theorem plane (p:ι→Fin 2→K) (rows:I→Pol (Fin 2) K) (h A d:ℕ) (gap:d<A)
    (height:∀ i,rows i∈restrictWeightAtMost (fun _=>1) h)
    (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    Fintype.card ι*(A-d)^2≤((Fintype.card I-A)*h+(A-d))^2 := by
  let k:=A-d
  let β:=(Fintype.card I-A)*h+k
  have kp:0<k:=by dsimp [k];omega
  have kb:k≤β:=Nat.le_add_left _ _
  obtain ⟨own,other⟩:=separator_orders p rows A d enough shared
  have onto:=interpolate_on p k (low (Fin 2) K β) (separator p rows 1) (by
    intro x Q
    have bound:=mul_mem_restrictWeightAtMost (sep_weight p rows A h (fun _=>1) height enough x)
      (low_shift (-(p x)) k kp Q (fun _=>1) (fun _=>le_rfl))
    intro e he
    have small:=mem_restrictWeightAtMost.mp bound e he
    change e.degree<β
    rw [Finsupp.degree_eq_weight_one]
    dsimp only [β];omega) own other
  have dim:=LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    (LinearEquiv.ofBijective _ (read_bijective (σ:=Fin 2) (K:=K) β)).finrank_eq] at dim
  have size (l:ℕ) (pos:0<l):finrank K (Local (Fin 2) K l)=(l+1).choose 2 := by
    obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero pos.ne'
    simpa only [Fintype.card_fin,show m+1+1=m+2 by omega] using local_dimension (σ:=Fin 2) (K:=K) m
  rw [size k kp,size β (kp.trans_le kb)] at dim
  have sides: Fintype.card ι*(k*(k+1))≤β*(β+1):=by
    have h:=Nat.mul_le_mul_right 2 dim
    rwa [Nat.mul_assoc,choose2,choose2] at h
  have scaled: (k+1)*(Fintype.card ι*k^2)≤(k+1)*β^2 := by
    nlinarith only [Nat.mul_le_mul_right k sides,Nat.mul_le_mul_right β kb]
  exact Nat.le_of_mul_le_mul_left scaled (Nat.succ_pos _)


private def ordinate : Option (Fin 2)→ℕ:=fun i=>i.elim 1 (fun _=>0)
private def seed : Option (Fin 2)→ℕ:=fun i=>i.elim 0 (fun _=>1)

private theorem bidegree {P:Pol (Option (Fin 2)) K} {a b:ℕ} :
    P∈restrictBidegree (Fin 2) K a b ↔
    P∈restrictWeightAtMost ordinate a ∧ P∈restrictWeightAtMost seed b := by
  rw [mem_restrictBidegree,mem_restrictWeightAtMost,mem_restrictWeightAtMost]
  change (∀ e∈P.support,e none≤a ∧ e.some.degree≤b) ↔
    (∀ e∈P.support,e.weight ordinate≤a) ∧ (∀ e∈P.support,e.weight seed≤b)
  have aeq (e:Option (Fin 2)→₀ℕ):e.weight ordinate=e none:=Finsupp.weight_elim_one_zero e
  have beq (e:Option (Fin 2)→₀ℕ):e.weight seed=e.some.degree:=Finsupp.weight_elim_zero_one e
  constructor
  · intro h
    exact ⟨fun e he=>(aeq e).le.trans (h e he).1,fun e he=>(beq e).le.trans (h e he).2⟩
  · rintro ⟨h,g⟩ e he
    exact ⟨(aeq e).ge.trans (h e he),(beq e).ge.trans (g e he)⟩

/-- The unrestricted affine family has one initial-value coordinate
and a common total degree for its two seeds. The coefficient three
comes from the bidegree dimension of that exact space. -/
theorem affine (p:ι→Option (Fin 2)→K) (rows:I→Pol (Option (Fin 2)) K) (y s A d:ℕ) (gap:d<A)
    (height:∀ i,rows i∈restrictBidegree (Fin 2) K y s)
    (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x z,x≠z → ((hits (p x) rows)∩(hits (p z) rows)).card≤d) :
    Fintype.card ι*(A-d)^3≤3*((Fintype.card I-A)*y+(A-d))*((Fintype.card I-A)*s+(A-d))^2 := by
  let k:=A-d
  let Y:=(Fintype.card I-A)*y+k
  let S:=(Fintype.card I-A)*s+k
  have kp:0<k:=by dsimp [k];omega
  have ky:k≤Y:=Nat.le_add_left _ _
  have ks:k≤S:=Nat.le_add_left _ _
  obtain ⟨own,other⟩:=separator_orders p rows A d enough shared
  have onto:=interpolate_on p k (restrictBidegree (Fin 2) K (Y-1) (S-1)) (separator p rows 1) (by
    intro x Q
    apply bidegree.mpr
    have first:=mul_mem_restrictWeightAtMost (sep_weight p rows A y ordinate (fun i=>(bidegree.mp (height i)).1) enough x)
      (low_shift (-(p x)) k kp Q ordinate (fun q=>by cases q <;> simp [ordinate]))
    have second:=mul_mem_restrictWeightAtMost (sep_weight p rows A s seed (fun i=>(bidegree.mp (height i)).2) enough x)
      (low_shift (-(p x)) k kp Q seed (fun q=>by cases q <;> simp [seed]))
    exact ⟨restrictWeightAtMost_mono _ (by dsimp only [Y];omega) first,
      restrictWeightAtMost_mono _ (by dsimp only [S];omega) second⟩) own other
  have dim:=LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,smul_eq_mul,finrank_restrictBidegree] at dim
  have localDim:finrank K (Local (Option (Fin 2)) K k)=(k+2).choose 3 := by
    have v:=local_dimension (σ:=Option (Fin 2)) (K:=K) (k-1)
    rw [Nat.sub_add_cancel kp,Fintype.card_option,Fintype.card_fin] at v
    rwa [show k-1+(2+1)=k+2 by omega] at v
  rw [localDim,Nat.card_fin,Nat.sub_add_cancel (kp.trans_le ky),show S-1+2=S+1 by omega] at dim
  have base:Fintype.card ι*(k*(k+1)*(k+2))≤3*Y*(S*(S+1)) := by
    nlinarith only [Nat.mul_le_mul_right 6 dim,congrArg (Fintype.card ι*·) (choose3 k),
      congrArg ((3*Y)*·) (choose2 S)]
  have cross:k*(S+1)≤S*(k+1):=by nlinarith only [ks]
  have ck:k^2*(S+1)≤S*(k+1)*(k+2):=by
    nlinarith only [Nat.mul_le_mul_left k cross,Nat.zero_le (S*(k+1))]
  have scaled:((k+1)*(k+2))*(Fintype.card ι*k^3)≤((k+1)*(k+2))*(3*Y*S^2):=by
    nlinarith only [Nat.mul_le_mul_right (k^2) base,Nat.mul_le_mul_left (3*Y*S) ck]
  exact Nat.le_of_mul_le_mul_left scaled (by positivity)


/-- Independent seed ceilings give the rectangular three-parameter
tariff. The common total-degree version above supplies the coefficient
three when the two seeds share their ceiling. -/
theorem three_axes (p:ι→Fin 3→K) (rows:I→Pol (Fin 3) K) (h:Fin 3→ℕ) (A d:ℕ) (gap:d<A)
    (height:∀ i j,(rows i).degreeOf j≤h j) (enough:∀ x,A≤(hits (p x) rows).card)
    (shared:∀ x y,x≠y → ((hits (p x) rows)∩(hits (p y) rows)).card≤d) :
    Fintype.card ι*(A-d)^3≤6*∏ j,WordSurfacePrice.side (Fintype.card I) A d (h j) := by
  classical
  let k:=A-d
  have pos:0<k:=by dsimp [k];omega
  obtain ⟨sep,cap,own,other⟩:=separators p rows h height A d 1 enough shared
  simp only [one_mul] at cap other
  have onto:=interpolate p k pos _ sep cap own other
  have rank:=LinearMap.finrank_le_finrank_of_surjective onto
  rw [Module.finrank_pi_fintype,sum_const,card_univ,smul_eq_mul,rectangle_dimension] at rank
  have dim:finrank K (Local (Fin 3) K k)=(k+2).choose 3 := by
    have b:=local_dimension (σ:=Fin 3) (K:=K) (k-1)
    rw [Nat.sub_add_cancel pos,Fintype.card_fin] at b
    rwa [show k-1+3=k+2 by omega] at b
  rw [dim] at rank
  have scale (j:Fin 3):(Fintype.card I-A)*h j+(k-1)+1=WordSurfacePrice.side (Fintype.card I) A d (h j) := by
    rw [Nat.add_assoc,Nat.sub_add_cancel pos];rfl
  simp_rw [scale] at rank
  have fact:=choose3 k
  have lower:k^3≤k*(k+1)*(k+2):=by nlinarith
  have rhs:=Nat.mul_le_mul_right 6 rank
  change Fintype.card ι*k^3≤_
  nlinarith only [rhs,congrArg (Fintype.card ι*·) fact,Nat.mul_le_mul_left (Fintype.card ι) lower]

end
end Research6966.WordUnconstrainedPrice
