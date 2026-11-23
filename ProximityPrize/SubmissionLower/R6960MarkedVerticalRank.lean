import ProximityPrize.SubmissionLower.R6960LineEulerCrossing

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000
namespace Lower6960.MarkedEvaluation
open LineEuler LaurentPolynomial Module Matrix Submodule Polynomial
open scoped Polynomial Matrix BigOperators
variable {k J:Type*} [Field k] [Fintype J] [DecidableEq J]

def twist (i:ℤ) (G:Matrix J J (Laurent k)) := (T (R:=k) i) • G
private theorem unit_twist (i:ℤ) {G:Matrix J J (Laurent k)} (unit:IsUnit G) : IsUnit (twist i G) := by
  rw [Matrix.isUnit_iff_isUnit_det,twist,Matrix.det_smul]
  exact ((isUnit_T i).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).mp unit)
private theorem neg_twist (i:ℤ) (G:Matrix J J (Laurent k)) : negativeTwist (twist i G)=twist (i-1) G := by
  rw [negativeTwist,twist,smul_smul,←T_add]
  rw [show -1+i=i-1 by omega];rfl

private theorem upper_map (A:Matrix J J k[X]) {v:J→Laurent k} (hv:v∈upperLattice k J 0) :
    (A.map (infinityEmbedding (k:=k)))*ᵥv ∈ upperLattice k J 0 := by
  rw [←range_shiftVector] at hv ⊢
  obtain ⟨p,rfl⟩:=hv
  refine ⟨A*ᵥp,funext (fun i=>?_)⟩
  simp only [shiftVector_apply,Nat.cast_zero,T_zero,one_mul,Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply]

private theorem inclusion (G:Matrix J J (Laurent k)) :
    transitionLattice (negativeTwist G)≤transitionLattice G := by
  rintro _ ⟨v,hv,rfl⟩
  let A:Matrix J J k[X]:=(Polynomial.X : k[X]) • (1:Matrix J J k[X])
  have mat : A.map (infinityEmbedding (k:=k))=T (R:=k) (-1) • (1:Matrix J J (Laurent k)) := by
    ext i j; by_cases eq:i=j <;> simp [A,Matrix.map_apply,Matrix.one_apply,eq,infinityEmbedding_apply,invert_T,smul_eq_mul]
  have trans : negativeTwist G=G*(A.map (infinityEmbedding (k:=k))) := by rw [mat,mul_smul_comm,mul_one]; rfl
  refine ⟨_,upper_map A hv,?_⟩
  change G*ᵥ(_*ᵥv)=(negativeTwist G)*ᵥv
  rw [Matrix.mulVec_mulVec,trans]

private theorem rank_mono (G:Matrix J J (Laurent k)) :
    finrank k (crossingEval (negativeTwist G)).range ≤ finrank k (crossingEval G).range := by
  have le:(crossingEval (negativeTwist G)).range≤(crossingEval G).range := by
    rintro _ ⟨v,rfl⟩; exact ⟨⟨v,⟨v.property.1,inclusion G v.property.2⟩⟩,rfl⟩
  exact Submodule.finrank_mono le

/-- Clear the inverse transition. Beyond this twist even the complete ordinary
infinity lattice is contained in the shifted chart image. -/
private theorem high_zero (G:Matrix J J (Laurent k)) (unit:IsUnit G) :
    ∃ N:ℕ,finrank k (H1 (twist (N:ℤ) G))=0 := by
  obtain ⟨g,hg⟩:=unit
  obtain ⟨N,A,clear⟩:=clear_transition (↑g⁻¹:Matrix J J (Laurent k))
  have prod : twist N G * A.map (infinityEmbedding (k:=k))=1 := by
    rw [twist,smul_mul_assoc,←mul_smul_comm,←clear,←hg,Units.mul_inv]
  have le:upperLattice k J 0≤transitionLattice (twist N G) := by
    intro v hv
    refine ⟨_,upper_map A hv,?_⟩
    change (twist (N:ℤ) G)*ᵥ(_*ᵥv)=v
    rw [Matrix.mulVec_mulVec,prod,Matrix.one_mulVec]
  have top:finiteLattice k J⊔transitionLattice (twist N G)=⊤ :=
    top_unique ((finite_sup_upper (k:=k) (ι:=J) 0) ▸ sup_le_sup_left le _)
  refine ⟨N,?_⟩
  change finrank k ((J→Laurent k) ⧸ (finiteLattice k J⊔transitionLattice _))=0
  rw [top];exact Module.finrank_zero_of_subsingleton

/-- The exact point-rank recurrence consumes at least one dimension at each
nonzero step; full evaluation rank, once attained, persists thereafter. -/
private theorem countdown (h q:ℕ→ℕ) (step:∀n,h n=h (n+1)+q n) (decrease:Antitone q)
    (last:∃N,h N=0) : h (h 0)=0 := by
  have mono:Antitone h:=antitone_nat_of_succ_le (fun n=>by have :=step n; omega)
  have positive (n) (hn:0<h n) : 0<q n := by
    by_contra! no
    have stable (m): h (n+m)=h n := by
      induction m with
      | zero=>simp
      | succ m ih=>
        have s:=step (n+m)
        have cut:=decrease (show n≤n+m by omega)
        change h (n+m+1)=h n
        omega
    obtain ⟨N,zero⟩:=last
    have z:=mono (show N≤n+N by omega)
    rw [zero,stable] at z;omega
  have bound (n):h n≤h 0-n := by
    induction n with
    | zero=>simp
    | succ n ih=>
      have st:=step n
      by_cases nz:0<h n
      · have:=positive n nz; omega
      · omega
  have:=bound (h 0);omega

/-- For a degree-e finite line algebra with injective global point evaluation,
twisting by s-1 suffices at determinant deficit s. The generic section dimension
is then e*s-s. No splitting basis for the vector bundle is required. -/
theorem vertical_rank (G:Matrix J J (Laurent k)) (unit:IsUnit G) (s:ℕ)
    (deg:G.det.degree=((-(s:ℤ):ℤ):WithBot ℤ)) (inj:Function.Injective (crossingEval G)) :
    finrank k (H1 (twist ((s:ℤ)-1) G))=0 ∧
      finrank k (H0 (twist ((s:ℤ)-1) G))+s=Fintype.card J*s := by
  let h (n:ℕ):=finrank k (H1 (twist ((n:ℤ)-1) G))
  let q (n:ℕ):=Fintype.card J-finrank k (crossingEval (twist (n:ℤ) G)).range
  have st (n:ℕ) : h n=h (n+1)+q n := by
    have r:=crossing_rank (twist (n:ℤ) G) (unit_twist _ unit)
    rw [neg_twist] at r
    have le:=Submodule.finrank_le (crossingEval (twist (n:ℤ) G)).range
    rw [Module.finrank_pi] at le
    dsimp only [h,q]
    rw [show ((n+1:ℕ):ℤ)-1=(n:ℤ) by omega]
    omega
  have decr:Antitone q:=antitone_nat_of_succ_le (by
    intro (n:ℕ)
    have r:=rank_mono (twist ((n+1:ℕ):ℤ) G)
    rw [neg_twist,show ((n+1:ℕ):ℤ)-1=(n:ℤ) by omega] at r
    exact Nat.sub_le_sub_left r _)
  obtain ⟨N,last⟩:=high_zero G unit
  have z:=countdown h q st decr ⟨N+1,by dsimp only [h]; rwa [show ((N+1:ℕ):ℤ)-1=(N:ℤ) by omega]⟩
  obtain ⟨f0,f1,d,ed,chi⟩:=euler_index G unit
  have old:=crossing_rank G unit
  have rank := LinearMap.finrank_range_of_inj inj
  have g0:twist 0 G=G := by simp [twist]
  have neg:twist (-1) G=negativeTwist G := rfl
  have nd:=WithBot.coe_injective (ed.symm.trans deg)
  have start : h 0=s := by
    change finrank k (H1 (negativeTwist G))=s
    omega
  rw [start] at z
  change finrank k (H1 (twist ((s:ℤ)-1) G))=0 at z
  refine ⟨z,?_⟩
  obtain ⟨_,_,v,ev,idx⟩:=euler_index (twist ((s:ℤ)-1) G) (unit_twist _ unit)
  obtain ⟨c,p,cn,repr⟩:=unit_monomial G.det ((Matrix.isUnit_iff_isUnit_det G).mp unit)
  have pval:p= -(s:ℤ) := WithBot.coe_injective ((degree_C_mul_T _ _ cn).symm.trans (repr ▸ deg))
  have dt:(twist ((s:ℤ)-1) G).det=LaurentPolynomial.C c*T (((s:ℤ)-1)*Fintype.card J+p) := by
    rw [twist,Matrix.det_smul,repr,T_pow,mul_left_comm,←T_add];congr 2 <;> ring
  rw [dt,degree_C_mul_T _ _ cn] at ev
  have ev':((s:ℤ)-1)*Fintype.card J+p=v := WithBot.coe_injective ev
  rw [z,Nat.cast_zero,sub_zero,←ev',pval] at idx
  exact_mod_cast (show (finrank k (H0 (twist ((s:ℤ)-1) G)):ℤ)+s=(Fintype.card J:ℤ)*s by rw [idx];ring)

#print axioms vertical_rank
end Lower6960.MarkedEvaluation
