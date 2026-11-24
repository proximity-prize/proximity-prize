import ProximityPrize.SubmissionLower.R6960MarkedEvaluationNorm

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6960.MarkedEvaluation
open Polynomial Module Matrix Finset
open scoped Polynomial Matrix BigOperators

variable {k I J : Type} [Field k] [Fintype I] [DecidableEq I] [Fintype J]
local notation "F" => FractionRing (Polynomial k)
local notation "ι" => algebraMap (Polynomial k) F

/-- A k-independent family of meromorphic functions, in coordinates in its
generic scalar span. The polynomial right inverse constructs the primitive basis
from the original functions, preserving the possible simple finite poles.
The selected minor has degree at least the excess of column count over row rank. -/
theorem primitive_minor (M:Matrix I J F) (full:∃ pick:I↪J,(M.submatrix id pick).det≠0)
    (independent:LinearIndependent k M.col) :
    ∃ (Q:Matrix I J (Polynomial k)) (T:Matrix J I (Polynomial k)) (B:Matrix I I F) (pick:I↪J),
      Q*T=1 ∧ M=B*Q.map ι ∧ B=M*T.map ι ∧ (Q.submatrix id pick).det≠0 ∧
      Fintype.card J≤Fintype.card I+(Q.submatrix id pick).det.natDegree := by
  classical
  obtain ⟨Q,T,B,d,idQ,represent,degrees,lead⟩:=
    P1_7_1_1_2.exists_reduced_rows M (P1_7_1_1_2.exists_split_rows M full)
  obtain ⟨pick,nz,maximal⟩:=P1_7_1_1_2.exists_minor_of_degree_sum Q d degrees lead
  have back : B=M*T.map ι := by
    rw [represent,Matrix.mul_assoc,←Matrix.map_mul,idQ,Matrix.map_one _ (map_zero _) (map_one _),Matrix.mul_one]
  let V:=fun i=>degreeLT k (d i+1)
  let col (j:J) (i:I):V i:=⟨Q i j, by
    apply mem_degreeLT.mpr
    exact (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le (degrees i j)))⟩
  let coeff (i:I) : V i→ₗ[k]F :=
    (IsScalarTower.toAlgHom k (Polynomial k) F).toLinearMap.comp (degreeLT k (d i+1)).subtype
  let values : (∀i,V i)→ₗ[k](I→F):=LinearMap.pi (fun i=>(coeff i).comp (LinearMap.proj i))
  let forward:=((Matrix.toLin' B).restrictScalars k).comp values
  have eq : forward ∘ col=M.col := by
    funext j i
    change (B*ᵥ(fun l=>ι (Q l j))) i=M i j
    rw [represent]; rfl
  have indep : LinearIndependent k col := LinearIndependent.of_comp forward (eq ▸ independent)
  let finite (i:I) : Module.Finite k (V i) := Module.Finite.of_basis (degreeLT.basis k (d i+1))
  have count:=indep.fintype_card_le_finrank
  have dim (i:I):finrank k (V i)=d i+1 := by simpa only [Fintype.card_fin] using finrank_eq_card_basis (degreeLT.basis k (d i+1))
  rw [Module.finrank_pi_fintype] at count
  simp only [dim,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,mul_one] at count
  exact ⟨Q,T,B,pick,idQ,represent,back,nz,by omega⟩

#print axioms primitive_minor
end Lower6960.MarkedEvaluation
