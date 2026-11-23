import ProximityPrize.SubmissionLower.KoalaCompression

/-! Weighted interpolation on actual marked rows. The output is the dimension
of the whole integral relation space, so it can be compared with all multiples
of an existing relation. -/
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace Lower6960.HeightCompression
open Polynomial Matrix
open scoped BigOperators Polynomial Matrix

variable {F : Type*} [Field F] {ι α : Type*} [Fintype ι]

abbrev Coeffs (F : Type*) [Field F] {ι : Type*} (weight : ι→ℕ) (width : ℕ) :=
  ∀ j,degreeLT F (width-weight j)

def evaluation (A : Matrix α ι F[X]) (weight : ι→ℕ) (width : ℕ) :
    Coeffs F weight width →ₗ[F] (α→F[X]) where
  toFun v i := ∑ j,A i j*(v j : F[X])
  map_add' v w := by funext i; simp [mul_add,Finset.sum_add_distrib]
  map_smul' c v := by funext i; simp [Finset.smul_sum]

/-- Each rational kernel direction frees a complete abscissa-width block.
The individual column weights are charged only once. -/
theorem weighted_kernel [Finite α] (A : Matrix α ι F[X]) (weight : ι→ℕ) (width : ℕ)
    (col : ∀ i j,(A i j).natDegree≤weight j) (k : ℕ)
    (ker : k≤Module.finrank (FractionRing F[X])
      (LinearMap.ker (A.map (algebraMap F[X] (FractionRing F[X]))).mulVecLin)) :
    (∑ j : ι, (width-weight j)) ≤ (Fintype.card ι-k)*width+
      Module.finrank F (LinearMap.ker (evaluation A weight width)) := by
  classical
  let E:=FractionRing F[X]
  let a:=algebraMap F[X] E
  let M:=A.map a
  let R:=Submodule.span E (Set.range M.row)
  let m:=Module.finrank E R
  have rank : m+Module.finrank E (LinearMap.ker M.mulVecLin)=Fintype.card ι := by
    have h:=M.mulVecLin.finrank_range_add_finrank_ker
    change M.rank+_= _ at h
    rw [M.rank_eq_finrank_span_row,Module.finrank_pi_fintype] at h
    simpa [m,R] using h
  have bound : m≤Fintype.card ι-k := by
    change k≤Module.finrank E (LinearMap.ker M.mulVecLin) at ker
    omega
  obtain ⟨B,mem,span,_⟩:=Submodule.exists_fun_fin_finrank_span_eq E (Set.range M.row)
  change Fin m → (ι→E) at B
  choose row hrow using mem
  have fits (v : Coeffs F weight width) (i : α) :
      (evaluation A weight width v i)∈degreeLT F width := by
    apply Submodule.sum_mem
    intro j _
    by_cases z : (v j : F[X])=0
    · simp [z]
    by_cases c : A i j=0
    · simp [c]
    apply mem_degreeLT.mpr
    apply (natDegree_lt_iff_degree_lt (mul_ne_zero c z)).mp
    have h:= (natDegree_lt_iff_degree_lt z).mpr (mem_degreeLT.mp (v j).property)
    have u:= (natDegree_mul_le (p:=A i j) (q:=(v j:F[X]))).trans (Nat.add_le_add_right (col i j) _)
    omega
  let small : Coeffs F weight width →ₗ[F] (Fin m → degreeLT F width) :=
    LinearMap.pi fun i => (((LinearMap.proj (row i)).comp (evaluation A weight width)).codRestrict
      (degreeLT F width) (fun v => fits v (row i)))
  have eq : LinearMap.ker small=LinearMap.ker (evaluation A weight width) := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv
      let ev : ι→E:=fun j=>a (v j : F[X])
      have hb (i : Fin m) : B i ⬝ᵥ ev=0 := by
        rw [←hrow i]
        have h:=congrArg (fun g : Fin m → degreeLT F width => (g i : F[X])) hv
        change (∑ j,A (row i) j*(v j : F[X]))=0 at h
        simpa [ev,M,Matrix.row,dotProduct] using congrArg a h
      funext i
      apply IsFractionRing.injective F[X] E
      have hi : M.row i∈Submodule.span E (Set.range B) := by
        rw [span]; exact Submodule.subset_span ⟨i,rfl⟩
      have zero : M.row i ⬝ᵥ ev=0 := by
        refine Submodule.span_induction (p:=fun x _=>x ⬝ᵥ ev=0) ?_ ?_ ?_ ?_ hi
        · rintro _ ⟨j,rfl⟩; exact hb j
        · exact zero_dotProduct _
        · intro x y _ _ hx hy; rw [add_dotProduct,hx,hy,add_zero]
        · intro c x _ hx; rw [smul_dotProduct,hx,smul_zero]
      simpa [evaluation,ev,M,Matrix.row,dotProduct] using zero
    · intro hv
      funext i
      apply Subtype.ext
      exact congrFun hv (row i)
  have source : Module.finrank F (Coeffs F weight width)=∑ j : ι, (width-weight j) := by
    simp [Coeffs,Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  have target : Module.finrank F (Fin m → degreeLT F width)=m*width := by
    simp [Module.finrank_pi_fintype,(degreeLTEquiv F _).finrank_eq]
  have size:=small.finrank_range_add_finrank_ker
  rw [source,eq] at size
  rw [←size]
  exact Nat.add_le_add_right ((Submodule.finrank_le ..).trans
    (target.le.trans (Nat.mul_le_mul_right _ bound))) _

#print axioms weighted_kernel
end Lower6960.HeightCompression
