import ProximityPrize.SubmissionLower.PoleActual
import ProximityPrize.SubmissionLower.HighSource6921Rank

set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 24
set_option maxHeartbeats 1200000

namespace PoleGlobal

open K1_14 (Shape)
open K1_14_1_7
open PoleActual
open scoped BigOperators Polynomial

open private poleTest_of_local from ProximityPrize.SubmissionLower.HighSource6921Rank

noncomputable section

def blockSum (s : Shape) : ℕ :=
  ∑ u : Fin (s.U+1), ∑ n : Fin (s.B+(s.U-u.val)+1), ∑ g : Fin (s.B+2*s.J),
    PoleFamily.blockBound ⟨u,n,g⟩

/-- The production matrix with pole-test kernel has rank at most the sum
of the normalized local image ranks at all distinct simple poles. -/
theorem simple_rank_le
    {F ι : Type} [Field F] [Fintype ι] {h : ℕ} {H : F[X]} {lift : (SeedFrac F)[X]}
    (G : SimplePoles h H lift) (ha : ∀ t, G.a t ≠ 0) (s : Shape)
    (P : ι → TrueSource F) (hP : ∀ i, Shaped s (P i))
    {n : ℕ} (M : Matrix (Fin n) ι F)
    (hM : ∀ v, M.mulVec v = 0 ↔ PoleTest s H lift (Fintype.linearCombination F P v)) :
    M.rank ≤ (2*h) * blockSum s := by
  classical
  let z : Fin (2*h) → SeedFrac F := fun t ↦ residue (G.side t) (G.a t) (G.b t) (G.c t)
  let poleMap : Fin (2*h) → TrueSource F →ₗ[F]
      (Target F) ⧸ PoleImage.CutIdeal (abscissa F) (s.B+s.J) :=
    fun t ↦ localMap s (G.root t) (z t)
  let S : Fin (2*h) → Submodule F ((Target F) ⧸ PoleImage.CutIdeal (abscissa F) (s.B+s.J)) :=
    fun t ↦ Submodule.span F (Set.range (poleMap t ∘ P))
  let comb := Fintype.linearCombination F P
  let (t : Fin (2*h)) : Module.Finite F (S t) :=
    Module.Finite.span_of_finite F (Set.finite_range (poleMap t ∘ P))
  let (_t : Fin (2*h)) : Module.Free F (S _t) := Module.Free.of_divisionRing F (S _t)
  have hcomb (t : Fin (2*h)) (v : ι → F) :
      poleMap t (comb v) = Fintype.linearCombination F (poleMap t ∘ P) v := by
    simp [comb, Fintype.linearCombination_apply, map_sum]
  let f : (ι → F) →ₗ[F] (∀ t : Fin (2*h), S t) :=
    LinearMap.pi fun t ↦ ((poleMap t).comp comb).codRestrict (S t) fun v ↦ by
      change poleMap t (comb v) ∈ Submodule.span F (Set.range (poleMap t ∘ P))
      rw [hcomb, ← Fintype.range_linearCombination]
      exact ⟨v,rfl⟩
  have hk : f.ker ≤ M.mulVecLin.ker := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    apply (hM v).mpr
    apply poleTest_of_local s G
    intro t
    apply ProjectivePole.local_to_CRT H lift (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
      (s.B+s.J) (comb v) (G.vanishes t) (G.centre t)
    apply (localMap_zero_iff s (G.root t) (z t) (comb v)).mp
    have he := congrArg (fun w : ∀ t : Fin (2*h), S t ↦ ((w t : S t) : (Target F) ⧸ PoleImage.CutIdeal (abscissa F) (s.B+s.J)))
      (LinearMap.mem_ker.mp hv)
    change poleMap t (comb v) = 0 at he
    exact he
  have hker := Submodule.finrank_mono hk
  have hlocal (t : Fin (2*h)) : Module.finrank F (S t) ≤ blockSum s :=
    local_image_span_rank_le s (G.root t) (G.side t) (G.a t) (G.b t) (G.c t)
      (ha t) (G.b_ne t) P hP
  have hrange : Module.finrank F f.range ≤ (2*h) * blockSum s := by
    refine f.range.finrank_le.trans ?_
    rw [Module.finrank_pi_fintype]
    calc
      _ ≤ ∑ _t : Fin (2*h), blockSum s := Finset.sum_le_sum fun t _ ↦ hlocal t
      _ = _ := by simp
  have hf := f.finrank_range_add_finrank_ker
  have hm := M.mulVecLin.finrank_range_add_finrank_ker
  unfold Matrix.rank
  omega

end
end PoleGlobal
