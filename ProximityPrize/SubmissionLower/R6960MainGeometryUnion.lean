import ProximityPrize.SubmissionLower.R6960MainGeometryFee

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6960.MainGeometry
open Finset
open K1 (K)
open K1_14 (jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_3 (Surface Parent ProjectedProduct)
open RescueGeometry (Model Family OnSurface SurfacePass word exceptional_prefix)
open scoped Classical

def prefixCap : ℕ := 235296504696168815

/-- Use this preparation's one selected helper and split only at its
exception. Both outputs go through one terminal bank on the same CRT lift. -/
theorem Rows.combined_prefix {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} (R : Rows F Crt)
    (lo : 2339≤M.overhead.toNat) (hi : M.overhead.toNat≤33561)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨main,left,fee,passing,cover⟩ := R.main_prefix hi noPole residues
  rcases R.out.kind with unit | common
  · refine ⟨main,left,fee.trans (by decide +kernel),passing,?_⟩
    intro γ hγ
    apply cover
    exact mem_filter.mpr ⟨hγ,by simp [unit,jetAt]⟩
  · obtain ⟨rescue,right,cost,retains,rescue_cover⟩ :=
      exceptional_prefix F Crt lo hi noPole residues common
    refine ⟨main∪rescue,left∪right,
      (card_union_le _ _).trans ((Nat.add_le_add fee cost).trans (by decide +kernel)),?_,?_⟩
    · intro q hq
      exact (mem_union.mp hq).elim (passing q) (retains q)
    · intro γ hγ
      let lift (paid' : Finset K) (S' : Finset Surface)
          (hp : paid'⊆main∪rescue) (hs : S'⊆left∪right)
          (on : γ∈paid' ∨ ∃ q∈S',OnSurface F q γ) :
          γ∈main∪rescue ∨ ∃ q∈left∪right,OnSurface F q γ := by
        rcases on with mark | ⟨q,hq,hmark⟩
        · exact Or.inl (hp mark)
        · exact Or.inr ⟨q,hs hq,hmark⟩
      by_cases e : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
      · exact lift rescue right subset_union_right subset_union_right (rescue_cover γ hγ e)
      · exact lift main left subset_union_left subset_union_left
          (cover γ (mem_filter.mpr ⟨hγ,e⟩))

/-- The concrete 69.60 high prefix and its shared projected product. An
empty union covers every mark by the paid prefix alone. -/
theorem combined_prefix {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2339≤M.overhead.toNat) (hi : M.overhead.toNat≤33561)
    (noPole : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ (paid : Finset K) (S : Finset Surface),paid.card≤prefixCap ∧
      (∀ q∈S,Parent q ∧ SurfacePass Crt (word M) q) ∧
      (S.Nonempty → ∃ f,ProjectedProduct S f) ∧
      ∀ γ∈Γ,γ∈paid ∨ ∃ q∈S,OnSurface F q γ := by
  obtain ⟨R⟩ := rows F Crt lo hi noPole residues
  obtain ⟨paid,S,fee,geom,cover⟩ := R.combined_prefix lo hi noPole residues
  exact ⟨paid,S,fee,geom,fun hs=>K1_14_3_7.proof S hs (fun q hq=>(geom q hq).1),cover⟩

#print axioms Rows.combined_prefix
#print axioms combined_prefix

end Lower6960.MainGeometry
