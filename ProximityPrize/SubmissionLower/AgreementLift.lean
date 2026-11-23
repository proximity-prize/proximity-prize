import ProximityPrize.SubmissionLower.Numeric2Aux

set_option Elab.async false
namespace AgreementLift
noncomputable section
open Polynomial Finset FrobeniusLocator Code LinearCode CoreDefinitions ProximityPrize.Benchmark
open P1 (I K node k)

/-- Every scalar hit at a retained site is an actual hit for the marked decoder. -/
theorem decoder_hit {cap u del A γ S} (M : P1.ModelAt cap u del) (B : P1.MarkAt (A := A) M γ S)
    {i} (hi : i ∉ del) (hit : S.eval (node i) = M.word i) :
    B.bad.decoder.eval (node i) = u 0 i + γ * u 1 i := by
  have eqn := congrArg (fun f : K[X] => f.eval (node i)) B.identity
  simp only [P1.ModelAt.decoder, P1.ModelAt.amplitude, P1.ModelAt.label,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_add, hit] at eqn
  apply mul_left_cancel₀ (M.E_nodes i)
  linear_combination eqn - M.first_word i hi - (γ - M.shift) * M.second_word i hi

def fullSupport {cap u del} (M : P1.ModelAt cap u del) (S : K[X]) : Finset I := by
  classical
  exact (univ \ del).filter fun i => S.eval (node i) = M.word i

private theorem restrict_extend {w : I → K} {T T' : Finset I} (sub : T ⊆ T')
    (ext : ExtendsOn node w k T') : ExtendsOn node w k T := by
  obtain ⟨f,df,hits⟩ := ext
  exact ⟨f,df,fun i hi => hits i (sub hi)⟩

/-- Enlarge the mark to every retained scalar hit while keeping its nonjoint witness. -/
def raiseMark {cap u del A γ S N} (M : P1.ModelAt cap u del) (B : P1.MarkAt (A := A) M γ S)
    (enough : N ≤ (fullSupport M S).card) : P1.MarkAt (A := N) M γ S := by
  classical
  have sub : B.bad.support ⊆ fullSupport M S := fun i hi => mem_filter.mpr
    ⟨mem_sdiff.mpr ⟨mem_univ _,fun bad => disjoint_left.mp B.avoids_deleted hi bad⟩, B.scalar_hits i hi⟩
  let mark : P1.BadMarkAt N u γ :=
    { support := fullSupport M S
      decoder := B.bad.decoder
      agreement := enough
      degree := B.bad.degree
      hits := fun i hi => decoder_hit M B (mem_sdiff.mp (mem_filter.mp hi).1).2 (mem_filter.mp hi).2
      nonjoint := fun both => B.bad.nonjoint ⟨restrict_extend sub both.1, restrict_extend sub both.2⟩ }
  exact ⟨mark, disjoint_left.mpr (fun _ hi => (mem_sdiff.mp (mem_filter.mp hi).1).2), B.scalar_fixed,
    B.scalar_degree, fun _ hi => (mem_filter.mp hi).2, B.pole_unit, B.identity⟩

def strong {cap u del Γ A} (M : P1.ModelAt cap u del) (F : P1.FamilyAt A M Γ) (N : ℕ) :
    Finset K := by
  classical
  exact Γ.filter fun γ => N ≤ (fullSupport M (F.scalar γ)).card

def atAgreement {cap u del Γ A} (M : P1.ModelAt cap u del) (F : P1.FamilyAt A M Γ) (N : ℕ) :
    P1.FamilyAt N M (strong M F N) where
  scalar := F.scalar
  distinct := F.distinct.mono (filter_subset _ _)
  mark γ hg := raiseMark M (F.mark γ (mem_filter.mp hg).1) (mem_filter.mp hg).2

/-- A mark with enough agreement yields the projected-code event at this radius. -/
theorem bad_of_mark {u γ N} (B : P1.BadMarkAt N u γ) {δ : ℝ}
    (threshold : (Fintype.card I : ℝ) * (1-δ) ≤ N) :
    IsMCA (AffineLineGenerator K) IRSProfile.baseCode γ u δ := by
  classical
  let : NeZero k := ⟨by decide⟩
  change IsMCA (AffineLineGenerator K) (ReedSolomon.code node k) γ u δ
  refine ⟨B.support,threshold.trans (by exact_mod_cast B.agreement),?_,?_⟩
  · have ext : ExtendsOn node (fun i => u 0 i + γ * u 1 i) k B.support := ⟨B.decoder,B.degree,B.hits⟩
    have h := (Principal.projected_mem_iff_extendsOn node _ k B.support).mpr ext
    simpa [AffineLineGenerator, Fin.sum_univ_two, smul_eq_mul, mul_comm] using h
  · by_contra! all
    apply B.nonjoint
    exact ⟨(Principal.projected_mem_iff_extendsOn node _ k B.support).mp (all 0),
      (Principal.projected_mem_iff_extendsOn node _ k B.support).mp (all 1)⟩

#print axioms decoder_hit
#print axioms atAgreement
#print axioms bad_of_mark
end
end AgreementLift
