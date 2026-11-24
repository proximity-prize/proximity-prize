import ProximityPrize.SubmissionLower.R6961MarkedSheetFrame

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Finset MulAction
open scoped BigOperators Polynomial

/-- Distinct integral roots cannot coalesce at a squarefree specialization. This
works over the local order directly, without a chosen uniformizer. -/
theorem distinct_residues {R k I:Type*} [CommRing R] [IsDomain R] [Field k]
    (ρ:R→+*k) (q:(Polynomial R)) (sep:(q.map ρ).Separable) (y:I→R) (inj:Function.Injective y)
    (root:∀i,q.eval (y i)=0) : Function.Injective (fun i=>ρ (y i)) := by
  intro i j eq
  by_contra ne
  obtain ⟨h,fac⟩:=dvd_iff_isRoot.mpr (root i)
  have other:h.eval (y j)=0 := by
    have hh:=root j
    rw [fac,eval_mul,eval_sub,eval_X,eval_C] at hh
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr (inj.ne (Ne.symm ne)))
  obtain ⟨g,rest⟩:=dvd_iff_isRoot.mpr other
  have dvd : (Polynomial.X-C (ρ (y i)))^2 ∣ q.map ρ := by
    refine ⟨g.map ρ,?_⟩
    change ρ (y i)=ρ (y j) at eq
    simp only [fac,rest,Polynomial.map_mul,Polynomial.map_sub,map_X,map_C,eq,pow_two,mul_assoc]
  have unit:=sep.squarefree _ (by simpa only [pow_two] using dvd)
  exact (irreducible_X_sub_C _).not_isUnit unit

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [IsGalois F E] [FiniteDimensional F E]
local notation "G" => E ≃ₐ[F] E

private theorem orbit_roots (y:E) : MulAction.orbit G y = (minpoly F y).rootSet E := by
  ext t
  rw [←Normal.minpoly_eq_iff_mem_orbit,Polynomial.mem_rootSet]
  have alg:IsIntegral F y:=Algebra.IsIntegral.isIntegral y
  constructor
  · intro eq
    exact ⟨minpoly.ne_zero alg,eq ▸ minpoly.aeval F t⟩
  · rintro ⟨_,root⟩
    exact minpoly.eq_of_root alg.isAlgebraic root

/-- The unmarked rows supplied by a separable local polynomial have the required
average. The chosen places may ramify. Annihilation by Y minus the word suffices
to prove a whole base-parameter factor in every entry of each such row. -/
theorem actual_unmarked_rows {J U:Type*} [Fintype J] [DecidableEq J] (e:ℕ)
    (y:J→E) (degree:∀j,(minpoly F (y j)).natDegree=e)
    {O:Type*} [CommRing O] [IsDomain O] [IsLocalRing O] (incl:O→+*E) (inj:Function.Injective incl)
    (q:J→(Polynomial O)) (sep:∀j,((q j).map (IsLocalRing.residue O)).Separable)
    (lift:∀ j, MulAction.orbit G (y j)→O) (value:∀j i,incl (lift j i)=i.val)
    (root:∀j i,(q j).eval (lift j i)=0) (word:J→O)
    (π:O) (A:G→Matrix J U O)
    (annihilates:∀g i j, π∣(lift i ⟨g (y i),⟨g,rfl⟩⟩-word i)*A g i j) :
    ∃ rows:G→Finset J, (∀g,∀i∈rows g,∀j,π∣A g i j) ∧
      e*(∑g:G,(rows g).card)=Fintype.card G*((e-1)*Fintype.card J) := by
  classical
  let I (j:J):Type _:=↥(MulAction.orbit G (y j))
  let fint (j:J):Fintype (I j) := (Finite.finite_mulAction_orbit (M:=G) (y j)).fintype
  have card (j:J) : Fintype.card (I j)=e := by
    calc _ = Fintype.card ((minpoly F (y j)).rootSet E) := Fintype.card_congr
           (Equiv.cast (congrArg (fun s:Set E=>↥s) (orbit_roots (F:=F) (y j))))
         _ = _ := (Polynomial.card_rootSet_eq_natDegree (IsGalois.separable F (y j))
           ((inferInstance : Normal F E).splits (y j))).trans (degree j)
  let pick (j:J):I j:=⟨y j,MulAction.mem_orbit_self (y j)⟩
  let res:=IsLocalRing.residue O
  have separates (j:J) : Function.Injective (fun a:I j=>res (lift j a)) :=
    distinct_residues res (q j) (sep j) _ (fun a b eq=>Subtype.ext
      ((value j a).symm.trans ((congrArg incl eq).trans (value j b)))) (root j)
  let chosen (j:J) : I j := if h:∃a:I j,res (lift j a)=res (word j) then h.choose else pick j
  have off (j:J) (a:I j) (ne:a≠chosen j) : res (lift j a)≠res (word j) := by
    intro eq
    have existsHit : ∃t:I j,res (lift j t)=res (word j) := ⟨a,eq⟩
    apply ne
    apply separates j
    simpa [chosen,existsHit] using eq.trans existsHit.choose_spec.symm
  let rows (g:G):=Finset.univ.filter (fun j=>g • pick j ≠chosen j)
  refine ⟨rows,fun g i hi j=>?_,row_average I e card pick chosen⟩
  have nz := off i (g • pick i) (Finset.mem_filter.mp hi).2
  have unit : IsUnit (lift i (g • pick i)-word i) :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by rw [map_sub];exact sub_ne_zero.mpr nz)
  exact unit.dvd_mul_left.mp (annihilates g i j)

#print axioms distinct_residues
#print axioms actual_unmarked_rows
end Lower6961.MarkedEvaluation
