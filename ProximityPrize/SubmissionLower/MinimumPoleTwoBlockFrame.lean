import ProximityPrize.SubmissionLower.H2429ConjugateTwists
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions


set_option autoImplicit false
set_option Elab.async false

namespace MinimumPoleFiniteCRT

open Polynomial Finset P1 H2429ConjugateTwists
open scoped Polynomial BigOperators

private theorem exists_basis {s : Finset ℕ} {H Q : ℕ → K[X]} {D : K[X]}
    (prod : D = ∏ i ∈ s, H i) (monic : D.Monic) (positive : 0 < D.natDegree)
    (coprime : (s : Set ℕ).Pairwise fun i j => IsCoprime (H i) (H j)) (i : ℕ) (hi : i ∈ s) :
    ∃ R : K[X], R.natDegree < D.natDegree ∧ H i ∣ R + Q i ∧
      ∀ j ∈ s.erase i, H j ∣ R := by
  classical
  let T := ∏ j ∈ s.erase i, H j
  have hcop : IsCoprime (H i) T := IsCoprime.prod_right fun j hj =>
    coprime hi (mem_of_mem_erase hj) (ne_of_mem_erase hj).symm
  obtain ⟨a,b,h⟩ := hcop
  let U := -(b * T) * Q i
  let R := U %ₘ D
  have diff : D ∣ R - U := dvd_modByMonic_sub U D
  have hneq : D ≠ 1 := fun he => by simp [he] at positive
  refine ⟨R,natDegree_modByMonic_lt _ monic hneq,?_,?_⟩
  · have hd : H i ∣ D := by rw [prod]; exact dvd_prod_of_mem _ hi
    have hu : H i ∣ U + Q i := ⟨a * Q i, by dsimp [U]; linear_combination -(Q i) * h⟩
    have eq : R + Q i = (R - U) + (U + Q i) := by ring
    rw [eq]
    exact dvd_add (hd.trans diff) hu
  · intro j hj
    have hT : H j ∣ T := dvd_prod_of_mem _ hj
    have hd : H j ∣ D := by rw [prod]; exact dvd_prod_of_mem _ (mem_of_mem_erase hj)
    have hu : H j ∣ U := dvd_mul_of_dvd_left (dvd_neg.mpr (hT.mul_left _)) _
    exact sub_add_cancel R U ▸ dvd_add (hd.trans diff) hu

/-- Distinct conjugate poles give a linear remainder and a lower-degree quotient. -/
theorem quotient {cap hits h : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    (s : Finset ℕ) (nonempty : s.Nonempty)
    (M : ModelAt cap u del) (F : FamilyAt hits M Γ)
    (pole : M.E.natDegree = h) (height : M.overhead = h)
    (positive : 0 < h) (room : s.card * h ≤ 131071 + h)
    (shift : M.shift = 0) (factor : M.factor = 1) (first : M.A₀ = 1) (second : M.A₁ = 0)
    (coprime : (s : Set ℕ).Pairwise (fun i j => IsCoprime (M.E.map (σ i)) (M.E.map (σ j)))) :
    ∃ (D : K[X]) (R : ℕ → K[X]),
      D.Monic ∧ D.natDegree = (s.card * h) ∧ (∀ i : I, D.eval (node i) ≠ 0) ∧
      (∀ i ∈ s, (R i).natDegree < (s.card * h)) ∧
      ∀ (γ : K) (hγ : γ ∈ Γ), ∃ q : K[X], q.natDegree ≤ (131071 + h - s.card * h) ∧
        F.scalar γ = D * q + ∑ i ∈ s, C (σ i γ) * R i ∧
        ∀ i ∈ (F.mark γ hγ).bad.support,
          D.eval (node i) * q.eval (node i) +
            (∑ j ∈ s, C (σ j γ) * R j).eval (node i) = M.word i := by
  classical
  have hsum : 0 < s.card * h := Nat.mul_pos (card_pos.mpr nonempty) positive
  let H (i : ℕ) := M.E.map (σ i)
  let Q (i : ℕ) := M.Q.map (σ i)
  let D := ∏ i ∈ s, H i
  have monic : D.Monic := monic_prod_of_monic s H fun i _ => M.E_monic.map (σ i)
  have dD : D.natDegree = (s.card * h) := by
    rw [natDegree_prod_of_monic s H (fun i _ => M.E_monic.map (σ i))]
    exact (sum_congr rfl (fun i _ => (natDegree_map (σ i)).trans pole)).trans (by simp)
  have localCoprime : (s : Set ℕ).Pairwise fun i j => IsCoprime (H i) (H j) :=
    coprime
  have exist (i : ℕ) : ∃ R : K[X], i ∈ s →
      R.natDegree < D.natDegree ∧ H i ∣ R + Q i ∧ ∀ j ∈ s.erase i, H j ∣ R := by
    by_cases hi : i ∈ s
    · obtain ⟨R,hR⟩ := exists_basis (s := s) (H := H) (Q := Q) (D := D) rfl monic (by omega) localCoprime i hi
      exact ⟨R,fun _ => hR⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose R spec using exist
  have off (i : I) : D.eval (node i) ≠ 0 := by
    rw [eval_prod]
    exact prod_ne_zero_iff.mpr (fun j _ => off_nodes M.E_nodes j i)
  refine ⟨D,R,monic,dD,off,fun i hi => dD ▸ (spec i hi).1,?_⟩
  intro γ hγ
  let f (i : ℕ) := C (σ i γ) * R i
  let T := ∑ i ∈ s, f i
  have dT : T.natDegree ≤ (s.card * h - 1) := by
    apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_le _ _).trans (by have h := (spec i hi).1; omega)
  let B := F.mark γ hγ
  have base : M.E ∣ F.scalar γ + C γ * M.Q := by
    have h := B.identity
    have label : M.label γ = γ := by simp [ModelAt.label, shift]
    change M.E * M.decoder B.bad - C (M.label γ) * M.Q =
      M.factor * (M.A₀ + C (M.label γ) * M.A₁) * F.scalar γ at h
    simp only [label, first, second, factor, mul_zero, add_zero, one_mul] at h
    exact ⟨M.decoder B.bad,by linear_combination -h⟩
  have all : D ∣ F.scalar γ - T := by
    apply Finset.prod_dvd_of_isRelPrime
    · intro i hi j hj hn
      exact (localCoprime hi hj hn).isRelPrime
    · intro i hi
      have original : H i ∣ F.scalar γ + C (σ i γ) * Q i := by
        simpa only [H,Q,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,family_fixed F i γ hγ]
          using Polynomial.map_dvd (σ i) base
      have own : H i ∣ f i + C (σ i γ) * Q i := by
        simpa only [f,mul_add] using ((spec i hi).2.1.mul_left (C (σ i γ)))
      have rest : H i ∣ ∑ j ∈ s.erase i, f j := by
        apply dvd_sum
        intro j hj
        have hs := mem_of_mem_erase hj
        have ne := ne_of_mem_erase hj
        exact ((spec j hs).2.2 i (mem_erase.mpr ⟨ne.symm,hi⟩)).mul_left _
      have eq : F.scalar γ - T =
          (F.scalar γ + C (σ i γ) * Q i) - (f i + C (σ i γ) * Q i) - ∑ j ∈ s.erase i, f j := by
        dsimp only [T]
        rw [← sum_erase_add _ _ hi]
        ring
      rw [eq]
      exact dvd_sub (dvd_sub original own) rest
  obtain ⟨q,hq⟩ := all
  have ds : (F.scalar γ).natDegree ≤ (131071 + h) := by
    rcases B.scalar_degree with h | h
    · simp [h]
    · change ((F.scalar γ).natDegree : ℤ) ≤ 131071 + M.overhead at h
      omega
  have dq : q.natDegree ≤ (131071 + h - s.card * h) := by
    by_cases hz : q = 0
    · simp [hz]
    · have h : (F.scalar γ - T).natDegree ≤ (131071 + h) :=
        (natDegree_sub_le _ _).trans (max_le ds (dT.trans (by omega)))
      rw [hq,natDegree_mul monic.ne_zero hz,dD] at h
      omega
  have eq : F.scalar γ = D * q + T := by linear_combination hq
  refine ⟨q,dq,eq,fun i hi => ?_⟩
  have h := congrArg (eval (node i)) eq
  rw [eval_add,eval_mul,B.scalar_hits i hi] at h
  exact h.symm

end MinimumPoleFiniteCRT


set_option autoImplicit false
set_option Elab.async false

namespace ResidueSpace
noncomputable section

open Polynomial
open scoped Polynomial

variable {F ι : Type*} [Field F] [Fintype ι]

private def multiples (G : F[X]) (n : ℕ) : Submodule F F[X] :=
  (degreeLT F n).map (LinearMap.mulLeft F G)

def space (G : F[X]) (n : ℕ) (R : ι → F[X]) : Submodule F F[X] :=
  multiples G n ⊔ Submodule.span F (Set.range R)

private instance degreeFinite (n : ℕ) : Module.Finite F (degreeLT F n) :=
  Module.Finite.of_surjective (degreeLTEquiv F n).symm.toLinearMap
    (degreeLTEquiv F n).symm.surjective

private instance multiplesFinite (G : F[X]) (n : ℕ) :
    Module.Finite F (multiples G n) := by
  unfold multiples
  infer_instance

private instance spanFinite (R : ι → F[X]) :
    Module.Finite F (Submodule.span F (Set.range R)) :=
  Module.Finite.span_of_finite F (Set.finite_range R)

private instance spaceFinite (G : F[X]) (n : ℕ) (R : ι → F[X]) :
    Module.Finite F (space G n R) := by
  unfold space
  infer_instance

theorem finrank_le (G : F[X]) (n : ℕ) (R : ι → F[X]) :
    Module.finrank F (space G n R) ≤ n + Fintype.card ι := by
  have hd : Module.finrank F (degreeLT F n) = n := by
    rw [(degreeLTEquiv F n).finrank_eq]
    simp [Module.finrank_pi]
  unfold space
  apply (Submodule.finrank_add_le_finrank_add_finrank _ _).trans
  exact Nat.add_le_add
    ((Submodule.finrank_map_le _ (degreeLT F n)).trans_eq hd)
    (finrank_range_le_card (R := F) R)

def evaluate (G : F[X]) (n : ℕ) (R : ι → F[X]) (T : Finset F) :
    space G n R →ₗ[F] T → F :=
  LinearMap.pi (fun (x : T) => (leval x.val).comp (space G n R).subtype)

/-- The chosen agreements remove one dimension each up to the number of
free polynomial coefficients. The pole is nonzero on the chosen sites. -/
theorem remaining_finrank (G : F[X]) (n : ℕ) (R : ι → F[X]) (T : Finset F)
    (size : T.card ≤ n) (off : ∀ x ∈ T, G.eval x ≠ 0) :
    Module.finrank F (LinearMap.ker (evaluate G n R T)) ≤
      n + Fintype.card ι - T.card := by
  classical
  let interp := Lagrange.funEquivDegreeLT (F := F) (s := T) (v := id)
    (fun _ _ _ _ eq => eq)
  have surjective : Function.Surjective (evaluate G n R T) := by
    intro w
    let f := interp.symm (fun x => w x / G.eval x.val)
    have mem : ((f : F[X])) ∈ degreeLT F n := degreeLT_mono size f.property
    have incl : multiples G n ≤ space G n R := le_sup_left
    have inSpace : G * (f : F[X]) ∈ space G n R :=
      incl (Submodule.mem_map.mpr ⟨f,mem,rfl⟩)
    refine ⟨⟨G * (f : F[X]),inSpace⟩,?_⟩
    funext x
    have hx := congrFun (interp.apply_symm_apply (fun x : T => w x / G.eval x.val)) x
    change (f : F[X]).eval x.val = w x / G.eval x.val at hx
    change (G * (f : F[X])).eval x.val = w x
    rw [eval_mul,hx,mul_comm,div_mul_cancel₀ _ (off x.val x.property)]
  have rank : Module.finrank F (LinearMap.range (evaluate G n R T)) = T.card := by
    rw [LinearMap.range_eq_top.mpr surjective,finrank_top]
    simp [Module.finrank_pi]
  have hs := (evaluate G n R T).finrank_range_add_finrank_ker
  rw [rank] at hs
  have hbound := finrank_le G n R
  omega


end
end ResidueSpace

namespace MinimumPoleTwoBlockFrame
open Polynomial Finset P1 H2429ConjugateTwists
open scoped Polynomial BigOperators

/-- The two prescribed pole residues keep the marked scalars in one small
polynomial space. Its degree and its dimension are separate bounds. -/
theorem two_blocks {cap hits h : ℕ} {u : Words} {del : Finset I} {Γ : Finset K}
    (M : ModelAt cap u del) (F : FamilyAt hits M Γ)
    (pole : M.E.natDegree = h) (height : M.overhead = h)
    (positive : 0 < h) (room : h ≤ 131071)
    (shift : M.shift = 0) (factor : M.factor = 1) (first : M.A₀ = 1) (second : M.A₁ = 0) :
    ∃ (D : K[X]) (R : Fin 2 → K[X]),
      D.Monic ∧ D.natDegree = 2 * h ∧ (∀ i : I, D.eval (node i) ≠ 0) ∧
      let W := ResidueSpace.space D (131071 - h + 1) R
      W ≤ degreeLT K (131071 + h + 1) ∧
      Module.finrank K W ≤ 131071 - h + 3 ∧
      ∀ γ ∈ Γ, F.scalar γ ∈ W := by
  classical
  let s : Finset ℕ := {0,1}
  have size : s.card = 2 := by decide
  have nz : s.Nonempty := by exact ⟨0,by simp [s]⟩
  have hz : σ 0 = RingHom.id K := by
    ext x
    rw [σ,iterateFrobenius_def]
    simp
  have hc : (s : Set ℕ).Pairwise fun i j => IsCoprime (M.E.map (σ i)) (M.E.map (σ j)) := by
    intro i hi j hj ne
    have hi' : i = 0 ∨ i = 1 := by simpa [s] using hi
    have hj' : j = 0 ∨ j = 1 := by simpa [s] using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · exact (ne rfl).elim
    · simpa only [hz,sigma_one,Polynomial.map_id] using M.adjacent_coprime
    · simpa only [hz,sigma_one,Polynomial.map_id] using M.adjacent_coprime.symm
    · exact (ne rfl).elim
  obtain ⟨D,R,monic,degree,off,rd,expansion⟩ :=
    MinimumPoleFiniteCRT.quotient s nz M F pole height positive (by rw [size]; omega)
      shift factor first second hc
  let B (i : Fin 2) := R i.val
  rw [size] at degree rd
  refine ⟨D,B,monic,degree,off,?_,?_,?_⟩
  · unfold ResidueSpace.space
    apply sup_le
    · intro P hP
      obtain ⟨V,hV,rfl⟩ := Submodule.mem_map.mp hP
      change D * V ∈ degreeLT K _
      rw [degreeLT_succ_eq_degreeLE,mem_degreeLE]
      rw [degreeLT_succ_eq_degreeLE,mem_degreeLE] at hV
      have hdeg := (degree_mul_le D V).trans (add_le_add (degree_le_natDegree) hV)
      rw [degree] at hdeg
      exact hdeg.trans (by exact_mod_cast (show 2*h + (131071-h) ≤ 131071+h by omega))
    · apply Submodule.span_le.mpr
      rintro P ⟨i,rfl⟩
      have hi : i.val = 0 ∨ i.val = 1 := by omega
      have hs : i.val ∈ s := by simpa [s] using hi
      have hd := (rd i.val hs).le.trans (by omega : 2*h ≤ 131071+h)
      change B i ∈ degreeLT K (131071+h+1)
      exact mem_degreeLT.mpr
        (degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hd))
  · simpa [Nat.add_assoc] using ResidueSpace.finrank_le D (131071-h+1) B
  · intro γ member
    obtain ⟨q,dq,eq,_⟩ := expansion γ member
    have dq' : q.natDegree ≤ 131071 - h := by rw [size] at dq; omega
    rw [eq]
    have dqm : q ∈ degreeLT K (131071-h+1) := by
      rw [degreeLT_succ_eq_degreeLE,mem_degreeLE]
      exact degree_le_natDegree.trans (by exact_mod_cast dq')
    have sub : ResidueSpace.multiples D (131071-h+1) ≤ ResidueSpace.space D (131071-h+1) B :=
      le_sup_left
    have m₁ : D*q ∈ ResidueSpace.space D (131071-h+1) B :=
      sub (Submodule.mem_map.mpr ⟨q,dqm,rfl⟩)
    have m₂ : ∑ i ∈ s, C (σ i γ) * R i ∈ Submodule.span K (Set.range B) := by
      apply Submodule.sum_mem
      intro i hi
      have hd : i = 0 ∨ i = 1 := by simpa [s] using hi
      have hm : R i ∈ Submodule.span K (Set.range B) :=
        Submodule.subset_span ⟨⟨i,by omega⟩,rfl⟩
      simpa only [smul_eq_C_mul] using Submodule.smul_mem _ (σ i γ) hm
    have incl : Submodule.span K (Set.range B) ≤ ResidueSpace.space D (131071-h+1) B :=
      le_sup_right
    exact Submodule.add_mem _ m₁ (incl m₂)

#print axioms two_blocks
end MinimumPoleTwoBlockFrame
