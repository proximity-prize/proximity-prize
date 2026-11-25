import ProximityPrize.SubmissionLower.R6966ProofNativeAffineRows
import ProximityPrize.SubmissionLower.R6966ProofWordAxisPrice
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineLedger

set_option Elab.async false

namespace Research6966.NativeAffineTariff
open Polynomial Finset
open K1 (K I p)
open K1_14 (FX Seeds Equation jetAt seedEmbedding)
open K1_14_3 (SeedField Surface ProjectedProduct)
open PadeNativeQuotient (Native)
open NativeAffineRows
open scoped Polynomial Differential Classical
attribute [local instance] GenericPhysicalCentre.physical
noncomputable section
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 18

private abbrev side (a d : ℕ) := WordSurfacePrice.side (Fintype.card I) a d

theorem side_explicit (a d h : ℕ) : side a d h=WordSurfacePrice.side (Fintype.card I) a d h := rfl

private theorem add_fee {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField} (N : Native G) (k bill extra : ℕ)
    (reg : (good F T N).card*k ≤ bill) (exc : (bad F T N).card ≤ extra) :
    T.card*k ≤ extra*k+bill := by
  rw [← sizes F N, Nat.add_mul, Nat.add_comm (extra*k)]
  exact Nat.add_le_add reg (Nat.mul_le_mul_right k exc)

/-- Independent seed widths price the complete family on an actual affine
native graph. Each height is the proved nodal degree in that coordinate. -/
theorem rectangular {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^3 ≤ (width 0+p*width 1)*(a-d)^3+
      6*side a d 1*side a d (d*width 0)*side a d (d*width 1) := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  have count := WordUnconstrainedPrice.three_axes (fun z : ↥(good F T N) => point F z.val)
    (rows M N d) _ a d gap (row_caps M N width axes d) enough shared
  rw [Fintype.card_coe, Fin.prod_univ_three] at count
  have reg : (good F T N).card*(a-d)^3 ≤ 6*side a d 1*side a d (d*width 0)*side a d (d*width 1) := by
    simpa only [show (1:Fin 3) = (0:Fin 2).succ from rfl, show (2:Fin 3) = (1:Fin 2).succ from rfl,
      Fin.cons_zero, Fin.cons_succ, ← Nat.mul_assoc] using count
  exact add_fee F N _ _ _ reg (fee F N gp affine width axes small owners)

/-- The projected surface can give a lower price than the unconstrained
three-coordinate affine family. Both prices use the same nodal rows. -/
theorem projected {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {H : Equation}
    (project : ProjectedProduct parents H) {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^2 ≤ (width 0+p*width 1)*(a-d)^2+2*
      (H.natDegree*side a d (d*width 0)*side a d (d*width 1)+
        KoalaRect.axisDegree H 0*side a d 1*side a d (d*width 1)+
        KoalaRect.axisDegree H 1*side a d 1*side a d (d*width 0)) := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  let H' := OdeSurfaceBridge.coordinates H
  let v : Fin 3 → ℕ := Fin.cons H.natDegree (KoalaRect.axisDegree H)
  have hn : H' ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv FX 2).symm.injective).mpr project.primitive.ne_zero
  have vanish (z : ↥(good F T N)) : MvPolynomial.eval (point F z.val) H' = 0 := by
    obtain ⟨q, hq, _, mark⟩ := owners z.val (good_subset F N z.property)
    have killed := mark (C H) (project.vanishes q hq)
    change MvPolynomial.eval (Fin.cons _ _) (OdeSurfaceBridge.coordinates H) = 0
    rw [OdeSurfaceBridge.read]
    simpa only [jetAt, coe_eval₂RingHom, eval₂_C, NonlinearMarkRows.evaluate,
      K1_14.graphEval, seedPoint] using killed
  have cap := OdeSurfaceBridge.degrees H H.natDegree (KoalaRect.axisDegree H) le_rfl
    (fun z => (OdeSurfaceBridge.axis_cap ..).mpr ((KoalaRect.axisDegree_le_iff H z _).mp le_rfl))
  have count := WordSurfacePrice.count (fun z : ↥(good F T N) => point F z.val) (rows M N d)
    H' hn vanish v _ cap (row_caps M N width axes d) a d gap enough shared
  rw [Fintype.card_coe] at count
  apply add_fee F N _ _ _ _ (fee F N gp affine width axes small owners)
  simpa only [WordSurfacePrice.mixed, v, show (1:Fin 3) = (0:Fin 2).succ from rfl,
    show (2:Fin 3) = (1:Fin 2).succ from rfl, Fin.cons_zero, Fin.cons_succ] using count

private def activeAxes (z : Fin 2) : Fin 2 ↪ Fin 3 where
  toFun := Fin.cons 0 (fun _ => z.succ)
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j
    · rfl
    · exact (Fin.succ_ne_zero z eq.symm).elim
    · exact (Fin.succ_ne_zero z eq).elim
    · rfl

/-- Removing the unused seed gives a two-coordinate price. The surviving
seed may be the Frobenius coordinate. -/
theorem single_seed {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : Fin 2 → ℕ)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ width z)
    (small : width 0 < p) (active : Fin 2) (inactive : ∀ z, z ≠ active → width z = 0)
    (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^2 ≤ (width 0+p*width 1)*(a-d)^2+2*side a d 1*side a d (d*width active) := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  let h := Fin.cons (α := fun _ : Fin 2 => ℕ) 1 (fun _ => d*width active)
  have cap := row_caps M N width axes d
  have selected (i : I) (j : Fin 2) : (rows M N d i).degreeOf (activeAxes active j) ≤ h j := by
    fin_cases j
    · exact cap i 0
    · exact cap i active.succ
  have dropped (i : I) (j : Fin 3) (out : j ∉ Set.range (activeAxes active)) :
      (rows M N d i).degreeOf j = 0 := by
    revert out
    refine Fin.cases ?_ (fun z => ?_) j
    · intro out; exact (out ⟨0, rfl⟩).elim
    · intro out
      have ne : z ≠ active := fun eq => out ⟨1, by subst z; rfl⟩
      exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ, inactive z ne, Nat.mul_zero] using cap i z.succ)
  have count := WordAxisPrice.two (fun z : ↥(good F T N) => point F z.val)
    (rows M N d) (activeAxes active) h a d gap selected dropped enough shared
  rw [Fintype.card_coe] at count
  exact add_fee F N _ _ _ count (fee F N gp affine width axes small owners)

private def ordinateAxis : Fin 1 ↪ Fin 3 :=
  ⟨fun _ => 0, fun i j _ => Subsingleton.elim i j⟩

/-- A fixed affine graph costs at most one agreement ratio, with no
singular-label fee. -/
theorem fixed {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1)
    (axes : ∀ j i z, ((N.poly.coeff j).coeff i).degreeOf z ≤ 0)
    (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d) ≤ side a d 1 := by
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  have cap := row_caps M N (fun _ => 0) axes d
  have dropped (i : I) (j : Fin 3) (out : j ∉ Set.range ordinateAxis) :
      (rows M N d i).degreeOf j = 0 := by
    revert out
    refine Fin.cases ?_ (fun z _ => ?_) j
    · intro out; exact (out ⟨0, rfl⟩).elim
    · exact Nat.eq_zero_of_le_zero (by simpa only [Fin.cons_succ, Nat.mul_zero] using cap i z.succ)
  have count := WordAxisPrice.one (fun z : ↥(good F T N) => point F z.val)
    (rows M N d) ordinateAxis 1 a d gap (fun i => cap i 0) dropped enough shared
  rw [Fintype.card_coe] at count
  have exc : (bad F T N).card ≤ 0 := by
    simpa only [Nat.mul_zero, Nat.add_zero] using fee F N gp affine (fun _ => 0) axes (by decide) owners
  simpa only [Nat.zero_mul, Nat.zero_add] using add_fee F N _ _ _ count exc

private theorem frobenius_total_count {E : Type*} [Field E] (q width : ℕ) (pos : 0 < q)
    (Q : MvPolynomial (Fin 2) E) (nonzero : Q ≠ 0)
    (total : Q ∈ MvPolynomial.restrictWeightAtMost (fun _ => 1) width) (small : width < q)
    (marks : Finset E) (roots : ∀ t ∈ marks, MvPolynomial.eval ![t,t^q] Q = 0) :
    marks.card ≤ q*width := by
  classical
  let P := K1_10.frobeniusGraph q Q
  have weight (e : Fin 2 →₀ ℕ) (he : e ∈ Q.support) : e 0+e 1 ≤ width := by
    have wt := MvPolynomial.mem_restrictWeightAtMost.mp total e he
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum, Fin.sum_univ_two] at wt
    exact wt
  have axis : Q.degreeOf 0 < q := by
    refine lt_of_le_of_lt (MvPolynomial.degreeOf_le_iff.mpr ?_) small
    intro e he
    have := weight e he
    omega
  have nz : P ≠ 0 := K1_10.frobeniusGraph_ne_zero q pos Q nonzero axis
  have deg : P.natDegree ≤ q*width := by
    apply (MvPolynomial.natDegree_aeval_le_weightedTotalDegree_of_le (fun _ => q)
      (![Polynomial.X,Polynomial.X^q] : Fin 2 → Polynomial E) Q ?_).trans
    · apply Finset.sup_le
      intro e he
      rw [Finsupp.weight_eq_sum, Fin.sum_univ_two, smul_eq_mul, smul_eq_mul]
      rw [← Nat.add_mul, Nat.mul_comm]
      exact Nat.mul_le_mul_left q (weight e he)
    · intro i
      fin_cases i
      · change (Polynomial.X : Polynomial E).natDegree ≤ q
        rw [natDegree_X]; exact pos
      · change ((Polynomial.X : Polynomial E)^q).natDegree ≤ q
        rw [natDegree_pow, natDegree_X, mul_one]
  have count : marks.card ≤ P.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro t ht
    apply (Polynomial.mem_roots nz).mpr
    have eval_eq :
        (Polynomial.evalRingHom t).comp (K1_10.frobeniusGraph (F := E) q).toRingHom =
          MvPolynomial.eval ![t,t^q] := by
      apply MvPolynomial.ringHom_ext
      · intro c; simp [K1_10.frobeniusGraph]
      · intro i; fin_cases i <;> simp [K1_10.frobeniusGraph]
    exact ((RingHom.congr_fun eval_eq Q).trans (roots t ht))
  exact count.trans deg

private theorem total_fee {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : ℕ)
    (total : leading N ∈ MvPolynomial.restrictWeightAtMost (fun _ => 1) width) (small : width < p) :
    (bad F T N).card ≤ p*width := by
  classical
  let embeddedLabel (z : K) := seedEmbedding (M.label z)
  have inj : Function.Injective embeddedLabel := seedEmbedding.injective.comp (label_inj M)
  have nonzero : leading N ≠ 0 := fun zero => NativeGraphExceptional.den_ne N gp
    (by rw [den_eq N gp affine, zero, map_zero])
  rw [← card_image_of_injective (bad F T N) inj]
  apply frobenius_total_count p width (by decide) (leading N) nonzero total small
  intro x hx
  obtain ⟨z, badz, rfl⟩ := mem_image.mp hx
  have root : NativeAffineRows.val F z (NativeGraphExceptional.den N) = 0 := (mem_filter.mp badz).2
  rw [den_eq N gp affine] at root
  unfold NativeAffineRows.val at root
  rw [eval₂_C] at root
  exact root

/-- A common total seed-degree ceiling gives the coefficient-three bound.
The singular denominator has at most `p * width` marked labels. -/
theorem price {u deleted maxHeight a} {M : P1.ModelAt maxHeight u deleted} {Γ T : Finset K}
    (F : P1.FamilyAt a M Γ) (sub : T ⊆ Γ) {parents : Finset Surface} {G : Pade.Row SeedField}
    (N : Native G) (gp : G.primitive) (affine : G.graphDegree = 1) (width : ℕ)
    (total : ∀ j i, (N.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _ => 1) width)
    (small : width < p) (d : ℕ) (physical : (131071 : ℤ)+M.overhead ≤ d) (dp : d < p)
    (gap : d < a) (owners : Owned F T parents N) :
    T.card*(a-d)^3 ≤ p*width*(a-d)^3+3*side a d 1*(side a d (d*width))^2 := by
  classical
  let S := good F T N
  let W := MvPolynomial.restrictWeightAtMost (R := FX) (fun _ : Fin 2 => 1) width
  have hA : leading N ∈ W := total 1 0
  have hB : linear N ∈ W := by
    change (-N.poly.coeff 0).coeff 1 ∈ W
    rw [coeff_neg]; exact Submodule.neg_mem _ (total 0 1)
  have hC : constant N ∈ W := by
    change (-N.poly.coeff 0).coeff 0 ∈ W
    rw [coeff_neg]; exact Submodule.neg_mem _ (total 0 0)
  let P (z : ↥S) (j : Option (Fin 2)) : FX :=
    j.elim (K1_14.atX (F.scalar z.val)) (seedPoint (M.label z.val))
  let R (i : I) := (MvPolynomial.optionEquivLeft FX (Fin 2)).symm (equation M N d i)
  have bound (i : I) : R i ∈ MvPolynomial.restrictBidegree (Fin 2) FX 1 (d*width) := by
    apply MvPolynomial.mem_restrictBidegree.mpr
    intro e he
    have align : ((equation M N d i).coeff (e none)).coeff e.some = (R i).coeff e := by
      simpa only [R, AlgEquiv.apply_symm_apply] using
        MvPolynomial.optionEquivLeft_coeff_some_coeff_none FX (Fin 2) e (R i)
    have live : ((equation M N d i).coeff (e none)).coeff e.some ≠ 0 :=
      align ▸ MvPolynomial.mem_support_iff.mp he
    have cnz : (equation M N d i).coeff (e none) ≠ 0 := fun zero => live (by rw [zero]; simp)
    refine ⟨(le_natDegree_of_ne_zero cnz).trans (AffineMarkRows.row_degree ..), ?_⟩
    have c := MvPolynomial.mem_restrictWeightAtMost.mp
      (AffineMarkRows.row_cap _ _ _ _ _ _ hA hB hC _ _ _ (e none)) e.some (MvPolynomial.mem_support_iff.mpr live)
    rwa [← Finsupp.degree_eq_weight_one] at c
  have tests (z : ↥S) : WordSurfaceMarks.hits (P z) R = WordSurfaceMarks.hits (point F z.val) (rows M N d) := by
    ext i
    rw [WordSurfaceMarks.hit, WordSurfaceMarks.hit]
    change MvPolynomial.eval (fun j => Option.elim j _ _) (R i) = 0 ↔ _
    rw [MvPolynomial.optionEquivLeft_elim_eval, show MvPolynomial.optionEquivLeft FX (Fin 2) (R i) =
      equation M N d i from AlgEquiv.apply_symm_apply .., Polynomial.eval_map]
    change NonlinearMarkRows.evaluate (seedPoint (M.label z.val)) (K1_14.atX (F.scalar z.val))
      (equation M N d i) = 0 ↔ MvPolynomial.eval (point F z.val) (rows M N d i) = 0
    rw [← OdeSurfaceBridge.read]
    rfl
  obtain ⟨enough, shared⟩ := nodal_count_hypotheses F sub N gp affine d physical dp owners
  have enough' (z : ↥S) : a ≤ (WordSurfaceMarks.hits (P z) R).card := by
    rw [tests z]; exact enough z
  have shared' (x y : ↥S) (ne : x ≠ y) :
      ((WordSurfaceMarks.hits (P x) R) ∩ (WordSurfaceMarks.hits (P y) R)).card ≤ d := by
    rw [tests x, tests y]; exact shared x y ne
  have result := WordUnconstrainedPrice.affine P R 1 (d*width) a d gap bound
    enough' shared'
  rw [Fintype.card_coe] at result
  exact add_fee F N _ _ _ result (total_fee F N gp affine width hA small)

#print axioms rectangular
#print axioms projected
#print axioms single_seed
#print axioms fixed
#print axioms price
theorem price_floor {u deleted maxHeight a} {M:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (F:P1.FamilyAt a M Γ) (sub:T⊆Γ) {parents:Finset Surface} {G:Pade.Row SeedField}
    (N:Native G) (gp:G.primitive) (affine:G.graphDegree=1) (width:ℕ) (wp:0<width)
    (total:∀ j i,(N.poly.coeff j).coeff i∈MvPolynomial.restrictWeightAtMost (fun _=>1) width)
    (small:width<p) (d:ℕ) (physical:(131071:ℤ)+M.overhead≤d) (dp:d<p)
    (pos:0<d) (gap:d<a) (an:a≤262144) (owners:Owned F T parents N) :
    T.card≤p*width+(3*(d*width)^2*(262144-d)^3)/(a-d)^3 := by
  have bound:=price F sub N gp affine width total small d physical dp gap owners
  unfold side at bound
  have card : Fintype.card I=262144 := Fintype.card_fin (2^18)
  rw [card] at bound
  have c:=NativeAffineLedger.three_floor (n:=262144) (a:=a) (d:=d) (marks:=T.card) (fee:=p*width)
    (c:=3) (h₀:=d*width) (h₁:=d*width) gap an (by simpa only [pow_two,Nat.mul_assoc] using bound)
  have positive:1≤d*width:=Nat.mul_le_mul pos wp
  rw [max_eq_right positive] at c
  simpa only [pow_two,Nat.mul_assoc] using c
#print axioms price_floor
end
end Research6966.NativeAffineTariff
