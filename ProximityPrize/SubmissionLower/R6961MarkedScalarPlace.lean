import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import ProximityPrize.SubmissionLower.KoalaRectCutoff
import Mathlib.RingTheory.Localization.Integer
import ProximityPrize.SubmissionLower.R6960MarkedSheet
import ProximityPrize.SubmissionLower.R6961Front6961PoleChart
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6960MarkedScalarPlace
import Mathlib.FieldTheory.Galois.Basic
import ProximityPrize.SubmissionLower.R6960CollisionTameBranch
import Mathlib.RingTheory.Valuation.LocalSubring

set_option Elab.async false

-- merged module R6961RetainedCompressionProjection
section Merged_R6961RetainedCompressionProjection

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

namespace Lower6961.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L FX Equation Seeds seedEmbedding graphEval atX)
open CurvatureSquares (Ordinate zView ordEval)
open KoalaRect (axisDegree axisDegree_le_iff)
open scoped Polynomial nonZeroDivisors

abbrev RationalOrdinate := Polynomial (Polynomial FX)

abbrev incl := algebraMap (Polynomial L) FX

private def graph : Seeds →+* (Polynomial FX) := (K1_14.frobeniusGraph (F := FX) p).toRingHom

/-- The graph map is applied to the original rational coefficients. -/
def project (f : Equation) : RationalOrdinate := f.map graph

def intoFraction (P : Ordinate) : RationalOrdinate :=
  P.map ((mapRingHom incl).comp Bivariate.swap.toRingHom)

private theorem incl_inj : Function.Injective incl := IsFractionRing.injective (Polynomial L) FX

private theorem coeff_into (P : Ordinate) (i j : ℕ) :
    ((intoFraction P).coeff i).coeff j = incl ((Bivariate.swap (P.coeff i)).coeff j) := by
  simp [intoFraction]

private theorem into_degree (P : Ordinate) : (intoFraction P).natDegree=P.natDegree :=
  natDegree_map_eq_of_injective ((Polynomial.map_injective incl incl_inj).comp Bivariate.swap.injective) P

private theorem degree_project (f : Equation) (small : axisDegree f 0<p) :
    (project f).natDegree=f.natDegree := by
  by_cases nz : f=0
  · simp [nz,project]
  apply natDegree_map_of_leadingCoeff_ne_zero graph
  exact K1_14.frobeniusGraph_ne_zero p (by decide) f.leadingCoeff
    (leadingCoeff_ne_zero.mpr nz) (((axisDegree_le_iff f 0 _).mp le_rfl f.natDegree).trans_lt small)

private theorem projected_coeff (f : Equation) (i : ℕ) :
    ((project f).coeff i).natDegree≤axisDegree f 0+p*axisDegree f 1 := by
  rw [project, coeff_map]
  exact K1_14.frobeniusGraph_degree p _ _ (f.coeff i)
    ((axisDegree_le_iff f 0 _).mp le_rfl i) ((axisDegree_le_iff f 1 _).mp le_rfl i)

private theorem graph_eval (z : K) :
    (evalRingHom (seedEmbedding z)).comp graph=graphEval z := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [graph, K1_14.frobeniusGraph, graphEval]
  · intro i
    fin_cases i <;> simp [graph, K1_14.frobeniusGraph, graphEval]

theorem specialize_project (f : Equation) (z : K) :
    (project f).map (evalRingHom (seedEmbedding z))=f.map (graphEval z) := by
  rw [project, Polynomial.map_map, graph_eval]

/-- Clear denominators in the abscissa without increasing either the ordinate
or scalar degree. The identity holds over the original fraction field. -/
theorem clear_abscissa (G : RationalOrdinate) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ intoFraction P=C (C (incl d))*G := by
  classical
  let S := G.support.sigma (fun i => (G.coeff i).support)
  let coeffs (x : Σ _ : ℕ, ℕ) : FX := (G.coeff x.1).coeff x.2
  let den := IsLocalization.commonDenom (nonZeroDivisors (Polynomial L)) S coeffs
  let ints := IsLocalization.integerMultiple (nonZeroDivisors (Polynomial L)) S coeffs
  let value (i j : ℕ) : (Polynomial L) := if h : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ S then ints ⟨⟨i,j⟩,h⟩ else 0
  let raw : Ordinate :=
    ∑ i∈G.support, monomial i (∑ j∈(G.coeff i).support, monomial j (value i j))
  let P := raw.map Bivariate.swap.toRingHom
  have degree (i j : ℕ) : (raw.coeff i).coeff j = value i j := by
    by_cases hi : i∈G.support
    · by_cases hj : j∈(G.coeff i).support
      · simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
          hi, hj]
      · have hnot : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∉ S := fun m => hj (Finset.mem_sigma.mp m).2
        simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
          hi, hj, value, hnot]
    · have hnot : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∉ S := fun m => hi (Finset.mem_sigma.mp m).1
      simp [raw, Polynomial.finsetSum_coeff, coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq',
        hi, value, hnot]
  refine ⟨den,P,nonZeroDivisors.coe_ne_zero den,?_⟩
  ext i j
  rw [coeff_into,show P.coeff i=Bivariate.swap (raw.coeff i) from coeff_map ..,
    Bivariate.swap_swap_apply, degree, coeff_C_mul, coeff_C_mul]
  by_cases h : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ S
  · have prop := IsLocalization.map_integerMultiple (nonZeroDivisors (Polynomial L)) S coeffs ⟨⟨i,j⟩,h⟩
    change incl (ints ⟨⟨i,j⟩,h⟩)=(den : (Polynomial L)) • (G.coeff i).coeff j at prop
    rw [Algebra.smul_def] at prop
    simpa only [value, dite_eq_left h] using prop
  · have zero : (G.coeff i).coeff j=0 := by
      by_contra ne
      have hj := mem_support_iff.mpr ne
      exact h (Finset.mem_sigma.mpr ⟨mem_support_iff.mpr (fun z => by simpa [z] using ne),hj⟩)
    simp [value, h,zero]

/-- A scalar specialization of a cleared ordinate polynomial, with the
abscissa polynomial kept as its coefficient ring. -/
def specialize (P : Ordinate) (z : L) : Polynomial (Polynomial L) :=
  P.map (mapRingHom (evalRingHom z))

theorem eval_swap {F : Type*} [Field F] (Q : Polynomial (Polynomial F)) (z : F) :
    (Bivariate.swap Q).eval (C z) = Q.map (evalRingHom z) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, eval_add, hP, hQ, Polynomial.map_add]
  | monomial n a =>
    rw [Bivariate.swap_monomial, eval_mul, eval_C, eval_map_apply, map_monomial,
      coe_evalRingHom, C_mul_X_pow_eq_monomial]

theorem specialize_into (P : Ordinate) (z : L) :
    (intoFraction P).map (evalRingHom (incl (C z)))=(specialize P z).map incl := by
  ext i
  simp only [intoFraction, specialize, coeff_map, RingHom.comp_apply, coe_mapRingHom,
    coe_evalRingHom, eval_map]
  change (Bivariate.swap (P.coeff i)).eval₂ incl (incl (C z)) =
    incl ((P.coeff i).map (evalRingHom z))
  have mapped := Polynomial.hom_eval₂ (p := Bivariate.swap (P.coeff i))
    (f := RingHom.id (Polynomial L)) (g := incl) (C z)
  rw [RingHom.comp_id] at mapped
  rw [← mapped]
  exact congrArg incl (eval_swap (P.coeff i) z)

private theorem z_coeff (P : Ordinate) (i j : ℕ) :
    ((zView P).coeff j).coeff i = (Bivariate.swap (P.coeff i)).coeff j := by
  change ((Bivariate.swap (P.map Bivariate.swap.toRingHom)).coeff j).coeff i =
    (Bivariate.swap (P.coeff i)).coeff j
  rw [CurvatureSquares.coeff_swap, coeff_map]
  rfl

/-- An integral projected polynomial carries the terminal equation's exact
ordinate degree and the shared scalar-degree cap. -/
theorem integral_project (f : Equation) (nz : f≠0) (small : axisDegree f 0<p) :
    ∃ (d : (Polynomial L)) (P : Ordinate), d≠0 ∧ P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤axisDegree f 0+p*axisDegree f 1 ∧
      ∀ z : K, (specialize P (algebraMap K L z)).map incl = C (incl d)*f.map (graphEval z) := by
  obtain ⟨d,P,hd,eq⟩ := clear_abscissa (project f)
  have dn : incl d≠0 := (map_ne_zero_iff incl incl_inj).mpr hd
  have pn : project f≠0 := by
    intro z
    have hl := degree_project f small
    unfold project at z
    have killed := congrArg (fun V : RationalOrdinate => V.coeff f.natDegree) z
    have hp : graph f.leadingCoeff≠0 :=
      K1_14.frobeniusGraph_ne_zero p (by decide) _ (leadingCoeff_ne_zero.mpr nz)
        (((axisDegree_le_iff f 0 _).mp le_rfl f.natDegree).trans_lt small)
    exact hp (by simpa only [coeff_map,coeff_natDegree,coeff_zero] using killed)
  refine ⟨d,P,hd,fun h => ?_,?_,?_,?_⟩
  · rw [h,intoFraction,Polynomial.map_zero] at eq
    exact (mul_ne_zero (C_ne_zero.mpr (C_ne_zero.mpr dn)) pn) eq.symm
  · rw [← into_degree P,eq,natDegree_C_mul (C_ne_zero.mpr dn),degree_project f small]
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    apply Polynomial.ext
    intro i
    rw [z_coeff,coeff_zero]
    apply incl_inj
    rw [← coeff_into,eq,coeff_C_mul,coeff_C_mul,coeff_eq_zero_of_natDegree_lt
      ((projected_coeff f i).trans_lt hj),mul_zero,map_zero]
  · intro z
    have label : incl (C (algebraMap K L z))=seedEmbedding z := rfl
    rw [← specialize_into, label, eq, Polynomial.map_mul, Polynomial.map_C, specialize_project]
    simp only [coe_evalRingHom, eval_C]

#print axioms integral_project
end
end Lower6961.RetainedCompression

end Merged_R6961RetainedCompressionProjection

-- merged module R6961RetainedCompressionFactors
section Merged_R6961RetainedCompressionFactors

set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000

namespace Lower6961.RetainedCompression
noncomputable section
open Polynomial Finset
open K1 (K p)
open K1_14 (L FX Equation graphEval atX liftPoly)
open CurvatureSquares (Ordinate zView zView_inj ordEval)
open KoalaRect (axisDegree)
open Lower6961.RescueGeometry (Model Family)
open RetainedShortening (Word)
open scoped Polynomial

structure MarkedFiber (P : Ordinate) (z : L) (S : (Polynomial L)) : Prop where
  full : (specialize P z).natDegree=P.natDegree
  separable : ((specialize P z).map incl).Separable
  root : (specialize P z).eval S=0

abbrev scalar {u deleted} (M : Model u deleted) (γ : K) : L := algebraMap K L (M.label γ)

theorem scalar_injective {u deleted} (M : Model u deleted) : Function.Injective (scalar M) :=
  (algebraMap K L).injective.comp (Lower6961.RescueGeometry.label_injective M)

def simpleSheet (f : Equation) (label : K) (word : (Polynomial K)) : Prop :=
  let q:=f.map (graphEval label)
  q.natDegree=f.natDegree ∧ q.Separable ∧
  ∃ H Q : (Polynomial FX), q=(Polynomial.X-C (atX word))*Q ∧ H.eval (atX word)=1 ∧ Q∣H ∧
    let e:=AdjoinRoot.mk q H
    e^2=e ∧ e≠0 ∧ e≠1

/-- The actual high marks give integral projected equations with squarefree,
full-degree fibres at every retained label. -/
theorem marked_projection {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (f : Equation) (sub : T⊆Γ)
    (d hMax axesCap : ℕ) (haxesSmall : axesCap < p) (hdegFit : 131071 + hMax ≤ d)
    (degree : 3≤f.natDegree) (axes : axisDegree f 0+axisDegree f 1≤axesCap)
    (hi : M.overhead.toNat≤hMax)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    Word 179798 d M.word F.scalar T ∧
    ∃ P : Ordinate, P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤axisDegree f 0+p*axisDegree f 1 ∧
      ∀ γ∈T, MarkedFiber P (scalar M γ) (liftPoly (F.scalar γ)) := by
  have nz : f≠0 := by intro h; simp [h] at degree
  have small : axisDegree f 0<p := by omega
  obtain ⟨D,P,dn,pn,deg,cap,called⟩ := integral_project f nz small
  refine ⟨⟨F.distinct.mono sub,?_,?_⟩,P,pn,deg,cap,?_⟩
  · intro γ hγ
    rcases (F.mark γ (sub hγ)).scalar_degree with z | bound
    · simp [z]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      have hh : M.overhead≤(hMax : ℤ) := by omega
      omega
  · intro γ hγ
    let mark := F.mark γ (sub hγ)
    exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
  · intro γ hγ
    have eq := called (M.label γ)
    have dnon : incl D≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) FX)).mpr dn
    have native := marks γ hγ
    change (f.map (graphEval (M.label γ))).natDegree=f.natDegree ∧
      (f.map (graphEval (M.label γ))).Separable ∧ _ at native
    obtain ⟨full,sep,H,Q,fac,_⟩ := native
    have root : (f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0 := by
      rw [fac,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul]
    have smap : ((specialize P (scalar M γ)).map incl).natDegree =
        (specialize P (scalar M γ)).natDegree :=
      natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX) _
    refine ⟨?_,?_,?_⟩
    · rw [← smap,eq,natDegree_C_mul dnon,full,deg]
    · rw [eq]
      exact sep.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr dnon))
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq, map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr root)

theorem split_fibre {P Q : Ordinate} {z : L} {S : (Polynomial L)}
    (pn : P≠0) (qn : Q≠0) (H : MarkedFiber (P*Q) z S) :
    MarkedFiber P z S ∨ MarkedFiber Q z S := by
  have eq : specialize (P*Q) z=specialize P z*specialize Q z := by simp [specialize]
  have pair : ((specialize P z).map incl*(specialize Q z).map incl).Separable := by
    simpa only [eq,Polynomial.map_mul] using H.separable
  have left := pair.of_mul_left
  have right := pair.of_mul_right
  have pz : specialize P z≠0 := fun h => left.ne_zero (by rw [h,Polynomial.map_zero])
  have qz : specialize Q z≠0 := fun h => right.ne_zero (by rw [h,Polynomial.map_zero])
  have sum := H.full
  rw [eq,natDegree_mul pn qn,natDegree_mul pz qz] at sum
  have pl : (specialize P z).natDegree≤P.natDegree := natDegree_map_le
  have ql : (specialize Q z).natDegree≤Q.natDegree := natDegree_map_le
  have zr := H.root
  rw [eq,eval_mul,mul_eq_zero] at zr
  exact zr.imp (fun root => ⟨by omega,left,root⟩) (fun root => ⟨by omega,right,root⟩)

/-- The assignments preserve full specialization and separability, and charge
each label only once. The two budgets add on actual irreducible factors. -/
theorem aggregate {ι : Type*} (P : Ordinate) (T : Finset ι) (z : ι → L) (S : ι → Polynomial L)
    (rate additive : ℕ) (nz : P≠0)
    (marks : ∀ γ∈T, MarkedFiber P (z γ) (S γ))
    (price : ∀ Q : Ordinate, Irreducible Q → Q∣P → ∀ U⊆T,
      (∀ γ∈U, MarkedFiber Q (z γ) (S γ)) →
      U.card≤rate*(zView Q).natDegree+additive*Q.natDegree) :
    T.card≤rate*(zView P).natDegree+additive*P.natDegree := by
  classical
  induction P using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => exact (nz rfl).elim
  | unit P unit =>
    have empty : T=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro γ hγ
      have units : IsUnit (specialize P (z γ)) :=
        unit.map (mapRingHom (mapRingHom (evalRingHom (z γ))))
      exact (units.map (evalRingHom (S γ))).ne_zero (marks γ hγ).root
    simp [empty]
  | mul Q P qn irr ih =>
    let U := T.filter (fun γ => MarkedFiber Q (z γ) (S γ))
    let V := T\U
    have us : U⊆T := filter_subset _ _
    have vs : V⊆T := sdiff_subset
    have pU := ih _ qn (fun γ hγ => (mem_filter.mp hγ).2)
      (fun f hI hD R hR hM => price f hI (hD.trans (show Q ∣ P*Q from ⟨P, mul_comm P Q⟩)) R (hR.trans us) hM)
    have pV := price P irr (show P ∣ P*Q from ⟨Q,rfl⟩) V vs (by
      intro γ hγ
      exact (split_fibre irr.ne_zero qn (marks γ (vs hγ))).resolve_right
        (fun h => (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨vs hγ,h⟩)))
    change U.card≤rate*(zView Q).natDegree+additive*Q.natDegree at pU
    have sum := card_sdiff_add_card_eq_card us
    change V.card+U.card=T.card at sum
    rw [map_mul,natDegree_mul ((map_ne_zero_iff _ zView_inj).mpr irr.ne_zero)
      ((map_ne_zero_iff _ zView_inj).mpr qn),natDegree_mul irr.ne_zero qn]
    simp only [Nat.mul_add]
    omega

/-- Ordinate-independent factors cannot carry a mark whose full specialization
is nonzero. -/
theorem no_zero_degree {P : Ordinate} {z : L} {S : (Polynomial L)}
    (H : MarkedFiber P z S) : 0<P.natDegree := by
  by_contra! hm
  have hz : (specialize P z).natDegree=0 := H.full.trans (Nat.eq_zero_of_le_zero hm)
  have eq := eq_C_of_natDegree_eq_zero hz
  have h := H.root
  rw [eq,eval_C] at h
  exact H.separable.ne_zero (by rw [eq,h,C_0,Polynomial.map_zero])

private theorem specialize_constant {P : Ordinate} (zero : (zView P).natDegree=0) (z : L) :
    specialize P z=specialize P 0 := by
  apply Polynomial.map_injective incl (IsFractionRing.injective (Polynomial L) FX)
  rw [← specialize_into,← specialize_into]
  ext i
  have coeffz : (Bivariate.swap (P.coeff i)).natDegree=0 :=
    Nat.eq_zero_of_le_zero ((CurvatureSquares.coeff_caps P i).2.trans (zero.le))
  have eq : (intoFraction P).coeff i=C (incl ((Bivariate.swap (P.coeff i)).coeff 0)) := by
    simp only [intoFraction,coeff_map,RingHom.comp_apply,coe_mapRingHom]
    change (Bivariate.swap (P.coeff i)).map incl = _
    conv_lhs => rw [eq_C_of_natDegree_eq_zero coeffz]
    rw [Polynomial.map_C]
  simp only [coeff_map,coe_evalRingHom,eq,eval_C]

/-- A seed-independent factor carries at most its ordinate degree many
distinct polynomial words. -/
theorem constant_price {ι : Type*} (P : Ordinate) (T : Finset ι)
    (z : ι → L) (S : ι → Polynomial L) (inj : Set.InjOn S (T:Set ι))
    (zero : (zView P).natDegree=0) (marks : ∀ γ∈T, MarkedFiber P (z γ) (S γ)) :
    T.card≤P.natDegree := by
  classical
  rcases T.eq_empty_or_nonempty with em | ⟨γ,hγ⟩
  · simp [em]
  let Q := specialize P 0
  have qn : Q≠0 := by
    intro ne
    have h := (marks γ hγ).separable.ne_zero
    rw [specialize_constant zero,show specialize P 0=0 from ne,Polynomial.map_zero] at h
    exact h rfl
  have D : Q.natDegree=P.natDegree := by
    simpa only [specialize_constant zero (z γ),Q] using (marks γ hγ).full
  rw [← D, ← card_image_of_injOn inj]
  apply Polynomial.card_le_degree_of_subset_roots (p:=Q)
  intro v hv
  obtain ⟨η,hη,rfl⟩ := mem_image.mp hv
  exact (Polynomial.mem_roots qn).mpr (by
    simpa only [Polynomial.IsRoot,specialize_constant zero (z η),Q] using (marks η hη).root)

end
end Lower6961.RetainedCompression

end Merged_R6961RetainedCompressionFactors

-- merged module R6961MarkedEvaluationLedger
section Merged_R6961MarkedEvaluationLedger

set_option Elab.async false
namespace Lower6961.MarkedEvaluation
open RetainedCompression

/-- Charge for counting a single determinant evaluated at multiple abscissas.
The extra eight scalar-degree units per complementary sheet fit the live rectangles. -/
def rate (e:ℕ) := (9*e+2)*(e-1)+2*e-1

/-- At twist s-1, the generic vertical section rank is at most e*s-s.
A marked sheet contributes s residues before its normalization-index loss.
The shared determinant can spend one e-th of a pole per evaluation row. -/
theorem price {N e s t loss obstructions ordinary meromorphic rank pole : ℕ}
    (positive : 0<s) (ep : 0<e) (rank_bound : rank+s≤e*s)
    (collision : loss≤8*s*t) (surface : obstructions≤s+s*t) (constants : s≤ordinary)
    (lift : N*s+ordinary≤loss+obstructions+meromorphic)
    (generated : meromorphic≤rank+pole) (orbit : e*pole≤N*rank) :
    N≤9*e*t+e*(e-1) := by
  have before : N*s+ordinary ≤ 8*s*t+(s+s*t)+(rank+pole) :=
    lift.trans (Nat.add_le_add (Nat.add_le_add collision surface) generated)
  have cancel : N*s ≤ 8*s*t+s*t+rank+pole := by omega
  have scaled := Nat.mul_le_mul_left e cancel
  have share := Nat.mul_le_mul_left N rank_bound
  have rankCost:=Nat.mul_le_mul_left e rank_bound
  have first : (N*s)*e ≤ (8*s*t+s*t)*e+e*rank+N*rank := by
    calc _ = e*(N*s) := Nat.mul_comm ..
         _ ≤ _ := scaled.trans (by nlinarith only [orbit])
  have paid : N*s+s*e≤9*e*t*s+(e*e)*s := by nlinarith only [first,share,rankCost]
  have equal : 9*e*t*s+(e*e)*s=(9*e*t+e*(e-1))*s+s*e := by
    obtain ⟨k,eq⟩:=Nat.exists_eq_succ_of_ne_zero ep.ne'
    rw [eq,Nat.succ_sub_one,Nat.succ_eq_add_one]; ring
  rw [equal] at paid
  exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right paid) positive

#print axioms price
end Lower6961.MarkedEvaluation

end Merged_R6961MarkedEvaluationLedger

-- merged module R6961MarkedEvaluationDeterminant
section Merged_R6961MarkedEvaluationDeterminant

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Finset Matrix Polynomial
open scoped Matrix BigOperators Polynomial

/-- Every cleared row from an unmarked sheet is divisible by the base parameter.
This contributes a whole parameter power, including at a ramified place. -/
theorem cleared_rows {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
    (π:R) (A:Matrix J J R) (rows:Finset J) (row : ∀ i∈rows,∀ j,π∣A i j) : π^rows.card∣A.det := by
  classical
  let c (i:J):=if i∈rows then π else 1
  have factors (i j:J) : c i∣A i j := by
    by_cases h:i∈rows
    · simpa [c,h] using row i h j
    · simp [c,h]
  choose B eq using factors
  have mat : A=Matrix.of (fun i j=>c i*B i j) := Matrix.ext (fun i j=>eq i j)
  have product : (∏ i,c i)=π^rows.card := by
    simp [c]
  rw [mat,Matrix.det_mul_column,product]
  exact dvd_mul_right ..

/-- Each row may use a different horizontal evaluation. Transitivity on the
sheets for that row determines its contribution to the average regardless of
correlations with all other rows. -/
theorem row_average {G J : Type*} [Group G] [Fintype G] [Fintype J] (I:J→Type*)
    [∀ j,Fintype (I j)] [∀ j,DecidableEq (I j)] [∀ j,MulAction G (I j)]
    [∀ j,MulAction.IsPretransitive G (I j)] (e:ℕ) (degree:∀ j,Fintype.card (I j)=e)
    (pick mark:∀ j,I j) :
    e*(∑ g:G,(Finset.univ.filter (fun j=>g • pick j≠mark j)).card)=
      Fintype.card G*((e-1)*Fintype.card J) := by
  classical
  let b (g:G) (j:J):ℕ:=if g • pick j≠mark j then 1 else 0
  have each (j:J) : e*(∑g:G,b g j)=Fintype.card G*(e-1) := by
    have eq:=Lower6960.MarkedSheet.omission (G:=G) ({mark j}:Finset (I j)) (pick j)
    simpa only [degree,Finset.card_singleton,Finset.mem_singleton,b] using eq
  calc _ = e*(∑g:G,∑j:J,b g j) := by simp only [b,Finset.sum_boole, Nat.cast_id]
       _ = ∑j:J,e*(∑g:G,b g j) := by rw [Finset.sum_comm,Finset.mul_sum]
       _ = _ := by simp only [each,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]; ring

/-- One descended determinant bounds the degree of the scalar bundle generated by
the meromorphic sections. Each chosen abscissa contributes at most one sheet's
share of a pole. -/
theorem pole_degree {K G J : Type*} [Field K] [Group G] [Fintype G] [Fintype J] [DecidableEq J]
    (e d : ℕ) (ep : 0<e) (T:Finset K) (P:(Polynomial K)) (nz:P≠0)
    (cap : P.natDegree+Fintype.card G*d≤Fintype.card G*(T.card*Fintype.card J))
    (O:K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (φ:∀ z,(Polynomial K)→+*O z) (π:∀z,O z) (place:∀ z∈T,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (A:∀ z,G→Matrix J J (O z)) (rows:K→G→Finset J)
    (norm:∀ z∈T,φ z P=∏g:G,(A z g).det)
    (hits:∀ z∈T,∀g,∀i∈rows z g,∀j,π z∣A z g i j)
    (avg:∀ z∈T,e*(∑g:G,(rows z g).card)=Fintype.card G*((e-1)*Fintype.card J)) :
    e*d≤T.card*Fintype.card J := by
  classical
  have atZ (z) (hz:z∈T) : Fintype.card G*((e-1)*Fintype.card J)≤e*P.rootMultiplicity z := by
    have dv : π z^(∑g:G,(rows z g).card)∣φ z P := by
      rw [norm z hz,←Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ (fun g _=>cleared_rows (π z) _ _ (hits z hz g))
    have pz:=place z hz
    exact (avg z hz) ▸ Nat.mul_le_mul_left e
      ((Lower6960.SheetDeterminant.base_parameter_order (φ z) z (π z) pz.1 pz.2.1 pz.2.2 nz _).mp dv)
  have total := Finset.sum_le_sum atZ
  simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at total
  simp only [Nat.cast_id] at total
  have low:=total.trans (Nat.mul_le_mul_left e
    (ProximityPrize.SubmissionLower.MatrixRootMultiplicity.sum_rootMultiplicity_le_natDegree P T))
  have high:=Nat.mul_le_mul_left e cap
  have es : e-1+1=e := Nat.sub_add_cancel ep
  have sh : Fintype.card G * (e*d) ≤ Fintype.card G*(T.card*Fintype.card J) := by
    have expand : Fintype.card G*(T.card*Fintype.card J)*e =
        T.card*(Fintype.card G*((e-1)*Fintype.card J))+Fintype.card G*(T.card*Fintype.card J) := by
      conv_lhs => rhs; rw [←es]
      ring
    nlinarith only [low,high,expand]
  exact Nat.le_of_mul_le_mul_left sh Fintype.card_pos

#print axioms cleared_rows
#print axioms row_average
#print axioms pole_degree
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedEvaluationDeterminant

-- merged module R6961MarkedEvaluationNorm
section Merged_R6961MarkedEvaluationNorm

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Algebra Module Finset Matrix
open scoped Polynomial BigOperators
variable {K E : Type*} [Field K] [DecidableEq (RatFunc K)] [Field E]
  [Algebra (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
  [Algebra (Polynomial K) E] [IsScalarTower (Polynomial K) (RatFunc K) E]
  [Algebra (Lower6960.SheetNorm.Infinity K) E] [IsScalarTower (Lower6960.SheetNorm.Infinity K) (RatFunc K) E]

/-- A determinant with a zero of order d at scalar infinity, after its common
degree-b clearing, pays b-d degrees in the base norm. -/
theorem norm_degree (v:E) (nz:v≠0) (finite:IsIntegral (Polynomial K) v) (b d:ℕ)
    (inf:IsIntegral (Lower6960.SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^d*v/
      algebraMap (RatFunc K) E (RatFunc.X^b))) :
    ∃ P:(Polynomial K),P≠0 ∧ algebraMap (Polynomial K) (RatFunc K) P=norm (RatFunc K) v ∧
      P.natDegree+finrank (RatFunc K) E*d≤finrank (RatFunc K) E*b := by
  let ι:=algebraMap (RatFunc K) E
  let j:=algebraMap (Polynomial K) (RatFunc K)
  have xi:IsIntegral (Polynomial K) (ι RatFunc.X) := by
    rw [←RatFunc.algebraMap_X,←IsScalarTower.algebraMap_apply]; exact isIntegral_algebraMap
  have xn:ι RatFunc.X≠0 := (map_ne_zero_iff _ ι.injective).mpr RatFunc.X_ne_zero
  obtain ⟨Q,qn,hq,degree⟩:=Lower6960.SheetNorm.polynomial_norm ((ι RatFunc.X)^d*v)
    (mul_ne_zero (pow_ne_zero _ xn) nz) ((xi.pow _).mul finite) b inf
  obtain ⟨P,hP⟩:=IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (RatFunc K) finite)
  have pn:P≠0 := by
    intro zero; apply (Algebra.norm_ne_zero_iff (R:=RatFunc K)).mpr nz; rw [←hP,zero,map_zero]
  have eq : Q=(Polynomial.X:(Polynomial K))^(d*finrank (RatFunc K) E)*P := by
    apply IsFractionRing.injective (Polynomial K) (RatFunc K)
    simp only [hq,ι,map_mul,map_pow,RatFunc.algebraMap_X,hP,Algebra.norm_algebraMap,←pow_mul,Nat.mul_comm d]
  rw [eq,natDegree_mul (pow_ne_zero _ X_ne_zero) pn,natDegree_pow,natDegree_X,mul_one] at degree
  exact ⟨P,pn,hP,by simpa only [Nat.mul_comm d,Nat.add_comm] using degree⟩

theorem conjugate_bound [IsGalois (RatFunc K) E] {J : Type*} [Fintype J] [DecidableEq J]
    (e d:ℕ) (ep:0<e) (T:Finset K) (B:Matrix J J E)
    (det:B.det≠0) (finite:IsIntegral (Polynomial K) B.det)
    (inf:IsIntegral (Lower6960.SheetNorm.Infinity K) ((algebraMap (RatFunc K) E RatFunc.X)^d*B.det/
      algebraMap (RatFunc K) E (RatFunc.X^(T.card*Fintype.card J))))
    (O:K→Type*) [∀ z,CommRing (O z)] [∀ z,IsDomain (O z)] [∀ z,IsLocalRing (O z)]
    (φ:∀z,(Polynomial K)→+*O z) (incl:∀z,O z→+*E) (inj:∀z,Function.Injective (incl z))
    (base:∀z,(incl z).comp (φ z)=(algebraMap (RatFunc K) E).comp (algebraMap (Polynomial K) (RatFunc K)))
    (π:∀z,O z) (place:∀ z∈T,π z≠0 ∧ IsLocalRing.residue _ (π z)=0 ∧ φ z (Polynomial.X-C z)=π z)
    (A:∀z,Lower6960.SheetNorm.Aut K E→Matrix J J (O z)) (row:K→Lower6960.SheetNorm.Aut K E→Finset J)
    (lift:∀ z∈T,∀g i j,incl z (A z g i j)=g (B i j))
    (outside:∀ z∈T,∀g,∀i∈row z g,∀j,π z∣A z g i j)
    (count:∀ z∈T,e*(∑g:Lower6960.SheetNorm.Aut K E,(row z g).card)=
      Fintype.card (Lower6960.SheetNorm.Aut K E)*((e-1)*Fintype.card J)) :
    e*d≤T.card*Fintype.card J := by
  obtain ⟨P,pn,eq,cap⟩:=norm_degree B.det det finite _ _ inf
  have size:Fintype.card (Lower6960.SheetNorm.Aut K E)=finrank (RatFunc K) E := by
    rw [Fintype.card_eq_nat_card,IsGalois.card_aut_eq_finrank]
  apply pole_degree e d ep T P pn (size ▸ cap) O φ π place A row _ outside count
  intro z hz
  apply inj z
  have mapP := DFunLike.congr_fun (base z) P
  change incl z (φ z P)=algebraMap (RatFunc K) E (algebraMap (Polynomial K) (RatFunc K) P) at mapP
  rw [mapP,eq,Algebra.norm_eq_prod_automorphisms,map_prod]
  apply Finset.prod_congr rfl
  intro g _
  rw [RingHom.map_det,AlgEquiv.map_det]
  exact congrArg Matrix.det (Matrix.ext (fun i j=>(lift z hz g i j).symm))

#print axioms norm_degree
#print axioms conjugate_bound
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedEvaluationNorm

-- merged module R6961MarkedPrimitiveMinor
section Merged_R6961MarkedPrimitiveMinor

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
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
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedPrimitiveMinor

-- merged module R6961MarkedHorizontalRows
section Merged_R6961MarkedHorizontalRows

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Module Matrix LinearMap Finset
open scoped Polynomial Matrix BigOperators
open P1_7_1_1_2 (exists_full_minor)
variable {k K I J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Fintype I] [Fintype J] [DecidableEq J]

/-- Distinct abscissas can all be translates of one transcendental variable.
There is already a nonzero coordinate minor of the desired size after evaluating
that variable at zero. The shifts lie in the original ground field k. -/
theorem translated_minor (P:Matrix I J (Polynomial K)) (li:LinearIndependent K P.col) :
    ∃ N:ℕ, ∃ shifts:Fin N ↪ k, ∃ rows:J↪(Fin N×I),
      (Matrix.of (fun u v:J=>Polynomial.taylor (algebraMap k K (shifts (rows u).1)) (P (rows u).2 v))).det≠0 := by
  classical
  let m:=Finset.univ.sup (fun ij:I×J=>(P ij.1 ij.2).natDegree)
  let pts:Fin (m+1)↪k := Fin.valEmbedding.trans (Infinite.natEmbedding k)
  let val:Fin (m+1)↪K := pts.trans ⟨_,(algebraMap k K).injective⟩
  let V:=degreeLT K (m+1)
  let C (j:J) (i:I):V:=⟨P i j,mem_degreeLT.mpr (degree_le_natDegree.trans_lt
    (by exact_mod_cast Nat.lt_succ_of_le (show (P i j).natDegree≤m from Finset.le_sup (f:=fun ij:I×J=>(P ij.1 ij.2).natDegree) (Finset.mem_univ (i,j)))))⟩
  let proj:(I→V) →ₗ[K] (I→(Polynomial K)) := LinearMap.pi (fun i=>V.subtype.comp (LinearMap.proj i))
  have ic:LinearIndependent K C := LinearIndependent.of_comp proj li
  let eval:(I→V) →ₗ[K] ((Fin (m+1)×I)→K) := LinearMap.pi (fun i=>
    (Polynomial.leval (val i.1)).comp (V.subtype.comp (LinearMap.proj i.2)))
  have inj:Function.Injective eval := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro u zero
    funext i;apply Subtype.ext
    by_contra nz
    let S:=Finset.univ.map val
    have roots : S⊆(u i).val.roots.toFinset := by
      intro x hx
      obtain ⟨a,_,rfl⟩:=Finset.mem_map.mp hx
      exact Multiset.mem_toFinset.mpr ((mem_roots nz).mpr (congrFun zero (a,i)))
    have high:= (Finset.card_le_card roots).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
    have d:=(natDegree_lt_iff_degree_lt nz).mpr (mem_degreeLT.mp (u i).property)
    have card : S.card=m+1 := by simp [S]
    omega
  let test : Matrix (Fin (m+1)×I) J K := fun i j=>(P i.2 j).eval (val i.1)
  have independent : LinearIndependent K test.transpose.row := ic.map' eval (LinearMap.ker_eq_bot.mpr inj)
  obtain ⟨rows,good⟩:=P1_7_1_1_2.exists_full_minor test.transpose independent
  refine ⟨m+1,pts,rows,?_⟩
  intro vanish
  let M := Matrix.of (fun u v:J=>Polynomial.taylor (algebraMap k K (pts (rows u).1)) (P (rows u).2 v))
  have eq:(evalRingHom (0:K)).mapMatrix M=(test.transpose.submatrix _root_.id rows).transpose := by
    ext i j
    change (Polynomial.taylor _ _).eval 0=_
    rw [taylor_eval,zero_add];rfl
  apply good
  rw [←Matrix.det_transpose,←eq,←RingHom.map_det]
  exact (congrArg (evalRingHom (0:K)) vanish).trans (map_zero _)

#print axioms translated_minor
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedHorizontalRows

-- merged module R6961MarkedHorizontalBasis
section Merged_R6961MarkedHorizontalBasis

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Module Matrix LinearMap
open scoped Polynomial Matrix BigOperators
open P1_7_1_1_2 (exists_full_minor)
variable {k K F E I J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra K F] [IsScalarTower K (Polynomial K) F]
  [Field E] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def translateField (F:Type) [Field F] [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] (a:K) : F≃+* F :=
  IsFractionRing.ringEquivOfRingEquiv (K:=F) (L:=F) (taylorEquiv a).toRingEquiv

theorem translate_polynomial (a:K) (p:(Polynomial K)) :
    translateField F a (algebraMap (Polynomial K) F p)=algebraMap (Polynomial K) F (taylor a p) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

/-- Independent scalar sections of a finite abscissa field have a nonsingular
coordinate minor on actual translates of X. No bound on their polynomial degrees
in X is part of the hypotheses. -/
theorem section_coordinates (b:Basis I F E) (v:J→E) (li:LinearIndependent K v) :
    ∃ N:ℕ,∃ shifts:Fin N↪k,∃ pick:J↪(Fin N×I),
      (Matrix.of (fun i j:J=>translateField F (algebraMap k K (shifts (pick i).1))
        (b.repr (v j) (pick i).2))).det≠0 := by
  classical
  let inc:=algebraMap (Polynomial K) F
  obtain ⟨d,h⟩:=IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (Polynomial K))
    (fun z:I×J=>b.repr (v z.2) z.1)
  choose q eq using h
  let P:Matrix I J (Polynomial K):=fun i j=>q (i,j)
  have poly (i j):inc (P i j)=inc (d:(Polynomial K))*b.repr (v j) i := by
    simpa only [Algebra.smul_def] using eq (i,j)
  have dn:inc (d:(Polynomial K))≠0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (mem_nonZeroDivisors_iff_ne_zero.mp d.property)
  let lift:(I→(Polynomial K)) →ₗ[K] (I→F) := LinearMap.pi (fun i=>(IsScalarTower.toAlgHom K (Polynomial K) F).toLinearMap.comp (LinearMap.proj i))
  let invert:(I→F) →ₗ[F] E := (inc (d:(Polynomial K)))⁻¹ • b.equivFun.symm.toLinearMap
  let recover:= (invert.restrictScalars K).comp lift
  have coord (j) : lift (P.col j)=inc (d:(Polynomial K)) • b.equivFun (v j) := funext (fun i=>poly i j)
  have vector : recover ∘ P.col =v := by
    funext j
    change (inc (d:(Polynomial K)))⁻¹ • b.equivFun.symm (lift (P.col j))=v j
    rw [coord,map_smul,LinearEquiv.symm_apply_apply,inv_smul_smul₀ dn]
  obtain ⟨N,sh,rows,nonzero⟩:=translated_minor (k:=k) P (LinearIndependent.of_comp recover (vector ▸ li))
  refine ⟨N,sh,rows,?_⟩
  let scale (i:J):=translateField F (algebraMap k K (sh (rows i).1)) (inc (d:(Polynomial K)))
  let V:Matrix J J F:=fun i j=>translateField F (algebraMap k K (sh (rows i).1)) (b.repr (v j) (rows i).2)
  let M:Matrix J J (Polynomial K):=fun i j=>taylor (algebraMap k K (sh (rows i).1)) (P (rows i).2 j)
  have values : inc.mapMatrix M=Matrix.of (fun i j=>scale i*V i j) := by
    ext i j
    change inc (taylor _ _)=_
    rw [←translate_polynomial,poly,map_mul];rfl
  intro vanish
  have zero:=congrArg Matrix.det values
  rw [←RingHom.map_det,Matrix.det_mul_column] at zero
  change V.det=0 at vanish
  exact nonzero ((map_eq_zero_iff _ (IsFractionRing.injective (Polynomial K) F)).mp
    (zero.trans (by rw [vanish,mul_zero])))

/-- Replacing each translated power-basis coordinate block by evaluations on all
distinct sheets preserves full column rank. One ordinary determinant is enough. -/
theorem sheet_minor {H B C : Type} [Field H] [Field B] [Algebra H B] [Fintype C]
    {e:ℕ} (values:Matrix (C×Fin e) J H) (full:∃ pick:J↪(C×Fin e),(values.submatrix pick _root_.id).det≠0)
    (y:C→Fin e→B) (simple:∀c,Function.Injective (y c)) :
    let A:Matrix (C×Fin e) J B:=fun u j=>∑i:Fin e,algebraMap H B (values (u.1,i) j)*(y u.1 u.2)^i.val
    ∃ pick:J↪(C×Fin e),(A.submatrix pick _root_.id).det≠0 := by
  classical
  let A:Matrix (C×Fin e) J B:=fun u j=>∑i:Fin e,algebraMap H B (values (u.1,i) j)*(y u.1 u.2)^i.val
  obtain ⟨sel,sn⟩:=full
  have st: ((algebraMap H B).mapMatrix (values.submatrix sel _root_.id)).det≠0 := by
    rw [←RingHom.map_det];exact (map_ne_zero_iff _ (algebraMap H B).injective).mpr sn
  have inj : Function.Injective A.mulVec := by
    change Function.Injective A.mulVecLin
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have rows (c:C) (i:Fin e) : ∑ j,algebraMap H B (values (c,i) j)*w j=0 := by
      let coeff (d:Fin e):=∑ j,algebraMap H B (values (c,d) j)*w j
      have atRoot (t:Fin e) : (Matrix.vandermonde (y c)*ᵥcoeff) t=0 := by
        have z:=congrFun hw (c,t)
        change (∑ j,(∑d:Fin e,algebraMap H B (values (c,d) j)*(y c t)^d.val)*w j)=0 at z
        change (∑d:Fin e,(y c t)^d.val*(∑ j,algebraMap H B (values (c,d) j)*w j))=0
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul] at z
        simpa only [mul_left_comm,mul_assoc,mul_comm] using z
      have injV:=Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
        (Matrix.det_vandermonde_ne_zero_iff.mpr (simple c)).isUnit)
      have eq:coeff=0:=injV ((funext atRoot).trans (Matrix.mulVec_zero _).symm)
      exact congrFun eq i
    have vec:(algebraMap H B).mapMatrix (values.submatrix sel _root_.id) *ᵥ w=0 := funext (fun i=>rows _ _)
    apply ((Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr st.isUnit)))
    rwa [Matrix.mulVec_zero]
  have li : LinearIndependent B A.transpose.row := Matrix.mulVec_injective_iff.mp inj
  obtain ⟨pick,good⟩:=P1_7_1_1_2.exists_full_minor A.transpose li
  refine ⟨pick,?_⟩
  change (A.submatrix pick _root_.id).det≠0
  rw [←Matrix.det_transpose];exact good

#print axioms section_coordinates
#print axioms sheet_minor
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedHorizontalBasis

-- merged module R6961MarkedSheetFrame
section Merged_R6961MarkedSheetFrame

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency.types false
namespace Lower6961.MarkedEvaluation
open Polynomial Module Matrix Algebra Finset
open scoped Polynomial Matrix BigOperators

variable {F E Ω : Type} [Field F] [Field E] [Algebra F E] [Field Ω]

private def atRoot (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) : E→+*Ω :=
  letI := h.toAlgebra
  (b.lift y hy).toRingHom

private theorem atRoot_base (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) (c:F) :
    atRoot b h y hy (algebraMap F E c)=h c := by
  letI:=h.toAlgebra
  exact (b.lift y hy).commutes c

private theorem atRoot_value (b:PowerBasis F E) (h:F→+*Ω) (y:Ω) (hy:(minpoly F b.gen).eval₂ h y=0) (v:E) :
    atRoot b h y hy v=∑ i:Fin b.dim,h (b.basis.repr v i)*y^i.val := by
  letI := h.toAlgebra
  conv_lhs => arg 2; rw [←b.basis.sum_repr v]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,map_mul,atRoot_base,b.basis_eq_pow,map_pow]
  exact congrArg (h (b.basis.repr v i)*·) (congrArg (·^i.val) (b.lift_gen y hy))

variable {k K J:Type} [Field k] [Infinite k] [Field K] [Algebra k K]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F] [Algebra K F] [IsScalarTower K (Polynomial K) F]
  [Algebra K E] [IsScalarTower K F E] [Fintype J] [DecidableEq J]

/-- One finite separable splitting polynomial provides an independent horizontal
evaluation matrix for the actual functions. Every row is a root-field embedding
extending an abscissa translation, which fixes the scalar parameter field. -/
theorem horizontal_frame_over {F' : Type} [Field F'] (exchange:F≃+*F')
    (b:PowerBasis F E) (simple:(minpoly F b.gen).Separable) (v:J→E) (li:LinearIndependent K v) :
    ∃ p:F'[X],p.Separable ∧ ∃ offsets:J→k, ∃ ev:J→(E→+*p.SplittingField),
      (∀j a,ev j (algebraMap F E a)=algebraMap F' p.SplittingField (exchange (translateField F (algebraMap k K (offsets j)) a))) ∧
      (Matrix.of (fun i j:J=>ev i (v j))).det≠0 := by
  classical
  obtain ⟨N,sh,pick,full⟩:=section_coordinates (k:=k) b.basis v li
  let τ (i:Fin N):=(translateField F (algebraMap k K (sh i))).trans exchange
  let q (i:Fin N):=(minpoly F b.gen).map (τ i).toRingHom
  let polys:=Finset.univ.image q
  let p:=∏ f∈polys,f
  have mon (i) : (q i).Monic := (minpoly.monic b.isIntegral_gen).map _
  have irr (i) : Irreducible (q i) :=
    (MulEquiv.irreducible_iff (Polynomial.mapEquiv (τ i))).mpr (minpoly.irreducible b.isIntegral_gen)
  have sep : p.Separable := by
    apply Polynomial.separable_prod'
    · rintro _ ha _ hb ne
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
      exact (irr i).coprime_iff_not_dvd.mpr
        (fun dv=>ne (eq_of_monic_of_associated (mon i) (mon j) ((irr i).associated_of_dvd (irr j) dv)))
    · rintro _ h
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp h; exact simple.map
  let S:=p.SplittingField
  let incl:=algebraMap F' S
  have splits (i) : ((q i).map incl).Splits := by
    have dvd : q i∣p := Finset.dvd_prod_of_mem _ (Finset.mem_image_of_mem q (Finset.mem_univ i))
    exact Polynomial.Splits.of_dvd (SplittingField.splits p) ((Polynomial.map_ne_zero_iff incl.injective).mpr sep.ne_zero)
      (Polynomial.map_dvd incl dvd)
  have size (i) : Fintype.card ((q i).rootSet S)=b.dim := by
    rw [Polynomial.card_rootSet_eq_natDegree simple.map (splits i),show (q i).natDegree=(minpoly F b.gen).natDegree
      from natDegree_map_eq_of_injective (τ i).injective _,b.natDegree_minpoly]
  let idx (i) := Fintype.equivOfCardEq (show Fintype.card (Fin b.dim)=Fintype.card ((q i).rootSet S) by rw [size,Fintype.card_fin])
  let roots (i:Fin N) (j:Fin b.dim):S:=(idx i j).val
  have distinct (i) : Function.Injective (roots i) := Subtype.val_injective.comp (idx i).injective
  let emb (i:Fin N) := incl.comp (τ i).toRingHom
  have isRoot (i j) : (minpoly F b.gen).eval₂ (emb i) (roots i j)=0 := by
    have h := (Polynomial.mem_rootSet.mp (idx i j).property).2
    change (q i).eval₂ incl (roots i j)=0 at h
    rw [show q i=(minpoly F b.gen).map (τ i).toRingHom from rfl,eval₂_map] at h
    exact h
  let C:Matrix (Fin N×Fin b.dim) J F':=fun r j=>τ r.1 (b.basis.repr (v j) r.2)
  let before:Matrix J J F:=fun i j=>translateField F (algebraMap k K (sh (pick i).1)) (b.basis.repr (v j) (pick i).2)
  have mapped : (C.submatrix pick _root_.id).det≠0 := by
    change (exchange.toRingHom.mapMatrix before).det≠0
    rw [←RingHom.map_det];exact (map_ne_zero_iff _ exchange.injective).mpr full
  obtain ⟨r,det⟩:=sheet_minor C ⟨pick,mapped⟩ roots distinct
  let row (u:J):=atRoot b (emb (r u).1) (roots (r u).1 (r u).2) (isRoot (r u).1 (r u).2)
  refine ⟨p,sep,fun u=>sh (r u).1,row,fun j a=>atRoot_base ..,?_⟩
  let A:Matrix J J S:=fun i j=>∑ h:Fin b.dim, incl (C ((r i).1,h) j)*(roots (r i).1 (r i).2)^h.val
  have eqMat : (Matrix.of (fun i j:J=>row i (v j)))=A := by
    apply Matrix.ext
    intro i j
    exact atRoot_value b (emb (r i).1) (roots (r i).1 (r i).2) (isRoot (r i).1 (r i).2) (v j)
  rw [eqMat];exact det

theorem horizontal_frame (b:PowerBasis F E) (simple:(minpoly F b.gen).Separable) (v:J→E) (li:LinearIndependent K v) :
    ∃ p:(Polynomial F),p.Separable ∧ ∃ offsets:J→k, ∃ ev:J→(E→+*p.SplittingField),
      (∀j a,ev j (algebraMap F E a)=algebraMap F p.SplittingField (translateField F (algebraMap k K (offsets j)) a)) ∧
      (Matrix.of (fun i j:J=>ev i (v j))).det≠0 :=
  horizontal_frame_over (RingEquiv.refl F) b simple v li

#print axioms horizontal_frame_over
#print axioms horizontal_frame
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedSheetFrame

-- merged module R6961MarkedResidueRows
section Merged_R6961MarkedResidueRows

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

end
end Merged_R6961MarkedResidueRows

-- merged module R6961MarkedScalarPlace
section Merged_R6961MarkedScalarPlace

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace Lower6961.MarkedEvaluation
open Polynomial IsLocalRing
open scoped Polynomial
variable (K Ω:Type) [Field K] [Field Ω] [Algebra (RatFunc K) Ω]
local notation "j" => algebraMap (Polynomial K) (RatFunc K)
local notation "ι" => algebraMap (RatFunc K) Ω

/-- A place in the one common splitting field, including its residue map on
the entire scalar polynomial ring, with no unramifiedness hypothesis. -/
structure MarkPlace (z:K) where
  V : ValuationSubring Ω
  lift : (Polynomial K)→+*V
  value : ∀p,(lift p:Ω)=ι (j p)
  specialize : ∀p,residue V (lift p)=residue V (lift (C (p.eval z)))

def markPlace (z:K) : MarkPlace K Ω z := by
  apply Classical.choice
  let P:=RingHom.ker (evalRingHom z)
  letI : P.IsPrime:=RingHom.ker_isPrime _
  let A:=Localization.AtPrime P
  let b:=algebraMap (Polynomial K) A
  let f: A→+*Ω:=(algebraMap (RatFunc K) Ω).comp (Lower6960.CollisionTame.branchFractionHom P)
  obtain ⟨V,h,loc⟩:=IsLocalRing.exists_factor_valuationRing f
  let g:A→+*V:=f.codRestrict V.toSubring h
  let l:=g.comp b
  have hπ:residue V (l (Polynomial.X-C z))=0 := by
    apply (residue_eq_zero_iff _).mpr
    change ¬IsUnit (g (b (Polynomial.X-C z)))
    intro u
    have nu:¬IsUnit (b (Polynomial.X-C z)) := by
      intro bunit
      have outside:Polynomial.X-C z ∈ P.primeCompl :=
        (IsLocalization.AtPrime.isUnit_to_map_iff A P _).mp bunit
      apply outside
      change (Polynomial.X-C z).eval z=0
      rw [eval_sub,eval_X,eval_C,sub_self]
    exact nu (IsUnit.of_map g _ u)
  refine ⟨⟨V,l,fun p=>congrArg (algebraMap (RatFunc K) Ω) (Lower6960.CollisionTame.branchFractionHom_apply _ _),fun p=>?_⟩⟩
  have reducing : ((residue V).comp l)=(((residue V).comp l).comp C).comp (evalRingHom z) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,coe_evalRingHom,eval_C]
    · change residue V (l Polynomial.X)=residue V (l (C (Polynomial.X.eval z)))
      rw [eval_X];rwa [map_sub,map_sub,sub_eq_zero] at hπ
  exact DFunLike.congr_fun reducing p

namespace MarkPlace
variable {K Ω} {z:K} (P:MarkPlace K Ω z)
def pi := P.lift (Polynomial.X-C z)
theorem pi_ne : P.pi≠0 := by
  intro h
  have exactValue:=P.value (Polynomial.X-C z)
  rw [show P.lift (Polynomial.X-C z)=0 from h] at exactValue
  exact ((map_ne_zero_iff _ (algebraMap (RatFunc K) Ω).injective).mpr
    ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr (X_sub_C_ne_zero z))) exactValue.symm
theorem pi_residue : residue P.V P.pi=0 := by
  have hz:((Polynomial.X:(Polynomial K))-C z).eval z=0 := by simp
  rw [pi,P.specialize,hz,map_zero,map_zero,map_zero]
theorem lift_unit {p:(Polynomial K)} (nz:p.eval z≠0) : IsUnit (P.lift p) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  rw [P.specialize]
  exact (map_ne_zero_iff _ (((residue P.V).comp P.lift).comp (C:K→+*(Polynomial K))).injective).mpr nz
theorem separable {q:(Polynomial (Polynomial K))} (sep:(q.map (evalRingHom z)).Separable) :
    ((q.map P.lift).map (residue P.V)).Separable := by
  have eq : (residue P.V).comp P.lift=((((residue P.V).comp P.lift).comp C).comp (evalRingHom z)) :=
    RingHom.ext P.specialize
  rw [Polynomial.map_map,eq,←Polynomial.map_map]
  exact sep.map

/-- Integral entries and all their conjugates land in the selected local ring. -/
theorem integral_mem [Algebra (Polynomial K) Ω] [IsScalarTower (Polynomial K) (RatFunc K) Ω]
    {x:Ω} (hx:IsIntegral (Polynomial K) x) : x∈P.V := by
  letI : Algebra (Polynomial K) P.V:=P.lift.toAlgebra
  letI : IsScalarTower (Polynomial K) P.V Ω:=IsScalarTower.of_algebraMap_eq (fun a=>
    (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) Ω a).trans (P.value a).symm)
  obtain ⟨v,hv⟩:=IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A:=P.V))
  exact hv ▸ v.property
end MarkPlace

#print axioms markPlace
#print axioms MarkPlace.integral_mem
end Lower6961.MarkedEvaluation

end
end Merged_R6961MarkedScalarPlace
