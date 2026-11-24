import ProximityPrize.SubmissionLower.R6960TerminalSmall
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6960ThirdPole
import ProximityPrize.SubmissionLower.R6960QuadraticProjection
import Mathlib.RingTheory.Localization.Integer

-- merged module R6960TerminalMarked
section Merged_R6960TerminalMarked
noncomputable section
set_option Elab.async false
namespace Lower6960.TerminalMarked
open Polynomial Finset
open K1 (K)
open K1_14 (Equation FX Seeds seedEmbedding graphEval atMark atX)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree axisDegree_le_iff)
open RescueGeometry (Model Family)
open scoped Polynomial Classical
private def determinant (f : Equation) : Seeds :=
  f.resultant f.derivative f.natDegree (f.natDegree-1)
private theorem det_axis (f : Equation) (i : Fin 2) :
    (determinant f).degreeOf i≤(2*f.natDegree-1)*axisDegree f i := by
  have coeffs := (axisDegree_le_iff f i _).mp le_rfl
  have der (j : ℕ) : (f.derivative.coeff j).degreeOf i≤axisDegree f i := by
    rw [coeff_derivative]
    have eq : ((j:Seeds)+1)=MvPolynomial.C ((j:FX)+1) := by simp
    rw [eq]
    apply (MvPolynomial.degreeOf_mul_le ..).trans
    rw [MvPolynomial.degreeOf_C,Nat.add_zero]
    exact coeffs (j+1)
  exact (ThirdPole.resultant_axis f f.derivative _ _ _ _ i coeffs der).trans
    (by rw [←Nat.add_mul]; apply Nat.mul_le_mul_right; omega)
theorem bad_labels (f : Equation) (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (degree : f.natDegree<48) (axes : axisDegree f 0+axisDegree f 1≤2400)
    (T : Finset K) (label : K→K) (inj : Set.InjOn label (T:Set K)) :
    (T.filter (fun γ=>graphEval (label γ) (determinant f)=0)).card≤
      (2*f.natDegree-1)*(axisDegree f 0+K1.p*axisDegree f 1) := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let coord (γ : K) := seedEmbedding (label γ)
  have eq : (B.image coord).card=B.card :=
    card_image_of_injOn (fun x hx y hy h=>inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 (seedEmbedding.injective h))
  have small : (2*f.natDegree-1)*axisDegree f 0<K1.p :=
    (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤93) (by omega : axisDegree f 0≤2400)).trans_lt (by decide)
  have nz : determinant f≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have cap := K1_10.frobenius_coefficient_exception_count K1.p _ _ (by decide) _ nz
    (det_axis f 0) small (det_axis f 1) (B.image coord) (by
      intro z hz
      obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hz
      exact (mem_filter.mp hγ).2)
  rw [eq] at cap
  exact cap.trans_eq (by ring)
def simpleSheet (f : Equation) (label : K) (word : (Polynomial K)) : Prop :=
  let q:=f.map (graphEval label)
  q.natDegree=f.natDegree ∧ q.Separable ∧
  ∃ H Q : (Polynomial FX), q=(Polynomial.X-C (atX word))*Q ∧ H.eval (atX word)=1 ∧ Q∣H ∧
    let e:=AdjoinRoot.mk q H
    e^2=e ∧ e≠0 ∧ e≠1
def excCap : ℕ := 93*2400*K1.p
def paidCap : ℕ := MainGeometry.prefixCap+TerminalSmall.smallCap+excCap
theorem good_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2359≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33579) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤paidCap ∨ ∃ (T : Finset K) (f : Equation),T⊆Γ ∧ Γ.card≤paidCap+T.card ∧
      3≤f.natDegree ∧ f.natDegree<48 ∧ axisDegree f 0+axisDegree f 1≤2400 ∧
      (∀ j : Fin 2,axisDegree f j<(TerminalReceipts.witness f.natDegree).order 1) ∧
      ∀ γ∈T,simpleSheet f (M.label γ) (F.scalar γ) ∧
        ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧ atMark q (M.label γ) (F.scalar γ)=0 := by
  classical
  rcases TerminalSmall.higher_remainder F Crt lo hi regular residues with all | ⟨U,f,sub,price,prim,sep,deg,axes,graded,marks⟩
  · exact Or.inl (all.trans (by unfold paidCap; omega))
  let B:=U.filter (fun γ=>graphEval (M.label γ) (determinant f)=0)
  let T:=U\B
  have cost := bad_labels f sep deg axes U M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq)
  have bc : B.card≤excCap := by
    apply cost.trans
    have scale : axisDegree f 0+K1.p*axisDegree f 1≤K1.p*2400 := by
      change axisDegree f 0+2130706433*axisDegree f 1≤2130706433*2400; omega
    exact (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤93) scale).trans_eq (by unfold excCap; ring)
  have count : T.card+B.card=U.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  rcases T.eq_empty_or_nonempty with empty | ⟨z,hz⟩
  · left; rw [empty,card_empty,zero_add] at count; unfold paidCap; omega
  have size : 3≤f.natDegree := by
    obtain ⟨q,_,dv,de,_⟩ := marks z (mem_sdiff.mp hz).1
    exact de.trans (natDegree_le_of_dvd dv prim.ne_zero)
  refine Or.inr ⟨T,f,sdiff_subset.trans sub,by unfold paidCap; omega,size,deg,axes,graded,?_⟩
  intro γ hγ
  have hu := (mem_sdiff.mp hγ).1
  have safe : graphEval (M.label γ) (determinant f)≠0 :=
    fun zero=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hu,zero⟩)
  refine ⟨?_,marks γ hu⟩
  obtain ⟨q,_,⟨g,eq⟩,_,hit⟩ := marks γ hu
  have root : (f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0 := by
    change eval₂ (graphEval (M.label γ)) (atX (F.scalar γ)) q=0 at hit
    rw [eval_map,eq,eval₂_mul,hit,zero_mul]
  have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero _ _ le_rfl safe
  exact ⟨full,separable_map_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe,
    MarkedRoot.sheet (by omega) _ root
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe _ root)⟩
#print axioms good_remainder
end Lower6960.TerminalMarked

end
end Merged_R6960TerminalMarked

-- merged module R6960RetainedCompressionProjection
section Merged_R6960RetainedCompressionProjection
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
namespace Lower6960.RetainedCompression
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
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionProjection
