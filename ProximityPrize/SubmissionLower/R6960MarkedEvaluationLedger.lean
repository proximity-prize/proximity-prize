import ProximityPrize.SubmissionLower.R6961PoleChartTypes
import ProximityPrize.SubmissionLower.R6960RetainedCompressionProjection

-- merged module R6960RetainedCompressionFactors
section Merged_R6960RetainedCompressionFactors
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1700000
namespace Lower6960.RetainedCompression
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
abbrev simpleSheet (f : Equation) (label : K) (word : (Polynomial K)) : Prop :=
  let q := f.map (graphEval label)
  q.natDegree = f.natDegree ∧ q.Separable ∧
  ∃ H Q : (Polynomial FX), q = (Polynomial.X - C (atX word)) * Q ∧ H.eval (atX word) = 1 ∧ Q ∣ H ∧
    let e := AdjoinRoot.mk q H
    e ^ 2 = e ∧ e ≠ 0 ∧ e ≠ 1

theorem marked_projection (hMax axesCap d : ℕ) (haxesSmall : axesCap < p)
    (hdegFit : 131071 + hMax ≤ d)
    {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (f : Equation) (sub : T⊆Γ)
    (degree : 3≤f.natDegree) (axes : axisDegree f 0+axisDegree f 1≤axesCap)
    (hi : M.overhead.toNat≤hMax)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    Word 179808 d M.word F.scalar T ∧
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
#print axioms marked_projection
#print axioms aggregate
#print axioms constant_price
end
end Lower6960.RetainedCompression

end Merged_R6960RetainedCompressionFactors

-- merged module R6960MarkedEvaluationLedger
section Merged_R6960MarkedEvaluationLedger
set_option Elab.async false
namespace Lower6960.MarkedEvaluation
open RetainedCompression
def rate (e:ℕ) := (9*e+2)*(e-1)+2*e-1
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
end Lower6960.MarkedEvaluation

end Merged_R6960MarkedEvaluationLedger
