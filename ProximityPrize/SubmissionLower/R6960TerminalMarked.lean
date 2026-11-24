import ProximityPrize.SubmissionLower.R6960TerminalSmall
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6960ThirdPole

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

/-- The native separant survives the Frobenius substitution throughout the
terminal degree box. Bad labels are counted jointly for the entire product. -/
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

/-- Every remaining mark in the actual high band has a genuine rational
sheet. The exceptional set is charged exactly once, even if the common
projected equation has several irreducible factors. -/
theorem good_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2339≤M.overhead.toNat)
    (hi : M.overhead.toNat≤33561) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
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
