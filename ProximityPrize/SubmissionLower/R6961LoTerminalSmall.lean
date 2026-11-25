import ProximityPrize.SubmissionLower.R6961LoTerminalDegrees
import ProximityPrize.SubmissionLower.R6960TerminalSmall

noncomputable section
set_option Elab.async false
namespace Lower6961.Lo.TerminalSmall
open Polynomial Finset
open K1 (K)
open K1_14 (Equation atMark atX graphEval)
open RetainedShortening (Word)
open KoalaRect (axisDegree axisDegree_le_iff axisDegree_mul)
open Lower6961.RescueGeometry (Model Family)
open Lower6960 (small_ordinate_count_at_scale smallMarks)

def fee (f : Equation) : ℕ :=
  18*(axisDegree f 0+K1.p*axisDegree f 1)+(K1.p+1)*(axisDegree f 0+axisDegree f 1)+4*f.natDegree

/-- Padding is proportional to the two seed degrees of the actual factor.
Summing the costs therefore spends the original product's seed degrees once. -/
private theorem one {w s T} (W : Word 179808 133520 w s T)
    (label : K→K) (inj : Set.InjOn label (T:Set K)) (q : Equation)
    (nq : q≠0) (pos : 0<q.natDegree) (dy : q.natDegree≤2)
    (cap : axisDegree q 0+axisDegree q 1≤3491)
    (roots : ∀ γ∈T,atMark q (label γ) (s γ)=0) : T.card≤fee q := by
  let v:=axisDegree q 0
  let u:=axisDegree q 1
  let b:=(v+u)/18
  have vmax : v+b+1≤19*(b+1) := by dsimp [b]; omega
  have umax : u+b+1≤19*(b+1) := by dsimp [b]; omega
  have shape : 3*(v+b+1)*(u+b+1)*(2*133520) < (b+1)*(b+1)*(K1.p/2) := by
    calc _ ≤ 3*(19*(b+1))*(19*(b+1))*(2*133520) := by gcongr
         _ = (b+1)*(b+1)*(3*19*19*(2*133520)) := by ring
         _ < _ := Nat.mul_lt_mul_of_pos_left (by decide) (by positivity)
  have sz : v+u≤3491 := cap
  have charge := small_ordinate_count_at_scale (k:=18) (b:=b) W label inj (by decide)
    (Or.inl (by decide)) q nq dy
    (fun i=>⟨(axisDegree_le_iff q 0 _).mp le_rfl i,(axisDegree_le_iff q 1 _).mp le_rfl i⟩)
    (by change v+b<2130706433; dsimp [b]; omega) shape (by decide) roots
  have hb : 18*b≤v+u := by dsimp [b]; omega
  have hpay := Nat.mul_le_mul_left (K1.p+1) hb
  change T.card≤18*(v+b+K1.p*(u+b))+4 at charge
  change T.card≤18*(v+K1.p*u)+(K1.p+1)*(v+u)+4*q.natDegree
  calc _ ≤ _ := charge
       _ = 18*(v+K1.p*u)+(K1.p+1)*(18*b)+4 := by ring
       _ ≤ _ := by omega

theorem covered {w s T} (W : Word 179808 133520 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) (f : Equation) :
    f≠0 → axisDegree f 0+axisDegree f 1≤3491 →
    (∀ γ∈T,∃ q : Equation,Irreducible q ∧ q∣f ∧ 0<q.natDegree ∧ q.natDegree≤2 ∧
      atMark q (label γ) (s γ)=0) → T.card≤fee f := by
  classical
  induction f using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit f hu =>
    intro _ _ cover
    have empty : T=∅ := eq_empty_iff_forall_notMem.mpr (fun γ h=>by
      obtain ⟨q,ir,dv,_⟩ := cover γ h
      exact ir.not_isUnit (isUnit_of_dvd_unit dv hu))
    simp [empty]
  | mul g q ng ir ih =>
    intro nz cap cover
    let U:=smallMarks T label s g
    let V:=T\U
    have us : U⊆T := filter_subset _ _
    have vs : V⊆T := sdiff_subset
    have word (R) (sub : R⊆T) : Word 179808 133520 w s R :=
      ⟨W.distinct.mono sub, fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
    have a0 := axisDegree_mul ir.ne_zero ng 0
    have a1 := axisDegree_mul ir.ne_zero ng 1
    have ca := ih (word U us) (inj.mono us) ng (by omega) (fun γ h=>(mem_filter.mp h).2)
    have rest (γ) (h : γ∈V) : 0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0 := by
      obtain ⟨l,il,dv,pos,dg,zr⟩ := cover γ (vs h)
      have dl : l∣q := (il.prime.dvd_mul.mp dv).resolve_right
        (fun d=>(mem_sdiff.mp h).2 (mem_filter.mpr ⟨vs h,l,il,d,pos,dg,zr⟩))
      have asso:=il.associated_of_dvd ir dl
      refine ⟨pos.trans_le (natDegree_le_of_dvd dl ir.ne_zero),
        (natDegree_le_of_dvd asso.symm.dvd il.ne_zero).trans dg,?_⟩
      obtain ⟨a,eq⟩ := dl
      change eval₂ (graphEval (label γ)) (atX (s γ)) l=0 at zr
      rw [eq,atMark,eval₂_mul,zr,zero_mul]
    have cb : V.card≤fee q := by
      rcases V.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
      · simp [empty]
      exact one (word V vs) label (inj.mono vs) q ir.ne_zero (rest γ hγ).1 (rest γ hγ).2.1
        (by omega) (fun t ht=>(rest t ht).2.2)
    have card : V.card+U.card=T.card := card_sdiff_add_card_eq_card us
    calc T.card = V.card+U.card := card.symm
         _ ≤ fee q+fee g := Nat.add_le_add cb ca
         _ = _ := by unfold fee; rw [a0,a1,natDegree_mul ir.ne_zero ng]; ring

def smallCap : ℕ := (19*K1.p+1)*3491+4*57

theorem small_marks {w s T} (W : Word 179808 133520 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) {f : Equation} (ne : f≠0) (deg : f.natDegree<58)
    (axes : axisDegree f 0+axisDegree f 1≤3491) :
    (smallMarks T label s f).card≤smallCap := by
  classical
  let U:=smallMarks T label s f
  have sub : U⊆T := filter_subset _ _
  have word : Word 179808 133520 w s U :=
    ⟨W.distinct.mono sub,fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
  have paid:=covered word label (inj.mono sub) f ne axes (fun γ h=>(mem_filter.mp h).2)
  refine paid.trans ?_
  unfold fee smallCap
  change 18*(_+2130706433*_)+2130706434*(_+_)+4*_ ≤ (19*2130706433+1)*3491+4*57
  omega

#print axioms small_marks

private theorem root_factor {f : Equation} (nf : f≠0) (z : K) (S : (Polynomial K))
    (root : atMark f z S=0) : ∃ q : Equation,Irreducible q ∧ q∣f ∧ atMark q z S=0 := by
  let ev := eval₂RingHom (graphEval z) (atX S)
  change ev f=0 at root
  induction f using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (nf rfl).elim
  | unit u hu => exact ((hu.map ev).ne_zero root).elim
  | mul g q ng ir ih =>
    rw [map_mul,mul_eq_zero] at root
    rcases root with r | r
    · exact ⟨q,ir,dvd_mul_right ..,r⟩
    · obtain ⟨a,ia,dv,hit⟩ := ih ng r
      exact ⟨a,ia,dv.trans (dvd_mul_left ..),hit⟩

open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open TerminalReceipts (witness)

/-- Isolate the precise marked family still needing the large-degree
surface theorem, retaining the common product and both actual degree caps. -/
theorem higher_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2346≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2449) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤MainGeometry.prefixCap ∨
      ∃ (T : Finset K) (f : Equation), T⊆Γ ∧ Γ.card≤MainGeometry.prefixCap+smallCap+T.card ∧
        f.IsPrimitive ∧ (f.map (algebraMap K1_14.Seeds K1_14_2.SeedField)).Separable ∧
        f.natDegree<58 ∧ axisDegree f 0+axisDegree f 1≤3491 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈T, ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ)=0 := by
  classical
  rcases TerminalDegrees.retained_equation F Crt lo hi regular residues with closed |
    ⟨paid,f,cost,primitive,sep,pos,deg,axes,graded,roots⟩
  · exact Or.inl closed
  let U:=Γ\paid
  let L:=smallMarks U M.label F.scalar f
  let T:=U\L
  have us : U⊆Γ := sdiff_subset
  have ls : L⊆U := filter_subset _ _
  have ts : T⊆U := sdiff_subset
  have W : Word 179808 133520 M.word F.scalar U := by
    refine ⟨F.distinct.mono us,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (us hγ)).scalar_degree with zero | degree
      · simp [zero]
      · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at degree
        omega
    · intro γ hγ
      let B:=F.mark γ (us hγ)
      exact ⟨B.bad.support,B.bad.agreement,B.scalar_hits⟩
  have lc := small_marks W M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq) primitive.ne_zero deg axes
  have card : T.card+L.card=U.card := card_sdiff_add_card_eq_card ls
  have base : Γ.card≤U.card+paid.card := by
    calc Γ.card ≤ (U∪paid).card := Finset.card_le_card (by
           intro γ hγ; by_cases hit : γ∈paid
           · exact mem_union_right _ hit
           · exact mem_union_left _ (mem_sdiff.mpr ⟨hγ,hit⟩))
         _ ≤ _ := card_union_le ..
  refine Or.inr ⟨T,f,ts.trans us,by change L.card≤_ at lc; omega,primitive,sep,deg,axes,graded,?_⟩
  intro γ hγ
  obtain ⟨q,ir,dv,hit⟩ := root_factor primitive.ne_zero _ _ (roots γ (us (ts hγ)) (mem_sdiff.mp (ts hγ)).2)
  have positive : 0<q.natDegree := by
    by_contra! zero
    have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero zero)
    exact ir.not_isUnit (eq ▸ (primitive _ (eq ▸ dv)).map C)
  refine ⟨q,ir,dv,?_,hit⟩
  by_contra! sm
  exact (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨ts hγ,q,ir,dv,positive,by omega,hit⟩)

#print axioms higher_remainder
end Lower6961.Lo.TerminalSmall
