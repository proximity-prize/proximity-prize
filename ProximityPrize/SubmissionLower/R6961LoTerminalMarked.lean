import ProximityPrize.SubmissionLower.R6961LoMainGeometryUnion
import ProximityPrize.SubmissionLower.R6961LoTerminalReceipts
import ProximityPrize.SubmissionLower.R6960TerminalDegrees
import ProximityPrize.SubmissionLower.R6960TerminalSmall
import ProximityPrize.SubmissionLower.R6960MarkedRoot
import ProximityPrize.SubmissionLower.R6960ThirdPole

set_option Elab.async false

-- merged module R6961LoTerminalDegrees
section Merged_R6961LoTerminalDegrees

noncomputable section
set_option Elab.async false
namespace Lower6961.Lo.TerminalDegrees
open Polynomial Finset
open K1_14 (Equation L atMark jetAt)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open Lower6961.RescueGeometry (Model Family OnSurface word)
open RescueGeometry (SurfacePass terminalShape)
open TerminalReceipts (terminalBank witness bank_checked positive)

private theorem reject {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2368≤h) (hi : h≤2401) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (i : Fin 59)
    (e : max 1 i.val≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179798 h terminalShape (max 1 i.val) U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179798 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  have fn : f≠0 := fun zero => by have := product.positive; simp [zero] at this
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179798 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 (by omega)
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2) fn e product slots)

private theorem box_guard (i : Fin 59) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel
private theorem one_sided : ∀ i : Fin 59, 0 < i.val → (witness i.val).order 0 = 0 := by decide +kernel

/-- The concrete terminal bounds the degree of the *whole* projected product.
The paired witness bounds the sum of the two seed degrees. At each positive
grade use the indicated witness in both orientations for the sharper bound. -/
theorem degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2368≤h) (hi : h≤2401) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q) {f : Equation} (product : ProjectedProduct S f) :
    f.natDegree<58 ∧ axisDegree f 0+axisDegree f 1≤3523 ∧
    ∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1 := by
  have ne := product.positive
  have rule (i : Fin 59) (e : max 1 i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (witness i.val).U (axisDegree f) r≤
        rectSlots (witness i.val).U (witness i.val).order r) :=
    reject Crt w lo hi parents product i e _ _ (box_guard i) (positive lo hi i)
  have rev (i : Fin 59) (e : max 1 i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (swap (witness i.val).U) (axisDegree f) r≤
        rectSlots (swap (witness i.val).U) (swap (witness i.val).order) r) := by
    apply reject Crt w lo hi parents product i e
    · simpa [Nat.add_comm] using box_guard i
    · rw [KoalaRectAxes.debit_swap,KoalaRectAxes.gain_swap]
      exact positive lo hi i
  have grade : f.natDegree<58 := by
    by_contra! bad
    apply rule 58 (by simpa using bad)
    intro r
    change (_+1-r*axisDegree f 0)*(_+1-r*axisDegree f 1) ≤ (_+1-r*0)*(_+1-r*0)
    simp only [Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨grade,?_,?_⟩
  · by_contra! large
    let t:=witness 0
    have guards : t.U 1≤t.U 0 ∧ t.order 0≤t.order 1 ∧ t.order 1≤t.order 0+1 ∧ t.order 0+t.order 1=3524 := by decide
    have deg : t.order 0+t.order 1≤axisDegree f 0+axisDegree f 1 := by omega
    by_cases axis : axisDegree f 0≤axisDegree f 1
    · apply rule 0 (by change 1 ≤ f.natDegree; omega)
      exact fun r=>HighCore82258.oriented_rect_capacity_le guards.1 axis guards.2.1 guards.2.2.1 deg
    · apply rev 0 (by change 1 ≤ f.natDegree; omega)
      exact fun r=>KoalaRectAxes.slots_reversed r guards.1 (by omega) guards.2.1 guards.2.2.1 deg
  · let i : Fin 59 := ⟨f.natDegree,by omega⟩
    let t:=witness f.natDegree
    have reach : max 1 i.val ≤ f.natDegree := max_le ne le_rfl
    have z0 : t.order 0=0 := one_sided i ne
    intro j
    by_contra! bad
    fin_cases j
    · apply rev i reach
      intro r
      apply Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
      change _≤_+1-r*t.order 0
      rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
    · apply rule i reach
      intro r
      apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
      change _≤_+1-r*t.order 0
      rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _

/-- Every unpaid original mark is a root of this same degree-bounded
equation. If the prefix has no surviving surfaces, its own cap suffices. -/
theorem retained_equation {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2368≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2401) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤MainGeometry.prefixCap ∨
      ∃ (paid : Finset K1.K) (f : Equation), paid.card≤MainGeometry.prefixCap ∧
        f.IsPrimitive ∧ (f.map (algebraMap K1_14.Seeds K1_14_2.SeedField)).Separable ∧
        0<f.natDegree ∧ f.natDegree<58 ∧ axisDegree f 0+axisDegree f 1≤3523 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈Γ, γ∉paid → atMark f (M.label γ) (F.scalar γ)=0 := by
  classical
  obtain ⟨paid,S,cap,geom,prod,cover⟩ := MainGeometry.combined_prefix F Crt lo hi regular residues
  by_cases has : S.Nonempty
  · obtain ⟨f,p⟩ := prod has
    obtain ⟨size,total,axis⟩ := degrees Crt (word M) lo hi geom p
    refine Or.inr ⟨paid,f,cap,p.primitive,p.separable,p.positive,size,total,axis,?_⟩
    intro γ hg outside
    obtain ⟨q,hq,on⟩ := (cover γ hg).resolve_left outside
    simpa only [jetAt,eval₂_C,coe_eval₂RingHom,atMark] using on _ (p.vanishes q hq)
  · apply Or.inl
    apply le_trans (Finset.card_le_card (s:=Γ) (t:=paid) ?_) cap
    intro γ hg
    exact (cover γ hg).resolve_right (fun ⟨q,hq,_⟩=>has ⟨q,hq⟩)

#print axioms degrees
#print axioms retained_equation
end Lower6961.Lo.TerminalDegrees

end
end Merged_R6961LoTerminalDegrees

-- merged module R6961LoTerminalSmall
section Merged_R6961LoTerminalSmall

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
private theorem one {w s T} (W : Word 179798 133472 w s T)
    (label : K→K) (inj : Set.InjOn label (T:Set K)) (q : Equation)
    (nq : q≠0) (pos : 0<q.natDegree) (dy : q.natDegree≤2)
    (cap : axisDegree q 0+axisDegree q 1≤3523)
    (roots : ∀ γ∈T,atMark q (label γ) (s γ)=0) : T.card≤fee q := by
  let v:=axisDegree q 0
  let u:=axisDegree q 1
  let b:=(v+u)/18
  have vmax : v+b+1≤19*(b+1) := by dsimp [b]; omega
  have umax : u+b+1≤19*(b+1) := by dsimp [b]; omega
  have shape : 3*(v+b+1)*(u+b+1)*(2*133472) < (b+1)*(b+1)*(K1.p/2) := by
    calc _ ≤ 3*(19*(b+1))*(19*(b+1))*(2*133472) := by gcongr
         _ = (b+1)*(b+1)*(3*19*19*(2*133472)) := by ring
         _ < _ := Nat.mul_lt_mul_of_pos_left (by decide) (by positivity)
  have sz : v+u≤3523 := cap
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

theorem covered {w s T} (W : Word 179798 133472 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) (f : Equation) :
    f≠0 → axisDegree f 0+axisDegree f 1≤3523 →
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
    have word (R) (sub : R⊆T) : Word 179798 133472 w s R :=
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

def smallCap : ℕ := (19*K1.p+1)*3523+4*57

theorem small_marks {w s T} (W : Word 179798 133472 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) {f : Equation} (ne : f≠0) (deg : f.natDegree<58)
    (axes : axisDegree f 0+axisDegree f 1≤3523) :
    (smallMarks T label s f).card≤smallCap := by
  classical
  let U:=smallMarks T label s f
  have sub : U⊆T := filter_subset _ _
  have word : Word 179798 133472 w s U :=
    ⟨W.distinct.mono sub,fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
  have paid:=covered word label (inj.mono sub) f ne axes (fun γ h=>(mem_filter.mp h).2)
  refine paid.trans ?_
  unfold fee smallCap
  change 18*(_+2130706433*_)+2130706434*(_+_)+4*_ ≤ (19*2130706433+1)*3523+4*57
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
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2368≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2401) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤MainGeometry.prefixCap ∨
      ∃ (T : Finset K) (f : Equation), T⊆Γ ∧ Γ.card≤MainGeometry.prefixCap+smallCap+T.card ∧
        f.IsPrimitive ∧ (f.map (algebraMap K1_14.Seeds K1_14_2.SeedField)).Separable ∧
        f.natDegree<58 ∧ axisDegree f 0+axisDegree f 1≤3523 ∧
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
  have W : Word 179798 133472 M.word F.scalar U := by
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

end
end Merged_R6961LoTerminalSmall

-- merged module R6961LoTerminalMarked
section Merged_R6961LoTerminalMarked

noncomputable section
set_option Elab.async false
namespace Lower6961.Lo.TerminalMarked
open Polynomial Finset
open K1 (K)
open K1_14 (Equation FX Seeds seedEmbedding graphEval atMark atX)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree axisDegree_le_iff)
open Lower6961.RescueGeometry (Model Family)
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
  exact (Lower6960.ThirdPole.resultant_axis f f.derivative _ _ _ _ i coeffs der).trans
    (by rw [←Nat.add_mul]; apply Nat.mul_le_mul_right; omega)

/-- The native separant survives the Frobenius substitution throughout the
terminal degree box. Bad labels are counted jointly for the entire product. -/
theorem bad_labels (f : Equation) (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (degree : f.natDegree<58) (axes : axisDegree f 0+axisDegree f 1≤3523)
    (T : Finset K) (label : K→K) (inj : Set.InjOn label (T:Set K)) :
    (T.filter (fun γ=>graphEval (label γ) (determinant f)=0)).card≤
      (2*f.natDegree-1)*(axisDegree f 0+K1.p*axisDegree f 1) := by
  classical
  let B:=T.filter (fun γ=>graphEval (label γ) (determinant f)=0)
  let coord (γ : K) := seedEmbedding (label γ)
  have eq : (B.image coord).card=B.card :=
    card_image_of_injOn (fun x hx y hy h=>inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 (seedEmbedding.injective h))
  have small : (2*f.natDegree-1)*axisDegree f 0<K1.p :=
    (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤113) (by omega : axisDegree f 0≤3523)).trans_lt (by decide)
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

def excCap : ℕ := 113*3523*K1.p
def paidCap : ℕ := MainGeometry.prefixCap+TerminalSmall.smallCap+excCap

/-- Every remaining mark in the actual high band has a genuine rational
sheet. The exceptional set is charged exactly once, even if the common
projected equation has several irreducible factors. -/
theorem good_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2368≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2401) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤paidCap ∨ ∃ (T : Finset K) (f : Equation),T⊆Γ ∧ Γ.card≤paidCap+T.card ∧
      3≤f.natDegree ∧ f.natDegree<58 ∧ axisDegree f 0+axisDegree f 1≤3523 ∧
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
    have scale : axisDegree f 0+K1.p*axisDegree f 1≤K1.p*3523 := by
      change axisDegree f 0+2130706433*axisDegree f 1≤2130706433*3523; omega
    exact (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤113) scale).trans_eq (by unfold excCap; ring)
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
    Lower6960.MarkedRoot.sheet (by omega) _ root
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe _ root)⟩

#print axioms good_remainder
end Lower6961.Lo.TerminalMarked

end
end Merged_R6961LoTerminalMarked
