import ProximityPrize.SubmissionLower.R6962B1Geometry
import ProximityPrize.SubmissionLower.R6960TerminalDegrees
import ProximityPrize.SubmissionLower.R6960TerminalSmall
import ProximityPrize.SubmissionLower.R6960RetainedCompressionProjection
import ProximityPrize.SubmissionLower.R6960MarkedProtocol

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

namespace Lower6962.B1.HighCount
open Polynomial Finset
open K1 (K p)
open K1_14 (L FX Equation Seeds seedEmbedding graphEval atMark atX jetAt liftPoly)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open K1_14_3 (Surface Parent ProjectedProduct)
open KoalaRect (axisDegree axisDegree_le_iff axisDegree_mul rectGain rectDebit rectSlots)
open KoalaRectAxes (swap)
open CurvatureSquares (Ordinate zView)
open RetainedShortening (Word)
open Lower6960 (small_ordinate_count_at_scale smallMarks)
open Lower6960.RescueGeometry (Model Family OnSurface word)
open Lower6960.TerminalMarked (simpleSheet)
open Lower6960.RetainedCompression (MarkedFiber scalar scalar_injective integral_project specialize
  specialize_into incl aggregate factor_price)
open Lower6960.MarkedEvaluation (rate rate_monotone rate_proper factor_price_of_nonlinear nonlinear_price band2_high_count)
open Lower6962.B1.TerminalReceipts (terminalBank witness bank_checked positive)
open Lower6962.B1.RescueGeometry (terminalShape SurfacePass)
open Lower6962.B1.MainGeometry (prefixCap combined_prefix)
open scoped Polynomial Classical

-- Step 1: Band 1 Terminal Degrees (f.natDegree < 64, sum <= 3279)
private theorem reject {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2360≤h) (hi : h≤2382) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q)
    {f : Equation} (product : ProjectedProduct S f) (i : Fin 65)
    (e : max 1 i.val≤f.natDegree) (U d : Fin 2→ℕ)
    (box : U 0+U 1≤terminalShape.U)
    (gain : rectDebit h terminalBank.nodeRows terminalBank.poleMoment U <
      rectGain 179808 h terminalShape (max 1 i.val) U d)
    (slots : ∀ r,rectSlots U (axisDegree f) r≤rectSlots U d r) : False := by
  have width : terminalShape.B*(131071-h)≤terminalShape.m*179808 :=
    (Nat.mul_le_mul_left _ (Nat.sub_le_sub_left lo 131071)).trans (by decide +kernel)
  have fn : f≠0 := fun zero => by have := product.positive; simp [zero] at this
  exact (not_le_of_gt gain) (KoalaRect.rectLoss (h:=h) (by omega) (by omega)
    (lt_of_le_of_lt hi (by decide)) Crt w 179808 terminalShape U d (by decide) (by decide)
    box bank_checked.moment.2 width bank_checked.nodes.le bank_checked.moment.1 (by omega)
    (fun q hq=>(parents q hq).1) (fun q hq=>(parents q hq).2) fn e product slots)

private theorem box_guard (i : Fin 65) : (witness i.val).U 0+(witness i.val).U 1≤terminalShape.U := by
  fin_cases i <;> decide +kernel

private theorem one_sided : ∀ i : Fin 65, 0 < i.val → (witness i.val).order 0 = 0 := by decide +kernel

theorem b1_degrees {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (w : K1.I→L)
    (lo : 2360≤h) (hi : h≤2382) {S : Finset Surface}
    (parents : ∀ q∈S,Parent q ∧ SurfacePass Crt w q) {f : Equation} (product : ProjectedProduct S f) :
    f.natDegree<64 ∧ axisDegree f 0+axisDegree f 1≤3279 ∧
    ∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1 := by
  have ne := product.positive
  have rule (i : Fin 65) (e : max 1 i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (witness i.val).U (axisDegree f) r≤rectSlots (witness i.val).U (witness i.val).order r) :=
    reject Crt w lo hi parents product i e _ _ (box_guard i) (positive lo hi i)
  have rev (i : Fin 65) (e : max 1 i.val≤f.natDegree) :
      ¬(∀ r,rectSlots (swap (witness i.val).U) (axisDegree f) r≤rectSlots (swap (witness i.val).U) (swap (witness i.val).order) r) := by
    apply reject Crt w lo hi parents product i e
    · simpa [Nat.add_comm] using box_guard i
    · rw [KoalaRectAxes.debit_swap,KoalaRectAxes.gain_swap]; exact positive lo hi i
  have grade : f.natDegree<64 := by
    by_contra! bad
    apply rule 64 (by simpa using bad)
    intro r
    change (_+1-r*axisDegree f 0)*(_+1-r*axisDegree f 1) ≤ (_+1-r*0)*(_+1-r*0)
    simp only [Nat.mul_zero,Nat.sub_zero]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  refine ⟨grade,?_,?_⟩
  · by_contra! large
    let t := witness 0
    have guards : t.U 1≤t.U 0 ∧ t.order 0≤t.order 1 ∧ t.order 1≤t.order 0+1 ∧ t.order 0+t.order 1=3280 := by decide
    have deg : t.order 0+t.order 1≤axisDegree f 0+axisDegree f 1 := by omega
    by_cases axis : axisDegree f 0≤axisDegree f 1
    · apply rule 0 (by change 1 ≤ f.natDegree; omega)
      exact fun r=>HighCore82258.oriented_rect_capacity_le guards.1 axis guards.2.1 guards.2.2.1 deg
    · apply rev 0 (by change 1 ≤ f.natDegree; omega)
      exact fun r=>KoalaRectAxes.slots_reversed r guards.1 (by omega) guards.2.1 guards.2.2.1 deg
  · let i : Fin 65 := ⟨f.natDegree,by omega⟩
    let t := witness f.natDegree
    have reach : max 1 i.val ≤ f.natDegree := max_le ne le_rfl
    have z0 : t.order 0=0 := one_sided i ne
    intro j; by_contra! bad; fin_cases j
    · apply rev i reach; intro r
      apply Nat.mul_le_mul (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
      change _≤_+1-r*t.order 0; rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _
    · apply rule i reach; intro r
      apply Nat.mul_le_mul _ (Nat.sub_le_sub_left (Nat.mul_le_mul_left r bad) _)
      change _≤_+1-r*t.order 0; rw [z0,Nat.mul_zero,Nat.sub_zero]; exact Nat.sub_le _ _

theorem b1_retained_equation {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2360≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2382) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤prefixCap ∨
      ∃ (paid : Finset K) (f : Equation), paid.card≤prefixCap ∧
        f.IsPrimitive ∧ (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable ∧
        0<f.natDegree ∧ f.natDegree<64 ∧ axisDegree f 0+axisDegree f 1≤3279 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈Γ, γ∉paid → atMark f (M.label γ) (F.scalar γ)=0 := by
  obtain ⟨paid,S,cap,geom,prod,cover⟩ := combined_prefix F Crt lo hi regular residues
  by_cases has : S.Nonempty
  · obtain ⟨f,p'⟩ := prod has
    obtain ⟨size,total,axis⟩ := b1_degrees Crt (word M) lo hi geom p'
    refine Or.inr ⟨paid,f,cap,p'.primitive,p'.separable,p'.positive,size,total,axis,?_⟩
    intro γ hg outside
    obtain ⟨q,hq,on⟩ := (cover γ hg).resolve_left outside
    simpa only [jetAt,eval₂_C,coe_eval₂RingHom,atMark] using on _ (p'.vanishes q hq)
  · apply Or.inl
    exact (Finset.card_le_card fun γ hg => (cover γ hg).resolve_right (fun ⟨q,hq,_⟩=>has ⟨q,hq⟩)).trans cap

-- Step 2: Band 1 Small Marks (deg <= 2 at d = 133453, sum <= 3279)
def b1SmallFee (f : Equation) : ℕ :=
  18*(axisDegree f 0+p*axisDegree f 1)+(p+1)*(axisDegree f 0+axisDegree f 1)+4*f.natDegree

private theorem b1_small_one {w s T} (W : Word 179808 133453 w s T)
    (label : K→K) (inj : Set.InjOn label (T:Set K)) (q : Equation)
    (nq : q≠0) (pos : 0<q.natDegree) (dy : q.natDegree≤2)
    (cap : axisDegree q 0+axisDegree q 1≤3279)
    (roots : ∀ γ∈T,atMark q (label γ) (s γ)=0) : T.card≤b1SmallFee q := by
  let v := axisDegree q 0; let u := axisDegree q 1; let b := (v+u)/18
  have vmax : v+b+1≤19*(b+1) := by dsimp [b]; omega
  have umax : u+b+1≤19*(b+1) := by dsimp [b]; omega
  have shape : 3*(v+b+1)*(u+b+1)*(2*133453) < (b+1)*(b+1)*(p/2) := by
    calc _ ≤ 3*(19*(b+1))*(19*(b+1))*(2*133453) := by gcongr
         _ = (b+1)*(b+1)*(3*19*19*(2*133453)) := by ring
         _ < _ := Nat.mul_lt_mul_of_pos_left (by decide) (by positivity)
  have charge := small_ordinate_count_at_scale (k:=18) (b:=b) W label inj (by decide)
    (Or.inl (by decide)) q nq dy
    (fun i=>⟨(axisDegree_le_iff q 0 _).mp le_rfl i,(axisDegree_le_iff q 1 _).mp le_rfl i⟩)
    (by change v+b<2130706433; dsimp [b]; omega) shape (by decide) roots
  have hb : 18*b≤v+u := by dsimp [b]; omega
  have hpay := Nat.mul_le_mul_left (p+1) hb
  change T.card≤18*(v+b+p*(u+b))+4 at charge
  change T.card≤18*(v+p*u)+(p+1)*(v+u)+4*q.natDegree
  calc _ ≤ _ := charge
       _ = 18*(v+p*u)+(p+1)*(18*b)+4 := by ring
       _ ≤ _ := by omega

theorem b1_small_covered {w s T} (W : Word 179808 133453 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) (f : Equation) :
    f≠0 → axisDegree f 0+axisDegree f 1≤3279 →
    (∀ γ∈T,∃ q : Equation,Irreducible q ∧ q∣f ∧ 0<q.natDegree ∧ q.natDegree≤2 ∧
      atMark q (label γ) (s γ)=0) → T.card≤b1SmallFee f := by
  induction f using WfDvdMonoid.induction_on_irreducible generalizing T with
  | zero => simp
  | unit f hu =>
    intro _ _ cover
    have empty : T=∅ := eq_empty_iff_forall_notMem.mpr (fun γ h=>by
      obtain ⟨q,ir,dv,_⟩ := cover γ h; exact ir.not_isUnit (isUnit_of_dvd_unit dv hu))
    simp [empty]
  | mul g q ng ir ih =>
    intro nz cap cover
    let U := smallMarks T label s g; let V := T\U
    have us : U⊆T := filter_subset _ _; have vs : V⊆T := sdiff_subset
    have word (R) (sub : R⊆T) : Word 179808 133453 w s R :=
      ⟨W.distinct.mono sub, fun γ h=>W.degree γ (sub h), fun γ h=>W.hits γ (sub h)⟩
    have a0 := axisDegree_mul ir.ne_zero ng 0; have a1 := axisDegree_mul ir.ne_zero ng 1
    have ca := ih (word U us) (inj.mono us) ng (by omega) (fun γ h=>(mem_filter.mp h).2)
    have rest (γ) (h : γ∈V) : 0<q.natDegree ∧ q.natDegree≤2 ∧ atMark q (label γ) (s γ)=0 := by
      obtain ⟨l,il,dv,pos,dg,zr⟩ := cover γ (vs h)
      have dl : l∣q := (il.prime.dvd_mul.mp dv).resolve_right
        (fun d=>(mem_sdiff.mp h).2 (mem_filter.mpr ⟨vs h,l,il,d,pos,dg,zr⟩))
      have asso := il.associated_of_dvd ir dl
      refine ⟨pos.trans_le (natDegree_le_of_dvd dl ir.ne_zero), (natDegree_le_of_dvd asso.symm.dvd il.ne_zero).trans dg, ?_⟩
      obtain ⟨a,eq⟩ := dl; change eval₂ (graphEval (label γ)) (atX (s γ)) l=0 at zr
      rw [eq,atMark,eval₂_mul,zr,zero_mul]
    have cb : V.card≤b1SmallFee q := by
      rcases V.eq_empty_or_nonempty with empty | ⟨γ,hγ⟩
      · simp [empty]
      exact b1_small_one (word V vs) label (inj.mono vs) q ir.ne_zero (rest γ hγ).1 (rest γ hγ).2.1 (by omega) (fun t ht=>(rest t ht).2.2)
    have card : V.card+U.card=T.card := card_sdiff_add_card_eq_card us
    calc T.card = V.card+U.card := card.symm
         _ ≤ b1SmallFee q+b1SmallFee g := Nat.add_le_add cb ca
         _ = _ := by unfold b1SmallFee; rw [a0,a1,natDegree_mul ir.ne_zero ng]; ring

def b1SmallCap : ℕ := 132745141485864

theorem b1_small_marks {w s T} (W : Word 179808 133453 w s T) (label : K→K)
    (inj : Set.InjOn label (T:Set K)) {f : Equation} (ne : f≠0) (deg : f.natDegree<64)
    (axes : axisDegree f 0+axisDegree f 1≤3279) :
    (smallMarks T label s f).card≤b1SmallCap := by
  let U := smallMarks T label s f; have sub : U⊆T := filter_subset _ _
  have word : Word 179808 133453 w s U := ⟨W.distinct.mono sub,fun γ h=>W.degree γ (sub h),fun γ h=>W.hits γ (sub h)⟩
  have paid := b1_small_covered word label (inj.mono sub) f ne axes (fun γ h=>(mem_filter.mp h).2)
  refine paid.trans ?_
  unfold b1SmallFee b1SmallCap
  change 18*(_+2130706433*_)+2130706434*(_+_)+4*_ ≤ 132745141485864
  omega

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
    · obtain ⟨a,ia,dv,hit⟩ := ih ng r; exact ⟨a,ia,dv.trans (dvd_mul_left ..),hit⟩

theorem b1_higher_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2360≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2382) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤prefixCap ∨
      ∃ (T : Finset K) (f : Equation), T⊆Γ ∧ Γ.card≤prefixCap+b1SmallCap+T.card ∧
        f.IsPrimitive ∧ (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable ∧
        f.natDegree<64 ∧ axisDegree f 0+axisDegree f 1≤3279 ∧
        (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
        ∀ γ∈T, ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ)=0 := by
  rcases b1_retained_equation F Crt lo hi regular residues with closed |
    ⟨paid,f,cost,primitive,sep,pos,deg,axes,graded,roots⟩
  · exact Or.inl closed
  let U := Γ\paid; let L' := smallMarks U M.label F.scalar f; let T := U\L'
  have us : U⊆Γ := sdiff_subset; have ls : L'⊆U := filter_subset _ _; have ts : T⊆U := sdiff_subset
  have W : Word 179808 133453 M.word F.scalar U := by
    refine ⟨F.distinct.mono us,?_,?_⟩
    · intro γ hγ
      rcases (F.mark γ (us hγ)).scalar_degree with zero | degree
      · simp [zero]
      · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at degree; omega
    · intro γ hγ; let B := F.mark γ (us hγ); exact ⟨B.bad.support,B.bad.agreement,B.scalar_hits⟩
  have lc := b1_small_marks W M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq) primitive.ne_zero deg axes
  have card : T.card+L'.card=U.card := card_sdiff_add_card_eq_card ls
  have base : Γ.card≤U.card+paid.card := by
    calc Γ.card ≤ (U∪paid).card := Finset.card_le_card (by
           intro γ hγ; by_cases hit : γ∈paid
           · exact mem_union_right _ hit
           · exact mem_union_left _ (mem_sdiff.mpr ⟨hγ,hit⟩))
         _ ≤ _ := card_union_le ..
  refine Or.inr ⟨T,f,ts.trans us,by change L'.card≤_ at lc; omega,primitive,sep,deg,axes,graded,?_⟩
  intro γ hγ
  obtain ⟨q,ir,dv,hit⟩ := root_factor primitive.ne_zero _ _ (roots γ (us (ts hγ)) (mem_sdiff.mp (ts hγ)).2)
  have positive : 0<q.natDegree := by
    by_contra! zero; have eq := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero zero)
    exact ir.not_isUnit (eq ▸ (primitive _ (eq ▸ dv)).map C)
  refine ⟨q,ir,dv,?_,hit⟩
  by_contra! sm
  exact (mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨ts hγ,q,ir,dv,positive,by omega,hit⟩)

-- Step 3: Band 1 Discriminant Exceptions + Good Remainder
private def b1Determinant (f : Equation) : Seeds :=
  f.resultant f.derivative f.natDegree (f.natDegree-1)

private theorem b1_det_axis (f : Equation) (i : Fin 2) :
    (b1Determinant f).degreeOf i≤(2*f.natDegree-1)*axisDegree f i := by
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

theorem b1_bad_labels (f : Equation) (sep : (f.map (algebraMap Seeds K1_14_2.SeedField)).Separable)
    (degree : f.natDegree<64) (axes : axisDegree f 0+axisDegree f 1≤3279)
    (T : Finset K) (label : K→K) (inj : Set.InjOn label (T:Set K)) :
    (T.filter (fun γ=>graphEval (label γ) (b1Determinant f)=0)).card≤
      (2*f.natDegree-1)*(axisDegree f 0+p*axisDegree f 1) := by
  let B := T.filter (fun γ=>graphEval (label γ) (b1Determinant f)=0)
  let coord (γ : K) := seedEmbedding (label γ)
  have eq : (B.image coord).card=B.card :=
    card_image_of_injOn (fun x hx y hy h=>inj (mem_filter.mp hx).1 (mem_filter.mp hy).1 (seedEmbedding.injective h))
  have small : (2*f.natDegree-1)*axisDegree f 0<p :=
    (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤125) (by omega : axisDegree f 0≤3279)).trans_lt (by decide)
  have nz : b1Determinant f≠0 := resultant_derivative_ne_zero_of_separable_map_fractionField f sep
  have cap := K1_10.frobenius_coefficient_exception_count p _ _ (by decide) _ nz
    (b1_det_axis f 0) small (b1_det_axis f 1) (B.image coord) (by
      intro z hz; obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hz; exact (mem_filter.mp hγ).2)
  rw [eq] at cap; exact cap.trans_eq (by ring)

def b1ExcCap : ℕ := 873323299225875
def b1PaidCap : ℕ := prefixCap+b1SmallCap+b1ExcCap
abbrev b1RetainedCap : ℕ := 75925419455894304

theorem b1_good_remainder {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (lo : 2360≤M.overhead.toNat)
    (hi : M.overhead.toNat≤2382) (regular : ∀ j i,(D.block j).eval (nodeL i)≠0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ)) :
    Γ.card≤b1PaidCap ∨ ∃ (T : Finset K) (f : Equation),T⊆Γ ∧ Γ.card≤b1PaidCap+T.card ∧
      3≤f.natDegree ∧ f.natDegree<64 ∧ axisDegree f 0+axisDegree f 1≤3279 ∧
      (∀ j : Fin 2,axisDegree f j<(witness f.natDegree).order 1) ∧
      ∀ γ∈T,simpleSheet f (M.label γ) (F.scalar γ) ∧
        ∃ q : Equation,Irreducible q ∧ q∣f ∧ 3≤q.natDegree ∧ atMark q (M.label γ) (F.scalar γ)=0 := by
  rcases b1_higher_remainder F Crt lo hi regular residues with all | ⟨U,f,sub,price,prim,sep,deg,axes,graded,marks⟩
  · exact Or.inl (all.trans (by unfold b1PaidCap; omega))
  let B := U.filter (fun γ=>graphEval (M.label γ) (b1Determinant f)=0)
  let T := U\B
  have cost := b1_bad_labels f sep deg axes U M.label (fun _ _ _ _ eq=>sub_left_inj.mp eq)
  have bc : B.card≤b1ExcCap := by
    apply cost.trans
    have scale : axisDegree f 0+p*axisDegree f 1≤p*3279 := by
      change axisDegree f 0+2130706433*axisDegree f 1≤2130706433*3279; omega
    exact (Nat.mul_le_mul (by omega : 2*f.natDegree-1≤125) scale).trans_eq (by unfold b1ExcCap; decide)
  have count : T.card+B.card=U.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  rcases T.eq_empty_or_nonempty with empty | ⟨z,hz⟩
  · left; rw [empty,card_empty,zero_add] at count; unfold b1PaidCap; omega
  have size : 3≤f.natDegree := by
    obtain ⟨q,_,dv,de,_⟩ := marks z (mem_sdiff.mp hz).1
    exact de.trans (natDegree_le_of_dvd dv prim.ne_zero)
  refine Or.inr ⟨T,f,sdiff_subset.trans sub,by unfold b1PaidCap; omega,size,deg,axes,graded,?_⟩
  intro γ hγ
  have hu := (mem_sdiff.mp hγ).1
  have safe : graphEval (M.label γ) (b1Determinant f)≠0 := fun zero=>(mem_sdiff.mp hγ).2 (mem_filter.mpr ⟨hu,zero⟩)
  refine ⟨?_,marks γ hu⟩
  obtain ⟨q,_,⟨g,eq⟩,_,hit⟩ := marks γ hu
  have root : (f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0 := by
    change eval₂ (graphEval (M.label γ)) (atX (F.scalar γ)) q=0 at hit
    rw [eval_map,eq,eval₂_mul,hit,zero_mul]
  have full := natDegree_map_eq_of_resultant_derivative_padded_ne_zero _ _ le_rfl safe
  exact ⟨full,separable_map_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe,
    Lower6960.MarkedRoot.sheet (by omega) _ root
      (eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero _ _ le_rfl (by omega) safe _ root)⟩

-- Step 4: Band 1 Marked Projection + Live Budget + Retained Compression
theorem b1_marked_projection {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (f : Equation) (sub : T⊆Γ)
    (degree : 3≤f.natDegree) (axes : axisDegree f 0+axisDegree f 1≤3279)
    (hi : M.overhead.toNat≤2382)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    Word 179808 133453 M.word F.scalar T ∧
    ∃ P : Ordinate, P≠0 ∧ P.natDegree=f.natDegree ∧
      (zView P).natDegree≤axisDegree f 0+p*axisDegree f 1 ∧
      ∀ γ∈T, MarkedFiber P (scalar M γ) (liftPoly (F.scalar γ)) := by
  have nz : f≠0 := by intro h; simp [h] at degree
  have small : axisDegree f 0<p := by change _<2130706433; omega
  obtain ⟨D,P,dn,pn,deg,cap,called⟩ := integral_project f nz small
  refine ⟨⟨F.distinct.mono sub,?_,?_⟩,P,pn,deg,cap,?_⟩
  · intro γ hγ
    rcases (F.mark γ (sub hγ)).scalar_degree with z | bound
    · simp [z]
    · change ((F.scalar γ).natDegree : ℤ)≤131071+M.overhead at bound
      have hh : M.overhead≤(2382 : ℤ) := by omega
      omega
  · intro γ hγ; let mark := F.mark γ (sub hγ); exact ⟨mark.bad.support,mark.bad.agreement,mark.scalar_hits⟩
  · intro γ hγ
    have eq := called (M.label γ)
    have dnon : incl D≠0 := (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) FX)).mpr dn
    have native := marks γ hγ
    change (f.map (graphEval (M.label γ))).natDegree=f.natDegree ∧ (f.map (graphEval (M.label γ))).Separable ∧ _ at native
    obtain ⟨full,sep,H,Q,fac,_⟩ := native
    have root : (f.map (graphEval (M.label γ))).eval (atX (F.scalar γ))=0 := by
      rw [fac,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul]
    have smap : ((specialize P (scalar M γ)).map incl).natDegree = (specialize P (scalar M γ)).natDegree :=
      natDegree_map_eq_of_injective (IsFractionRing.injective (Polynomial L) FX) _
    refine ⟨?_,?_,?_⟩
    · rw [← smap,eq,natDegree_C_mul dnon,full,deg]
    · rw [eq]; exact sep.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr dnon))
    · apply (IsFractionRing.injective (Polynomial L) FX)
      rw [← Polynomial.eval_map_apply,eq,map_zero,eval_mul,eval_C]
      exact mul_eq_zero.mpr (Or.inr root)

theorem b1_live_maximum (e : Fin 64) (lo : 3≤e.val) :
    rate e.val * (3279+p*((witness e.val).order 1-1))+(e.val-1)*e.val ≤ 64487385692461473 := by
  revert lo
  fin_cases e <;> decide +kernel

theorem b1_budget (e a b : ℕ) (lo : 3≤e) (hi : e<64) (axes : a+b≤3279)
    (bound : b<(witness e).order 1) : rate e*(a+p*b)+(e-1)*e≤b1RetainedCap := by
  have fit := b1_live_maximum ⟨e,hi⟩ lo
  have bnd : b≤(witness e).order 1-1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (show a≤3279 by omega) (Nat.mul_le_mul_left _ bnd))) _).trans (fit.trans (by decide))

theorem b1_vote_scale : CurvatureVotes.VoteScale 179808 133453 18 :=
  Or.inl (by decide +kernel)

theorem b1_retained {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (hi : M.overhead.toNat≤2382) (T : Finset K) (f : Equation) (sub : T⊆Γ)
    (emin : 3≤f.natDegree) (emax : f.natDegree<64) (axes : axisDegree f 0+axisDegree f 1≤3279)
    (graded : ∀ j : Fin 2, axisDegree f j<(witness f.natDegree).order 1)
    (marks : ∀ γ∈T, simpleSheet f (M.label γ) (F.scalar γ)) :
    T.card≤b1RetainedCap := by
  obtain ⟨W,P,pn,deg,seed,fibre⟩ := b1_marked_projection F f sub emin axes hi marks
  have pmin : 3≤P.natDegree := deg.symm ▸ emin
  have pmax : P.natDegree<64 := deg.symm ▸ emax
  have count := aggregate P T (scalar M) (fun γ=>liftPoly (F.scalar γ))
    (rate P.natDegree) (P.natDegree-1) pn fibre (by
      intro Q ir dvd U us qmark
      have words : Word 179808 133453 M.word F.scalar U :=
        ⟨W.distinct.mono us,fun γ hγ=>W.degree γ (us hγ),fun γ hγ=>W.hits γ (us hγ)⟩
      exact factor_price rate rate_monotone (by decide) rate_proper
        (factor_price_of_nonlinear nonlinear_price) 133453 (by decide) (by decide) b1_vote_scale
        F (us.trans sub) words ir _ pmin (Or.inr ⟨pmax, le_rfl⟩)
        (natDegree_le_of_dvd dvd pn) qmark)
  rw [deg] at count
  have priced := Nat.add_le_add_right (Nat.mul_le_mul_left (rate f.natDegree) seed) ((f.natDegree-1)*f.natDegree)
  exact count.trans (priced.trans (b1_budget f.natDegree _ _ emin emax axes (graded 1)))

theorem band1_high_count {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2360 ≤ M.overhead) (hi : M.overhead ≤ 2382) :
    Γ.card ≤ 265963255385514628 := by
  have hlo : 2360 ≤ M.overhead.toNat := by omega
  have hhi : M.overhead.toNat ≤ 2382 := by omega
  obtain ⟨D, ⟨Crt⟩, regular, residues⟩ := Lower6960.FrontPoleChart.of_family M F
  rcases b1_good_remainder F Crt hlo hhi regular residues with
    paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
  · exact paid.trans (by decide +kernel)
  · exact (paid.trans (Nat.add_le_add_left
      (b1_retained F hhi T f sub degree small axes grade (fun γ hγ => (marks γ hγ).1)) _)).trans_eq
      (by decide +kernel)

theorem candidate_of_gates (gates : Low6960Allocation.Gates) :
    ProximityPrize.Benchmark.ProtocolClaim 6962 2896975644678137418 9223372036854702689 :=
  Lower6960.protocol_claim_of_bands gates
    (fun M F lo hi => band1_high_count M F lo hi)
    (fun M F lo hi => band2_high_count nonlinear_price M F lo hi)

#print axioms band1_high_count
#print axioms candidate_of_gates
end Lower6962.B1.HighCount
