import ProximityPrize.SubmissionLower.R6966ProofHelperBankRank
import ArkLib.ToMathlib.MvPolynomial.SupportWeight

set_option Elab.async false

-- merged module R6966ProofRectangularHelperShift
section Merged_R6966ProofRectangularHelperShift

namespace Research6966.RectangularHelperShift
open Polynomial Finset Module
open K1_14 (FX L Jet Shape seedHasse)
open K1_14_1 (SeedPoly PoleData CRTLift centerEval)
open K1_14_1_3 (seedCoeff translation sourceHasse mapCoeffs_coeff cleared sourceX evaluatedHasse evaluatedHasse_eq centerEval_clear)
open KoalaRect (rectComplete rectEvaluated rectShaped)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem seed_axis (i z:Fin 2) (r:ℕ) (P:SeedPoly) : (seedCoeff i r P).degreeOf z≤P.degreeOf z := by
  classical
  let w:Fin 2→ℕ:=Pi.single z 1
  let w':Option (Fin 2)→ℕ:=fun j=>j.elim 0 w
  let g (j:Fin 2):MvPolynomial (Option (Fin 2)) L:=
    MvPolynomial.X (some j)+if j=i then MvPolynomial.X none else 0
  have scalar (Q:SeedPoly) : Q∈MvPolynomial.restrictWeightAtMost w (Q.degreeOf z) := by
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro e he;rw [show e.weight w=e z from Finsupp.weight_single_one_apply _ _]
    exact MvPolynomial.le_degreeOf_of_mem_support z he
  have subst:=MvPolynomial.bind₁_mem_restrictWeightAtMost (w:=w) (v:=w') (f:=g) (by
    intro j
    apply Submodule.add_mem
    · exact MvPolynomial.X_mem_restrictWeightAtMost w' _ le_rfl
    · by_cases yes:j=i
      · rw [ite_eq_left yes];exact MvPolynomial.X_mem_restrictWeightAtMost w' _ (Nat.zero_le _)
      · rw [ite_eq_right yes];exact Submodule.zero_mem _) (scalar P)
  have eq:translation (R:=L) i=(MvPolynomial.optionEquivLeft L (Fin 2)).toAlgHom.comp (MvPolynomial.bind₁ g) := by
    apply MvPolynomial.algHom_ext
    intro j;by_cases yes:j=i <;> simp [translation,g,yes]
  change ((translation i P).coeff r).degreeOf z≤_
  rw [eq]
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro e he
  have h:=MvPolynomial.mem_restrictWeightAtMost.mp subst (e.optionElim r)
    ((MvPolynomial.mem_support_coeff_optionEquivLeft L).mp he)
  change (e.optionElim r).weight (fun j=>j.elim 0 w)≤_ at h
  simpa [Finsupp.weight_optionElim,w,Finsupp.weight_single_one_apply] using h

theorem cleared_rect {h:ℕ} (D:PoleData h) (i:Fin 2) (r:ℕ) {Q:K1_14_1.Source}
    {U:Fin 2→ℕ} (fits:rectShaped U Q) : rectShaped U (cleared D i r Q) := by
  classical
  intro j k a e nz z
  by_contra above
  apply nz
  change K1_14_1.coeffAt (cleared D i r Q) j k a e=0
  simp only [cleared,K1_14_1.coeffAt,K1_14_1.jetConstant,RingHom.comp_apply]
  rw [coeff_C_mul,coeff_C_mul,coeff_mul,MvPolynomial.coeff_sum]
  simp only [sourceX,coeff_map,MvPolynomial.coeff_C_mul,sourceHasse,mapCoeffs_coeff]
  apply sum_eq_zero
  rintro ⟨b,c⟩ _
  let A:=((Q.coeff j).coeff k).coeff c
  change _*(seedCoeff i r A).coeff e=0
  by_contra live
  have cap:A.degreeOf z≤U z:=MvPolynomial.degreeOf_le_iff.mpr
    (fun d hd=>fits j k c d (MvPolynomial.mem_support_iff.mp hd) z)
  have on:=MvPolynomial.le_degreeOf_of_mem_support z (MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul live))
  exact above (on.trans ((seed_axis i z r A).trans cap))

theorem shifted {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) {s:Shape} {W:ℕ} {U:Fin 2→ℕ} {P:Jet}
    (mem:P∈rectEvaluated Crt word s W U) (i:Fin 2) (r:ℕ) :
    seedHasse i r P∈rectEvaluated Crt word s (W+2*h*r) U := by
  let target:=rectEvaluated Crt word s (W+2*h*r) U
  have sub:rectEvaluated Crt word s W U ≤ target.comap (evaluatedHasse i r) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Q,q,rfl⟩
    have m:cleared D i r Q∈rectComplete Crt word s (W+2*h*r) U :=
      ⟨⟨⟨K1_14_1_3.ambient_cleared D q.1.1.1 i r,K1_14_1_3_1.proof h D word s Q q.1.1.2 i r⟩,
        K1_14_1_3_2.proof h D Crt s Q q.1.2 i r⟩,cleared_rect D i r q.2⟩
    have he:centerEval (cleared D i r Q)∈target:=Submodule.subset_span ⟨_,m,rfl⟩
    rw [centerEval_clear] at he
    have nc:algebraMap L[X] FX ((D.block i)^(2*r))≠0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective L[X] FX)).mpr (pow_ne_zero _ (D.monic i).ne_zero)
    exact (target.smul_mem_iff nc).mp he
  rw [←evaluatedHasse_eq]
  exact sub mem

theorem mono {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ)
    {W V:ℕ} (le:W≤V) :rectEvaluated Crt word s W U ≤rectEvaluated Crt word s V U :=
  Submodule.span_mono (Set.image_mono (show rectComplete Crt word s W U≤rectComplete Crt word s V U from
    inf_le_inf_right _ (K1_14_1.complete_mono Crt word rfl rfl rfl le_rfl le)))

theorem all_axes {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (W:ℕ) :
    rectEvaluated Crt word s W (fun _=>s.U)=K1_14_1.evaluated Crt word s W := by
  apply le_antisymm (KoalaRect.rectEvaluated_le ..)
  apply Submodule.span_le.mpr
  rintro _ ⟨P,hP,rfl⟩
  apply Submodule.subset_span
  refine ⟨P,⟨hP,?_⟩,rfl⟩
  intro j i a e nz z
  have eligible:K1_14_1.trueEligible h s W j i a e:=by by_contra no;exact nz (hP.1.1 j i a e no)
  have sz:=eligible.2.2.1
  rw [K1_14_1_5.seedWeight_eq] at sz
  change e z≤s.U
  fin_cases z
  · exact (Nat.le_add_right (e 0) (e 1)).trans sz
  · exact (Nat.le_add_left (e 1) (e 0)).trans sz

/-- Absence of an avoiding row at one rectangular cutoff forces the
same seed-dependent prime to the full layer power at every earlier cutoff. -/
theorem common_power {h W top:ℕ} (hp:0<h) (lt:W<top) {D:PoleData h} (Crt:CRTLift D)
    (word:K1.I→L) (s:Shape) (U:Fin 2→ℕ) {G:Jet} (irr:Irreducible G) (slope:0<G.natDegree)
    (uses:K1_14_2.UsesSeed G) (small:s.U<K1.p)
    (common:∀ Q∈rectEvaluated Crt word s (top-1) U,G∣Q) :
    ∀ P∈rectComplete Crt word s W U,G^(1+(top-1-W)/(2*h))∣centerEval P := by
  intro P mem
  have row:centerEval P∈rectEvaluated Crt word s W U:=Submodule.subset_span ⟨P,mem,rfl⟩
  by_cases zero:centerEval P=0
  · rw [zero];exact dvd_zero _
  apply Lower6960.PowerLayers.forced_power hp lt irr slope uses zero
    (common _ (mono Crt word s U (by omega) row)) small
  · intro j i
    by_cases z:((centerEval P).coeff j).coeff i=0
    · simp [z]
    · exact (K1_14_1.evaluated_shape Crt word (KoalaRect.rectEvaluated_le Crt word s W U row) j i z).2.2
  · intro i r cap
    exact common _ (mono Crt word s U cap (shifted Crt word row i r))

#print axioms common_power
end
end Research6966.RectangularHelperShift

end Merged_R6966ProofRectangularHelperShift

-- merged module R6966ProofHelperAvoidance
section Merged_R6966ProofHelperAvoidance

namespace Research6966.HelperAvoidance
open Polynomial Finset Module
open K1_14 (Shape FX L Jet shapeSum triangle)
open K1_14_1 (CRTLift PoleData centerEval)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open KoalaRect (area rectEvaluated rectComplete rectDebit)
open HelperBankRank (cells)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def power (N h W:ℕ):=1+(N-1-W)/(2*h)

def rectSlots (U widths:Fin 2→ℕ) (k:ℕ):ℕ :=
  if ∀z,k*widths z≤U z then area (fun z=>U z-k*widths z) else 0

def triSlots (U width k:ℕ):ℕ := if k*width≤U then triangle (U-k*width) else 0

def debitAt (s:Shape) (h N W a b L:ℕ) (slots:ℕ→ℕ):ℕ :=
  let t:=power N h W
  (cells s h W t a b L).card*slots t

private theorem cells_mono (s:Shape) (h W k:ℕ) {a A b B L L':ℕ} (aa:a≤A) (bb:b≤B) (ll:L≤L') :
    cells s h W k A B L' ⊆cells s h W k a b L := by
  intro t ht
  have ax:=Nat.mul_le_mul_left k aa
  have bx:=Nat.mul_le_mul_left k bb
  have lx:=Nat.mul_le_mul_left k ll
  unfold cells at ht ⊢
  split at ht
  · rename_i room
    rw [ite_eq_left (by omega)]
    obtain ⟨pos,weight⟩:=mem_filter.mp ht
    apply mem_filter.mpr
    constructor
    · simp [PadeRank.positions] at pos ⊢;omega
    · exact weight.trans (Nat.sub_le_sub_left lx W)
  · simp at ht

private theorem rect_mono (U:Fin 2→ℕ) {a b:Fin 2→ℕ} (axis:∀ z,a z≤b z) (k:ℕ) :
    rectSlots U b k≤rectSlots U a k := by
  unfold rectSlots
  split
  · rename_i room
    rw [ite_eq_left (fun z=>(Nat.mul_le_mul_left k (axis z)).trans (room z))]
    exact Nat.mul_le_mul (Nat.succ_le_succ (Nat.sub_le_sub_left (Nat.mul_le_mul_left k (axis 0)) _))
      (Nat.succ_le_succ (Nat.sub_le_sub_left (Nat.mul_le_mul_left k (axis 1)) _))
  · exact Nat.zero_le _

private theorem tri_mono (U:ℕ) {a b:ℕ} (le:a≤b) (k:ℕ) : triSlots U b k≤triSlots U a k := by
  have less:=Nat.mul_le_mul_left k le
  unfold triSlots
  split
  · rename_i room
    rw [ite_eq_left (less.trans room)]
    unfold triangle
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul (by omega) (by omega)
  · exact Nat.zero_le _

private theorem width {h N:ℕ} {s:Shape} (nz:0<N) (wide:s.B*(131071-h)≤N) :
    K1_14_1.rawWidthCond h s (N-1) := by
  intro q hq j _
  rw [Nat.sub_add_cancel nz]
  exact (Nat.mul_le_mul_right _ hq).trans (wide.trans (Nat.le_add_right N j))

theorem rect_contradiction {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U widths:Fin 2→ℕ) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (fn:F≠0) {a b L0 nodes moment:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (axes:∀ z,widths z≤PadeNativeQuotient.axis F z) (box:U 0+U 1≤s.U) (small:s.B<K1.p)
    (nz:0<N) (wide:s.B*(131071-h)≤N) (num:P1_7_1.nodeRows s≤nodes)
    (pole:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (positive:rectDebit h nodes moment U + ∑ W∈range N,debitAt s h N W a b L0 (rectSlots U widths) <
      area U*shapeSum s (fun q j=>N+j-q*(131071-h)))
    (force:∀ W<N,∀ P∈rectComplete Crt word s W U,F^(power N h W)∣centerEval P) : False := by
  have floor:=KoalaRect.rectRankFloor hp hl (hl.trans_lt (by decide)) Crt word s (N-1) U box small
    (width nz wide) num pole
  rw [Nat.sub_add_cancel nz] at floor
  have cost (W:ℕ) (hw:W∈range N) : finrank FX (rectEvaluated Crt word s W U)≤debitAt s h N W a b L0 (rectSlots U widths) := by
    have rank:=(HelperBankRank.bank_rank hp hl Crt word s U M fn (force W (mem_range.mp hw))).1
    exact rank.trans (Nat.mul_le_mul (card_le_card (cells_mono s h W _ aCap bCap lCap)) (rect_mono U axes _))
  exact (Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left (sum_le_sum cost) _))) positive

/-- A positive physical rectangle supplies an avoiding row in that exact
rectangle, with no assumptions on its seed derivatives. -/
theorem rect_avoiding {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (U widths:Fin 2→ℕ) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (prime:Irreducible F) (slope:0<F.natDegree)
    (seeded:K1_14_2.UsesSeed F) (char:s.U<K1.p) {a b L0 nodes moment:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (axes:∀ z,widths z≤PadeNativeQuotient.axis F z) (box:U 0+U 1≤s.U) (small:s.B<K1.p)
    (nz:0<N) (wide:s.B*(131071-h)≤N) (num:P1_7_1.nodeRows s≤nodes)
    (pole:P1_7_1.groupedPoleMoment s.B s.J≤moment)
    (positive:rectDebit h nodes moment U + ∑ W∈range N,debitAt s h N W a b L0 (rectSlots U widths) <
      area U*shapeSum s (fun q j=>N+j-q*(131071-h))) :
    ∃ Q∈rectEvaluated Crt word s (N-1) U,¬F∣Q := by
  classical
  by_contra! common
  exact rect_contradiction hp hl Crt word s U widths M prime.ne_zero aCap bCap lCap axes box small
    nz wide num pole positive (fun W hw=>RectangularHelperShift.common_power hp hw Crt word s U prime slope seeded char common)

theorem triangle_contradiction {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (bank:P1_7.Bank) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (fn:F≠0) {a b L0 u:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (uCap:u≤seedDegree F) (small:bank.shape.B<K1.p)
    (nz:0<N) (wide:bank.shape.B*(131071-h)≤N) (num:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank + ∑ W∈range N,debitAt bank.shape h N W a b L0 (triSlots bank.shape.U u) <
      triangle bank.shape.U*shapeSum bank.shape (fun q j=>N+j-q*(131071-h)))
    (force:∀ W<N,∀ P∈rectComplete Crt word bank.shape W (fun _=>bank.shape.U),F^(power N h W)∣centerEval P) : False := by
  have floor:=Lower6960.HelperSource.crt_rank_floor Crt word bank hp hl num pole small (N-1) (width nz wide)
  unfold K1_14_1.rawVolumeAt at floor
  rw [Nat.sub_add_cancel nz] at floor
  have cost (W:ℕ) (hw:W∈range N) : finrank FX (K1_14_1.evaluated Crt word bank.shape W) ≤
      debitAt bank.shape h N W a b L0 (triSlots bank.shape.U u) := by
    rw [←RectangularHelperShift.all_axes]
    have rank:=(HelperBankRank.bank_rank hp hl Crt word bank.shape (fun _=>bank.shape.U) M fn (force W (mem_range.mp hw))).2
    exact rank.trans (Nat.mul_le_mul (card_le_card (cells_mono bank.shape h W _ aCap bCap lCap)) (tri_mono _ uCap _))
  exact Nat.not_lt_of_ge (floor.trans (Nat.add_le_add_left (sum_le_sum cost) _)) positive

theorem triangle_avoiding {h N:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) (bank:P1_7.Bank) {F:Jet}
    (M:HelperPhysicalModel.Model Crt F) (prime:Irreducible F) (slope:0<F.natDegree)
    (seeded:K1_14_2.UsesSeed F) (char:bank.shape.U<K1.p) {a b L0 u:ℕ}
    (aCap:a≤jetDegree F) (bCap:b≤F.natDegree) (lCap:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw)
    (uCap:u≤seedDegree F) (small:bank.shape.B<K1.p)
    (nz:0<N) (wide:bank.shape.B*(131071-h)≤N) (num:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (positive:P1_7.debit h bank + ∑ W∈range N,debitAt bank.shape h N W a b L0 (triSlots bank.shape.U u) <
      triangle bank.shape.U*shapeSum bank.shape (fun q j=>N+j-q*(131071-h))) :
    ∃ Q∈K1_14_1.evaluated Crt word bank.shape (N-1),¬F∣Q := by
  classical
  by_contra! common
  rw [←RectangularHelperShift.all_axes] at common
  exact triangle_contradiction hp hl Crt word bank M prime.ne_zero aCap bCap lCap uCap small nz wide num pole
    positive (fun W hw=>RectangularHelperShift.common_power hp hw Crt word bank.shape _
      prime slope seeded char common)

#print axioms rect_avoiding
#print axioms triangle_avoiding
end
end Research6966.HelperAvoidance

end Merged_R6966ProofHelperAvoidance
