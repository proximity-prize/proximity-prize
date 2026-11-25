import ProximityPrize.SubmissionLower.R6960RescueGeometryBills
import ProximityPrize.SubmissionLower.R6960RetainedCompressionProjection
import ProximityPrize.SubmissionLower.R6960MarkedSheet

set_option Elab.async false

-- merged module R6960Front6960PoleChart
section Merged_R6960Front6960PoleChart

set_option Elab.async false
set_option maxRecDepth 18000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.FrontPoleChart
noncomputable section
open Polynomial
open P1 (K I node twist p)
open K1_14 (L liftPoly)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open RescueGeometry (Model Family)
open scoped Polynomial

private def AdjacentChart {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) : Prop :=
  let σ := frobenius L p
  let H' := H.map σ
  H.Monic ∧ H.natDegree = M.overhead.toNat ∧ H ∣ liftPoly M.E ∧
  H'.Monic ∧ H'.natDegree = M.overhead.toNat ∧ H' ∣ liftPoly (M.E.map twist) ∧
  IsCoprime H H' ∧
  (∀ i, H.eval (algebraMap K L (node i)) ≠ 0 ∧ H'.eval (algebraMap K L (node i)) ≠ 0) ∧
  IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H ∧
  IsCoprime ((liftPoly (M.Q * M.factor * M.A₀)).map σ) H' ∧
  ∀ γ ∈ Γ,
    let z := algebraMap K L (M.label γ)
    let D := liftPoly (M.factor * M.amplitude γ)
    let S := liftPoly (F.scalar γ)
    IsCoprime D H ∧ IsCoprime (D.map σ) H' ∧
    H ∣ D * S + C z * liftPoly M.Q ∧
    H' ∣ D.map σ * S + C (z ^ p) * (liftPoly M.Q).map σ
private theorem adjacent_chart {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ H, AdjacentChart M F H := by
  let φ := algebraMap K L
  let σ := frobenius L p
  have hsmall : M.overhead.toNat ≤ (liftPoly M.E).natDegree := by
    rw [liftPoly, natDegree_map]
    unfold P1.ModelAt.overhead
    omega
  obtain ⟨H, hm, hdeg, hd⟩ := K1_14.trim _ _ hsmall
  have hd' : H.map σ ∣ liftPoly (M.E.map twist) := by
    change H.map σ ∣ liftPoly (M.E.map K1.twist)
    rw [K1_14.twist_lift]
    exact Polynomial.map_dvd σ hd
  have hcop : IsCoprime H (H.map σ) := by
    have ha := M.adjacent_coprime.map (Polynomial.mapRingHom φ)
    exact (ha.of_isCoprime_of_dvd_left hd).of_isCoprime_of_dvd_right hd'
  have hunit : IsCoprime (liftPoly (M.Q * M.factor * M.A₀)) H :=
    (((M.offset_reduced.mul_left M.coprime_factor.symm).mul_left M.first_amplitude_unit).map
      (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
  refine ⟨H, hm, hdeg, hd, hm.map σ, (natDegree_map σ).trans hdeg, hd', hcop, ?_,
    hunit, hunit.map (Polynomial.mapRingHom σ), ?_⟩
  · intro i
    have h₀ : H.eval (φ (node i)) ≠ 0 := by
      intro hz
      have hb : (liftPoly M.E).eval (φ (node i)) = 0 := by
        obtain ⟨J, hj⟩ := hd
        simp [hj, eval_mul, hz]
      exact M.E_nodes i (φ.injective (by simpa [liftPoly, φ] using hb))
    have hx : σ (φ (node i)) = φ (node i) := by
      change φ (node i) ^ p = _
      rw [← map_pow, FrobeniusLocator.Native.native_domain_fixed]
    refine ⟨h₀, ?_⟩
    rw [← hx, eval_map_apply]
    exact (map_ne_zero σ).mpr h₀
  · intro γ hγ
    let z := M.label γ
    let B := F.mark γ hγ
    have ha : IsCoprime (liftPoly (M.factor * M.amplitude γ)) H :=
      ((M.coprime_factor.symm.mul_left B.pole_unit).map
        (Polynomial.mapRingHom φ)).of_isCoprime_of_dvd_right hd
    have hid : M.E ∣ (M.factor * M.amplitude γ) * F.scalar γ + C z * M.Q :=
      ⟨M.decoder B.bad, by rw [← B.identity]; ring⟩
    have hres : H ∣ liftPoly (M.factor * M.amplitude γ) * liftPoly (F.scalar γ) +
        C (φ z) * liftPoly M.Q := by
      simpa only [liftPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        using hd.trans (Polynomial.map_dvd φ hid)
    have hfix : (liftPoly (F.scalar γ)).map σ = liftPoly (F.scalar γ) := by
      rw [← K1_14.twist_lift]
      exact congrArg liftPoly B.scalar_fixed
    refine ⟨ha, ha.map (Polynomial.mapRingHom σ), hres, ?_⟩
    simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hfix,
      σ, frobenius_def] using (Polynomial.map_dvd σ hres)
private theorem chart_poles {u del} (M : Model u del) {Γ} (F : Family M Γ)
    (H : (Polynomial L)) (hH : AdjacentChart M F H) :
    ∃ D : PoleData M.overhead.toNat,
      K1_14_1.poleProduct D = H * H.map (frobenius L p) ∧
      (∀ i k, (D.block i).eval (nodeL k) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  let σ := frobenius L p
  rcases hH with ⟨hm, hd, _, hm', hd', _, hcop, hnode, hdet, hdet', hmarks⟩
  let A := liftPoly (M.factor * M.A₀)
  let B := liftPoly (M.factor * M.A₁)
  let Q := liftPoly M.Q
  have hdet0 : IsCoprime (Q * A) H := by
    simpa [Q, A, liftPoly, mul_assoc] using hdet
  have hdet1 : IsCoprime (Q.map σ * A.map σ) (H.map σ) := by
    simpa [Q, A, liftPoly, mul_assoc, σ, Polynomial.map_mul] using hdet'
  let D : PoleData M.overhead.toNat :=
    ⟨![H, H.map σ], ![Q, Q.map σ], ![A, A.map σ], ![B, B.map σ],
      Fin.forall_fin_two.mpr ⟨hm, hm'⟩,
      Fin.forall_fin_two.mpr ⟨hd, hd'⟩,
      hcop, Fin.forall_fin_two.mpr ⟨hdet0, hdet1⟩⟩
  refine ⟨D, rfl, ?_, ?_⟩
  · intro i k
    fin_cases i
    · exact (hnode k).1
    · exact (hnode k).2
  · intro γ hγ i
    let z := algebraMap K L (M.label γ)
    have hz : liftPoly (M.factor * M.amplitude γ) = A + (@Polynomial.C L _) z * B := by
      simp [A, B, z, P1.ModelAt.amplitude, liftPoly, mul_add, mul_left_comm]
    obtain ⟨h₀, h₁, hr₀, hr₁⟩ := hmarks γ hγ
    fin_cases i
    · change IsCoprime (A + (@Polynomial.C L _) z * B) H ∧
        H ∣ (A + (@Polynomial.C L _) z * B) * liftPoly (F.scalar γ) + (@Polynomial.C L _) z * Q
      rw [← hz]
      exact ⟨h₀, hr₀⟩
    · have hσ : (liftPoly (M.factor * M.amplitude γ)).map σ =
          A.map σ + (@Polynomial.C L _) (z^p) * B.map σ := by
        rw [hz, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
        rfl
      change IsCoprime (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) (H.map σ) ∧
        H.map σ ∣ (A.map σ + (@Polynomial.C L _) (z^p) * B.map σ) * liftPoly (F.scalar γ) +
          (@Polynomial.C L _) (z^p) * Q.map σ
      rw [← hσ]
      exact ⟨h₁, hr₁⟩
/-- The actual 69.60 family supplies both coprime pole blocks and all residues
for the same CRT lift used by the high interpolation banks. -/
theorem of_family {u del} (M : Model u del) {Γ} (F : Family M Γ) :
    ∃ D : PoleData M.overhead.toNat, Nonempty (CRTLift D) ∧
      (∀ j i, (D.block j).eval (nodeL i) ≠ 0) ∧
      ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ) := by
  obtain ⟨H, chart⟩ := adjacent_chart M F
  obtain ⟨D, _, regular, residues⟩ := chart_poles M F H chart
  exact ⟨D, P0_10_1.crt_lift D, regular, residues⟩

#print axioms of_family
end
end Lower6960.FrontPoleChart

end Merged_R6960Front6960PoleChart

-- merged module R6960Front6960HighCount
section Merged_R6960Front6960HighCount

set_option Elab.async false
namespace Lower6960
open Polynomial
open K1 (K)
open K1_14 (Equation atMark)
open K1_14_1 (PoleData CRTLift nodeL MarkResidues)
open KoalaRect (axisDegree)
open RescueGeometry (Model Family)
open scoped Polynomial

abbrev retainedCap : ℕ := 30359056712357701

/-- A bound for the actual family of simple marked sheets left by the high prefix. -/
def RetainedCount : Prop :=
  ∀ {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (_lo : 2359 ≤ M.overhead.toNat) (_hi : M.overhead.toNat ≤ 33579)
    {D : PoleData M.overhead.toNat} (_Crt : CRTLift D)
    (_regular : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (_residues : ∀ γ ∈ Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (T : Finset K) (f : Equation), T ⊆ Γ →
      3 ≤ f.natDegree → f.natDegree < 48 → axisDegree f 0 + axisDegree f 1 ≤ 2400 →
      (∀ j : Fin 2, axisDegree f j < (TerminalReceipts.witness f.natDegree).order 1) →
      (∀ γ ∈ T, TerminalMarked.simpleSheet f (M.label γ) (F.scalar γ) ∧
        ∃ q : Equation, Irreducible q ∧ q ∣ f ∧ 3 ≤ q.natDegree ∧
          atMark q (M.label γ) (F.scalar γ) = 0) →
      T.card ≤ retainedCap

theorem high_count_of_retained (retained : RetainedCount)
    {u deleted} (M : Model u deleted) {Γ} (F : Family M Γ)
    (lo : 2359 ≤ M.overhead) (hi : M.overhead ≤ 33579) :
    Γ.card ≤ 266228295297719504 := by
  have hlo : 2359 ≤ M.overhead.toNat := by omega
  have hhi : M.overhead.toNat ≤ 33579 := by omega
  obtain ⟨D, ⟨Crt⟩, regular, residues⟩ := FrontPoleChart.of_family M F
  rcases TerminalMarked.good_remainder F Crt hlo hhi regular residues with
    paid | ⟨T, f, sub, paid, degree, small, axes, grade, marks⟩
  · exact paid.trans (by decide +kernel)
  · exact (paid.trans (Nat.add_le_add_left
      (retained F hlo hhi Crt regular residues T f sub degree small axes grade marks) _)).trans_eq
      (by decide +kernel)

#print axioms high_count_of_retained
end Lower6960

end Merged_R6960Front6960HighCount

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
open RescueGeometry (Model Family)
open RetainedShortening (Word)
open scoped Polynomial
structure MarkedFiber (P : Ordinate) (z : L) (S : (Polynomial L)) : Prop where
  full : (specialize P z).natDegree=P.natDegree
  separable : ((specialize P z).map incl).Separable
  root : (specialize P z).eval S=0
abbrev scalar {u deleted} (M : Model u deleted) (γ : K) : L := algebraMap K L (M.label γ)
theorem scalar_injective {u deleted} (M : Model u deleted) : Function.Injective (scalar M) :=
  (algebraMap K L).injective.comp (RescueGeometry.label_injective M)
theorem marked_projection {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (f : Equation) (sub : T⊆Γ)
    (degree : 3≤f.natDegree) (axes : axisDegree f 0+axisDegree f 1≤2400)
    (hi : M.overhead.toNat≤33579)
    (marks : ∀ γ∈T, TerminalMarked.simpleSheet f (M.label γ) (F.scalar γ)) :
    Word 179818 164650 M.word F.scalar T ∧
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
      have hh : M.overhead≤(33579 : ℤ) := by omega
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
theorem graded_budget (e a b : ℕ) (lo : 3≤e) (hi : e<48)
    (axes : a+b≤2400) (bmax : b<(TerminalReceipts.witness e).order 1) :
    MarkedSheet.rate e*(a+p*b)+(e-1)*e≤retainedCap := by
  have numeric (i : Fin 48) : (3 ≤ i.val) →
      MarkedSheet.rate i.val*(2400+p*((TerminalReceipts.witness i.val).order 1-1))+
        (i.val-1)*i.val≤retainedCap := by
    fin_cases i <;> decide +kernel
  have hb : b≤(TerminalReceipts.witness e).order 1-1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (by omega : a≤2400) (Nat.mul_le_mul_left _ hb))) _).trans (numeric ⟨e,hi⟩ lo)
#print axioms marked_projection
#print axioms aggregate
#print axioms constant_price
#print axioms graded_budget
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
theorem live_maximum (e : Fin 48) (lo:3≤e.val) :
    rate e.val * (2400+K1.p*((TerminalReceipts.witness e.val).order 1-1))+
      (e.val-1)*e.val ≤ 27833294590898808 := by
  fin_cases e <;> decide +kernel
theorem maximum_at_42 : rate 42 * (2400+K1.p*((TerminalReceipts.witness 42).order 1-1))+
    41*42=27833294590898808 ∧
    27833294590898808+2525762121458893=retainedCap := by decide +kernel
theorem budget (e a b : ℕ) (lo:3≤e) (hi:e<48) (axes:a+b≤2400)
    (bound:b<(TerminalReceipts.witness e).order 1) : rate e*(a+K1.p*b)+(e-1)*e≤retainedCap := by
  have fit:=live_maximum ⟨e,hi⟩ lo
  have bnd : b≤(TerminalReceipts.witness e).order 1-1 := by omega
  exact (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add
    (show a≤2400 by omega) (Nat.mul_le_mul_left _ bnd))) _).trans
    (fit.trans (by decide))
#print axioms price
#print axioms budget
end Lower6960.MarkedEvaluation

end Merged_R6960MarkedEvaluationLedger
