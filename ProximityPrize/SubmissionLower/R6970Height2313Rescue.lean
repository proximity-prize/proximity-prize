import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.R6970Height2313Main

set_option Elab.async false

namespace Research6970.Height2313

open _root_.Lower6960 _root_.Research6969

section Z6969Source0614
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Rescue

noncomputable section

open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly triangle shapeSum)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (length_le_mass ordinate_eq)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open Far6969RescueGeometry (Model Family word OnMark contact_at_mark zero_of_contact)
open DifferentialContact (Native)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)
open Research6966
open Research6966.HelperAvoidance (debitAt triSlots)
open scoped Classical BigOperators

structure Plan where
  count : ℕ
  positive : 0 < count
  primeShape : Shape
  bank : Fin count → P1_7.Bank
  reserve : Fin count → ℕ
  reserve_zero : reserve ⟨0, positive⟩ = 0
  reserve_small : ∀ i, reserve i < K1.p
  prime_fit : primeShape.J ≤ primeShape.B
  stage_fit : ∀ i, (bank i).shape.J ≤ (bank i).shape.B
  initial_small : ∀ k, pairCap primeShape (bank ⟨0, positive⟩).shape k < K1.p
  degree : ℕ
  slopeFloor : ℕ
  physicalFloor : ℕ
  seedFloor : ℕ

namespace Plan

def first (plan : Plan) : Fin plan.count := ⟨0, plan.positive⟩

def initialCap (plan : Plan) : Fin 4 → ℕ :=
  pairCap plan.primeShape (plan.bank plan.first).shape

def top (plan : Plan) (h : ℕ) (i : Fin plan.count) : ℕ :=
  HelperSource.cutoffCount (plan.bank i).shape 179730 h (plan.reserve i)

def cutoff (plan : Plan) (h : ℕ) (i : Fin plan.count) : ℕ :=
  plan.top h i - 1

def surplus (plan : Plan) (h : ℕ) (i : Fin plan.count) : Prop :=
  let bank := plan.bank i
  let W := plan.top h i
  P1_7.debit h bank +
    (∑ d ∈ range W, debitAt bank.shape h W d plan.degree plan.slopeFloor plan.physicalFloor
      (triSlots bank.shape.U plan.seedFloor)) <
    triangle bank.shape.U * shapeSum bank.shape
      (fun q j => W + j - q * (131071 - h))

structure Ready (plan : Plan) (h : ℕ) : Prop where
  hpos : 0 < h
  hmax : h ≤ 131070
  rank : ∀ i, P3_7_1.BankOK (plan.bank i)
  seed_small : ∀ i, (plan.bank i).shape.U < K1.p
  wide : ∀ i, HelperSource.WidthGuard (plan.bank i) 179730 h (plan.reserve i)
  margin : ∀ i, plan.surplus h i

theorem Ready.avoid {plan : Plan} {h : ℕ} (ready : plan.Ready h)
    {D : PoleData h} (Crt : CRTLift D) (w : I → L) {G : Jet}
    (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G)
    (slope : 0 < G.natDegree) (seeded : UsesSeed G)
    (degree : plan.degree ≤ jetDegree G) (slopeFloor : plan.slopeFloor ≤ G.natDegree)
    (physicalFloor : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (seedFloor : plan.seedFloor ≤ seedDegree G) (i : Fin plan.count) :
    ∃ Q ∈ evaluated Crt w (plan.bank i).shape (plan.cutoff h i), ¬ G ∣ Q := by
  have wide := ready.wide i
  exact Research6966.HelperAvoidance.triangle_avoiding ready.hpos ready.hmax Crt w
    (plan.bank i) phys irr slope seeded (ready.seed_small i) degree slopeFloor physicalFloor
    seedFloor (ready.rank i).moment.2 ((Nat.zero_le _).trans_lt wide) wide.le
    (ready.rank i).nodes (ready.rank i).moment.1 (ready.margin i)

end Plan

private theorem initial_sections {G Q : Jet} {s t : Shape} (irr : Irreducible G)
    (avoid : ¬G∣Q) (gs : RowCaps G s) (qs : RowCaps Q t) (js : s.J≤s.B) (jt : t.J≤t.B) :
    ∃ A : Finset (Ideal Ambient), P1_7_4_1.SectionGeometry A ∧ Fits A (pairCap s t) ∧
      (∀ J∈A,toJet G∈J ∧ toJet Q∈J) ∧
      ∀ z S,jetAt G z S=0 → jetAt Q z S=0 → ∃ J∈A,OnJet J z S := by
  have proper := irreducible_cut irr avoid
  obtain ⟨A,geom,cover⟩ := K1_14_2_2_2_3.proof _ _ proper
  obtain ⟨finite,fit⟩ := section_bound _ _ proper s t js jt gs qs A geom
  refine ⟨A,?_,fit,fun J mem=>(geom J mem).2.2,cover⟩
  intro J mem
  obtain ⟨prime,dim,g,q⟩ := geom J mem
  exact ⟨prime,dim,component_height proper prime dim g q,finite J mem⟩
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (plan : Plan) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ plan.initialCap 2
  seed_points : seeds.points.card ≤ plan.initialCap 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ plan.initialCap 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (plan.initialCap)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ
private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {plan : Plan} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (plan.initialCap))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ plan) := by
  classical
  let noSeeds := A.filter (fun J=>sectionDegree J 0=0)
  let constY := A.filter (fun J=>0<sectionDegree J 0 ∧
    ¬Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let active := A.filter (fun J=>0<sectionDegree J 0 ∧
    Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl))
  let rank := active.filter (fun J=>¬dual J)
  let parents := active.filter dual
  have geomActive (J : Ideal Ambient) (mem : J∈active) : Active J ∧ J.height=2 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,height,finite⟩ := geom J hin
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (plan.initial_small k))
    exact ⟨⟨prime,dim,finite.seeds,finite.ordinate,finite.mixed,finite.jets,
      ⟨seedPos,small 0⟩,small 2,small 3,ord⟩,height⟩
  have seed_exists (J : Ideal Ambient) (mem : J∈noSeeds) :
      ∃ C : SeedCover,C.curve.totalDegree≤sectionDegree J 2 ∧ C.points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → C.Covers z := by
    obtain ⟨hin,zero⟩ := mem_filter.mp mem
    obtain ⟨prime,dim,_,finite⟩ := geom J hin
    exact seed_projection J prime dim finite zero
  let seedImage (J : Ideal Ambient) : SeedCover :=
    if mem : J∈noSeeds then Classical.choose (seed_exists J mem) else ⟨1,one_ne_zero,∅⟩
  have seed_spec (J : Ideal Ambient) (mem : J∈noSeeds) :
      (seedImage J).curve.totalDegree≤sectionDegree J 2 ∧
        (seedImage J).points.card≤sectionDegree J 3 ∧
        ∀ z S,OnJet J z S → (seedImage J).Covers z := by
    simpa only [seedImage,dite_eq_left mem] using Classical.choose_spec (seed_exists J mem)
  let onY (J : Ideal Ambient) := (Γ.filter (OnMark F J)).image fun γ=>atX (F.scalar γ)
  have ordinate_bound (J : Ideal Ambient) (mem : J∈constY) : (onY J).card≤sectionDegree J 0 := by
    obtain ⟨hin,seedPos,ord⟩ := mem_filter.mp mem
    apply le_trans (b:=1) _ seedPos
    apply card_le_one.mpr
    intro y hy z hz
    obtain ⟨γ,hγ,rfl⟩ := mem_image.mp hy
    obtain ⟨δ,hδ,rfl⟩ := mem_image.mp hz
    exact ordinate_eq (geom J hin).1 ord (mem_filter.mp hγ).2 (mem_filter.mp hδ).2
  refine ⟨⟨joinCovers noSeeds seedImage,?_,?_,constY.biUnion onY,?_,rank,parents,?_,?_,?_,?_,?_⟩⟩
  · exact (joinCovers_degree _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 2).trans (fit 2)))
  · exact (joinCovers_points _ _).trans ((sum_le_sum fun J mem=>(seed_spec J mem).2.1).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 3).trans (fit 3)))
  · exact card_biUnion_le.trans ((sum_le_sum ordinate_bound).trans
      ((K1_14_2_2.mass_mono (filter_subset _ _) 0).trans (fit 0)))
  · intro J mem
    exact ⟨(geomActive J (mem_filter.mp mem).1).1,(mem_filter.mp mem).2⟩
  · intro J mem
    obtain ⟨hin,d⟩ := mem_filter.mp mem
    obtain ⟨act,ht⟩ := geomActive J hin
    exact ⟨act,d,ht,rows J (mem_filter.mp hin).1⟩
  · exact disjoint_left.mpr fun _ a b=>(mem_filter.mp a).2 (mem_filter.mp b).2
  · apply K1_14_2_2.fits_mono _ fit
    exact union_subset ((filter_subset _ _).trans (filter_subset _ _))
      ((filter_subset _ _).trans (filter_subset _ _))
  · intro γ hγ zero
    obtain ⟨J,hin,on⟩ := cover γ hγ zero
    by_cases z : sectionDegree J 0=0
    · have mem : J∈noSeeds := mem_filter.mpr ⟨hin,z⟩
      exact Or.inl (joinCovers_covers mem ((seed_spec J mem).2.2 _ _ on))
    · by_cases ord : Function.Injective ((Ideal.Quotient.mk J).comp ordinateIncl)
      · have mem : J∈active := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        by_cases d : dual J
        · exact Or.inr (Or.inr (Or.inr ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨J,mem_filter.mpr ⟨mem,d⟩,on⟩))
      · have mem : J∈constY := mem_filter.mpr ⟨hin,Nat.pos_of_ne_zero z,ord⟩
        exact Or.inr (Or.inl (mem_biUnion.mpr ⟨J,mem,
          mem_image.mpr ⟨γ,mem_filter.mpr ⟨hγ,on⟩,rfl⟩⟩))
theorem initial_cover {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {plan : Plan} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (plan.primeShape)) (capsQ : RowCaps Q₀ (plan.bank plan.first).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ plan) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (plan.prime_fit)
    (plan.stage_fit plan.first)
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))
theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {plan : Plan} (initial : Initial F G Q₀ plan) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

theorem history_from_initial {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G : Jet} {plan : Plan} (irr : Irreducible G) (capsG : RowCaps G (plan.primeShape))
    (Q : Fin plan.count→Jet) (init : Initial F G (Q plan.first) plan) (avoid : ∀ i,¬G∣Q i)
    (caps : ∀ i,RowCaps (Q i) (plan.bank i).shape)
    (contact : ∀ i γ,γ∈Γ → Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ)))
      (plan.reserve i+1) (Q i)) :
    ∃ kept : ℕ→Finset (Ideal Ambient),
      kept 0=init.parents ∧ kept 1=init.parents ∧ Antitone kept ∧
      (∀ i : Fin plan.count,∀ n,i.val<n → ∀ J∈kept n,Native J (plan.reserve i+1) (Q i)) ∧
      (∀ i : Fin plan.count,∀ n,i.val<n → ∀ c : Fin 4,
        (plan.reserve i+1)*mass (kept n) c≤pairCap (plan.primeShape) (plan.bank i).shape c) ∧
      ∀ i : Fin plan.count,∀ J∈kept i.val,J∉kept (i.val+1) →
        ∃ C : Jet,RowCaps C (plan.bank i).shape ∧ toJet C∉J ∧
          ∀ γ∈Γ,jetAt C (M.label γ) (F.scalar γ)=0 := by
  have on (J : Ideal Ambient) (mem : J∈init.parents) : Active J ∧ dual J ∧ toJet G∈J :=
    let h := init.parent_geom J mem
    ⟨h.1,h.2.1,h.2.2.2.1⟩
  choose S sub pass bound cut using fun i =>
    ExceptionalStage.filter irr (avoid i) capsG (caps i) plan.prime_fit
      (plan.stage_fit i) init.parents on (plan.reserve i) (plan.reserve_small i)
  let selected (i : Fin plan.count) := if i = plan.first then init.parents else S i
  have first : selected plan.first=init.parents := by simp [selected]
  have rzero : plan.reserve plan.first=0 := plan.reserve_zero
  have contact_zero (J : Ideal Ambient) (mem : J∈init.parents) : Native J (plan.reserve plan.first+1) (Q plan.first) := by
    intro w hw
    have hz : w.length = 0 := by omega
    rw [List.length_eq_zero_iff.mp hz]
    exact (init.parent_geom J mem).2.2.2.2
  have sel_pass (i : Fin plan.count) (J : Ideal Ambient) (mem : J∈selected i) :
      Native J (plan.reserve i+1) (Q i) := by
    by_cases zi : i = plan.first
    · subst i; exact contact_zero J (first ▸ mem)
    · exact pass i J (by simpa only [selected,ite_eq_right zi] using mem)
  have sel_bound (i : Fin plan.count) (c : Fin 4) :
      (plan.reserve i+1)*mass (selected i) c≤pairCap (plan.primeShape) (plan.bank i).shape c := by
    by_cases zi : i = plan.first
    · subst i
      rw [rzero, Nat.zero_add, first, one_mul]
      exact K1_14_2_2.mass_mono (subset_union_right (s₁:=init.rankExit) (s₂:=init.parents)) c
        |>.trans (init.fits c)
    · simpa only [selected,ite_eq_right zi] using bound i c
  let kept (n : ℕ) := init.parents.filter (fun J=>∀ i : Fin plan.count,i.val<n → J∈selected i)
  have spec {J n} : J∈kept n ↔ J∈init.parents ∧ ∀ i : Fin plan.count,i.val<n → J∈selected i := mem_filter
  refine ⟨kept,?_,?_,?_,?_,?_,?_⟩
  · ext J; simp [kept]
  · ext J
    refine ⟨fun h=>(spec.mp h).1,fun h=>spec.mpr ⟨h,?_⟩⟩
    intro i hi
    have zi : i = plan.first := Fin.ext (by change i.val = 0; omega)
    subst i
    exact first.symm ▸ h
  · intro n m h J mem
    exact spec.mpr ⟨(spec.mp mem).1,fun i hi=>(spec.mp mem).2 i (hi.trans_le h)⟩
  · intro i n hi J mem
    exact sel_pass i J ((spec.mp mem).2 i hi)
  · intro i n hi c
    have hsub : kept n⊆selected i := fun _ mem=>(spec.mp mem).2 i hi
    exact (Nat.mul_le_mul_left _ (K1_14_2_2.mass_mono hsub c)).trans (sel_bound i c)
  · intro i J prev lost
    obtain ⟨root,prior⟩ := spec.mp prev
    have fail : J∉selected i := by
      intro pass
      apply lost (spec.mpr ⟨root,?_⟩)
      intro j hj
      by_cases same : j=i
      · exact same ▸ pass
      · apply prior
        have diff : j.val≠i.val := fun h=>same (Fin.ext h)
        omega
    have nz : i ≠ plan.first := by
      intro z
      subst i
      exact fail (first.symm ▸ root)
    obtain ⟨C,cap,proper,zero⟩ := cut i J root (by simpa only [selected,ite_eq_right nz] using fail)
    exact ⟨C,cap,proper,fun γ hγ=>zero _ _ (contact i γ hγ)⟩

structure Run {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (G : Jet) (plan : Plan) where
  row : Fin plan.count → Jet
  row_mem : ∀ i, row i ∈ evaluated Crt (word M) (plan.bank i).shape (plan.cutoff M.overhead.toNat i)
  avoids : ∀ i, ¬ G ∣ row i
  initial : Initial F G (row plan.first) plan
  kept : ℕ → Finset (Ideal Ambient)
  start : kept 0 = initial.parents
  intro_pass : kept 1 = initial.parents
  antitone : Antitone kept
  passed : ∀ (i : Fin plan.count) n, i.val < n → ∀ J ∈ kept n, Native J (plan.reserve i+1) (row i)
  cap : ∀ (i : Fin plan.count) n, i.val < n → ∀ k : Fin 4,
    (plan.reserve i+1)*mass (kept n) k ≤ pairCap plan.primeShape (plan.bank i).shape k
  cut : ∀ (i : Fin plan.count), ∀ J ∈ kept i.val, J ∉ kept (i.val+1) →
    ∃ C : Jet, RowCaps C (plan.bank i).shape ∧ toJet C ∉ J ∧
      ∀ γ∈Γ, jetAt C (M.label γ) (F.scalar γ) = 0

theorem prepare {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D) (plan : Plan)
    (ready : plan.Ready M.overhead.toNat)
    (noPole : ∀ j i,(D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ,MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (irr : Irreducible G)
    (slope : 0 < G.natDegree) (seeded : UsesSeed G) (capsG : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (slopeFloor : plan.slopeFloor ≤ G.natDegree)
    (physicalFloor : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) (seedFloor : plan.seedFloor ≤ seedDegree G) :
    Nonempty (Run F Crt G plan) := by
  choose Q inside avoid using ready.avoid Crt (word M) phys irr slope seeded degree
    slopeFloor physicalFloor seedFloor
  have caps (i : Fin plan.count) : RowCaps (Q i) (plan.bank i).shape :=
    evaluated_shape Crt (word M) (inside i)
  have contact (i : Fin plan.count) (γ : K) (hγ : γ∈Γ) :
      Native (RingHom.ker (jetMarkHom (M.label γ) (F.scalar γ))) (plan.reserve i+1) (Q i) :=
    contact_at_mark F Crt noPole residues (inside i)
      (FreeSource.buffered_fit (plan.bank i) 179730 _ (plan.reserve i) (ready.wide i)) γ hγ
  obtain ⟨ini⟩ := initial_cover F irr (avoid plan.first) capsG (caps plan.first)
    (fun γ hγ => zero_of_contact (contact plan.first γ hγ))
  obtain ⟨kept, start, intro_pass, anti, passed, cap, cut⟩ :=
    history_from_initial irr capsG Q ini avoid caps contact
  exact ⟨⟨Q, inside, avoid, ini, kept, start, intro_pass, anti, passed, cap, cut⟩⟩

theorem Run.parent_geom {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan} (R : Run F Crt G plan)
    {n : ℕ} {J : Ideal Ambient} (mem : J∈R.kept n) :
    Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet (R.row plan.first)∈J :=
  R.initial.parent_geom J (R.start ▸ R.antitone (Nat.zero_le n) mem)


end
end Lower6960.Prefix6969Rescue
end Z6969Source0614


section Z6969Source0615
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset
open K1 (K)
open K1_14 (Shape Jet jetAt atX)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover RowCaps Active emptyCut joinCuts joinCuts_cost mass mass_mono
  weight dot sectionDegree sum_dot)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono dotQ weightedBill bill_bound_with_final)
open Far6969RescueGeometry (Model Family OnMark OnSurface proper_cut beforeCuts)
open scoped BigOperators Classical

def Plan.cutShape (plan : Plan) (i : ℕ) : Shape :=
  if hi : i + 1 < plan.count then (plan.bank ⟨i + 1, hi⟩).shape else ⟨0, 0, 0, 0⟩

def Plan.history (plan : Plan) : ℕ → Mass
  | 0 => fun k => plan.initialCap k
  | i + 1 =>
    if hi : i + 1 < plan.count then
      let j : Fin plan.count := ⟨i + 1, hi⟩
      fun k => min (plan.history i k)
        ((pairCap plan.primeShape (plan.bank j).shape k : ℚ) / (plan.reserve j + 1 : ℕ))
    else plan.history i

section Run

variable {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable (R : Run F Crt G plan)

/-- Stage zero introduces the parent set, so the cut list starts at stage one. -/
def Run.live (i : ℕ) : Finset (Ideal Ambient) := R.kept (i + 1)

def Run.lost (i : ℕ) : Finset (Ideal Ambient) := R.live i \ R.live (i + 1)

theorem Run.live_start : R.live 0 = R.initial.parents := R.intro_pass

theorem Run.next_sub (i : ℕ) : R.live (i + 1) ⊆ R.live i :=
  R.antitone (Nat.le_succ (i + 1))

theorem Run.live_mass (i : ℕ) (hi : i < plan.count) (k : Fin 4) :
    massQ (R.live i) k ≤ plan.history i k := by
  induction i with
  | zero =>
    rw [R.live_start]
    exact (Nat.cast_le (α := ℚ)).mpr
      ((mass_mono (subset_union_right : R.initial.parents ⊆ R.initial.rankExit ∪ R.initial.parents)
        k).trans (R.initial.fits k))
  | succ i ih =>
    rw [Plan.history, dite_eq_left hi]
    apply le_min
    · exact (massQ_mono (R.next_sub i) k).trans (ih (by omega))
    · let j : Fin plan.count := ⟨i + 1, hi⟩
      have hcap := R.cap j (i + 1 + 1) (by change i+1 < i+1+1; omega) k
      apply (le_div_iff₀ (by positivity : (0 : ℚ) < ((plan.reserve j + 1 : ℕ) : ℚ))).mpr
      have h : mass (R.live (i + 1)) k * (plan.reserve j + 1) ≤
          pairCap plan.primeShape (plan.bank j).shape k := by
        simpa only [Run.live, Nat.mul_comm] using hcap
      change (mass (R.live (i + 1)) k : ℚ) * ((plan.reserve j + 1 : ℕ) : ℚ) ≤
        (pairCap plan.primeShape (plan.bank j).shape k : ℚ)
      exact_mod_cast h

theorem Run.cut_cover {i : ℕ} (hi : i + 1 < plan.count) :
    ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, (∃ J∈R.lost i, OnMark F J γ) →
        γ ∈ C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
  let j : Fin plan.count := ⟨i + 1, hi⟩
  have shape : plan.cutShape i = (plan.bank j).shape := by
    rw [Plan.cutShape, dite_eq_left hi]
  have oneCut (J : Ideal Ambient) (mem : J∈R.lost i) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤
        dot (weight (plan.cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
    obtain ⟨present, absent⟩ := mem_sdiff.mp mem
    obtain ⟨P, caps, proper, roots⟩ := R.cut j J present absent
    rw [shape]
    exact proper_cut F _ (plan.stage_fit j) (R.parent_geom present).1 caps proper roots
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈R.lost i then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈R.lost i) :
      (∀ fee, (C J).cost fee ≤ dot (weight (plan.cutShape i) fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves, OnMark F Q γ := by
    simpa only [C, dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts (R.lost i) C, ?_, ?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans
      ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J, mem, on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q, hQ, hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J, mem, point⟩)
    · exact Or.inr ⟨Q, mem_biUnion.mpr ⟨J, mem, hQ⟩, hmark⟩

theorem Run.retained_or_lost (stop : ℕ) {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈R.live stop ∨ ∃ i < stop, J∈R.lost i := by
  by_cases h : ∃ i < stop, J∈R.lost i
  · exact Or.inr h
  · left
    have live : ∀ n ≤ stop, J∈R.live n := by
      intro n hn
      induction n with
      | zero => exact R.live_start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n, by omega, mem_sdiff.mpr ⟨ih (by omega), absent⟩⟩
    exact live stop le_rfl

private def Run.jointLive : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit ∪ R.initial.parents
  | i + 1 => R.live i

private def Run.jointLost : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i + 1 => R.lost i

/-- Stopping before terminal interpolation keeps the complete final credit. -/
theorem Run.early_bill (stop : ℕ) (stop_ok : stop < plan.count) (rank : Mass) (cut : ℕ → Mass) :
    dotQ rank (massQ R.initial.rankExit) + (∑ i∈range stop, dotQ (cut i) (massQ (R.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) (stop + 1)) (massQ (R.live stop)) ≤
      weightedBill (stop + 1) (beforeCuts rank cut)
        (beforeCuts (fun k => plan.initialCap k) plan.history) := by
  have bill := bill_bound_with_final (stop + 1) (beforeCuts rank cut)
    (beforeCuts (fun k => plan.initialCap k) plan.history) R.jointLive R.jointLost ?_ ?_ ?_
  · rw [sum_range_succ'] at bill
    simpa only [beforeCuts, Run.jointLost, Run.jointLive, add_comm] using bill
  · intro i hi
    cases i with
    | zero => simpa only [Run.jointLive, R.live_start] using
        (subset_union_right : R.initial.parents ⊆ R.initial.rankExit ∪ R.initial.parents)
    | succ i => exact R.next_sub i
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem, ?_⟩
      rw [Run.jointLive, R.live_start]
      exact fun h => (disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α := ℚ)).mpr (R.initial.fits k)
    | succ i => exact R.live_mass i (by omega) k

theorem Run.stop_surfaces (stop : ℕ) :
    ∃ S : Finset Surface,
      (∀ q∈S, Parent q ∧ ∃ J∈R.live stop, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈Γ, (∃ J∈R.live stop, OnMark F J γ) → ∃ q∈S, OnSurface F q γ := by
  let getGeom (J : R.live stop) := R.parent_geom J.property
  let surface (J : R.live stop) := surfaceOf J.val (getGeom J).1.prime
  let S := (R.live stop).attach.image surface
  refine ⟨S, ?_, ?_⟩
  · intro q hq
    obtain ⟨J, _, rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1, J.val, J.property, rfl⟩
  · rintro γ _ ⟨J, hJ, on⟩
    let q : R.live stop := ⟨J, hJ⟩
    refine ⟨surface q, mem_image.mpr ⟨q, mem_attach _ _, rfl⟩, ?_⟩
    intro P mem
    rw [← K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Run.stop_books (stop : ℕ) (stop_ok : stop < plan.count) :
    ∃ C : ℕ → CutCover,
      (∀ i < stop, ∀ fee, (C i).cost fee ≤
        dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0 →
        R.initial.seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ R.initial.ordinates ∨
        (∃ J∈R.initial.rankExit, OnMark F J γ) ∨
        (∃ i < stop, γ ∈ (C i).direct ∨ ∃ Q∈(C i).curves, OnMark F Q γ) ∨
        ∃ J∈R.live stop, OnMark F J γ := by
  have pick (i : ℕ) : ∃ C : CutCover, i < stop →
      (∀ fee, C.cost fee ≤ dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, (∃ J∈R.lost i, OnMark F J γ) →
        γ∈C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
    by_cases hi : i < stop
    · obtain ⟨C, fee, covers⟩ := R.cut_cover (i := i) (by omega)
      exact ⟨C, fun _ => ⟨fee, covers⟩⟩
    · exact ⟨emptyCut, fun h => (hi h).elim⟩
  choose C valid using pick
  refine ⟨C, fun i h => (valid i h).1, ?_⟩
  intro γ hγ hG
  rcases R.initial.covers γ hγ hG with seed | ordinate | rank | ⟨J, parent, marked⟩
  · exact Or.inl seed
  · exact Or.inr (Or.inl ordinate)
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases R.retained_or_lost stop parent with live | ⟨i, hi, lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨J, live, marked⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, (valid i hi).2 γ hγ ⟨J,lost,marked⟩⟩)))

end Run


end
end Lower6960.Prefix6969Rescue
end Z6969Source0615


section Z6969Source0616
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Research6969.PhysicalWindow
open Research6966
open Far6969RescueGeometry (Model Family)
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (UsesSeed)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)

def Plan.request (plan : Plan) (i : Fin plan.count) : Request :=
  ⟨plan.bank i, plan.reserve i, plan.degree, plan.slopeFloor, plan.physicalFloor, plan.seedFloor⟩

structure Plan.Sources (plan : Plan) (first last : ℕ) : Prop where
  first_pos : 0 < first
  last_safe : last ≤ 131070
  slope_pos : 0 < plan.slopeFloor
  rank : ∀ i, P3_7_1.BankOK (plan.bank i)
  reserve_fit : ∀ i, 2 * plan.reserve i ≤ (plan.bank i).shape.B
  seed_small : ∀ i, (plan.bank i).shape.U < K1.p
  narrow : ∀ i, (plan.bank i).shape.J < 131071-last
  width : ∀ i, HelperSource.WidthGuard (plan.bank i) 179730 first (plan.reserve i)
  covers : ∀ i, ∃ ends, Cover (Triangular (plan.request i)) last first ends

theorem Plan.Sources.ready {plan : Plan} {first last h : ℕ} (S : plan.Sources first last)
    (lo : first ≤ h) (hi : h ≤ last) : plan.Ready h := by
  refine ⟨S.first_pos.trans_le lo, hi.trans S.last_safe, S.rank, S.seed_small, ?_, ?_⟩
  · intro i
    exact HelperSource.width_at_height (plan.bank i) 179730 first h (plan.reserve i) lo
      (hi.trans (S.last_safe.trans (by decide))) (S.reserve_fit i) (S.width i)
  · intro i
    obtain ⟨ends, cov⟩ := S.covers i
    obtain ⟨left,right,hlo,hhi,high,cert⟩ := covered cov lo hi
    exact triangle_positive (plan.request i) (S.first_pos.trans_le lo) hlo hhi
      ((S.narrow i).trans_le (Nat.sub_le_sub_left high 131071)) S.slope_pos cert

/-- Instantiate the single physical rescue producer from a bank/height receipt. -/
theorem Plan.Sources.run {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {plan : Plan} {first last : ℕ} (S : plan.Sources first last)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : plan.slopeFloor ≤ G.natDegree) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) : Nonempty (Run F Crt G plan) :=
  Prefix6969Rescue.prepare F Crt plan (S.ready lo hi) noPole residues phys prime.irreducible
    (S.slope_pos.trans_le slope) seeded caps degree slope physical seed


end
end Lower6960.Prefix6969Rescue
end Z6969Source0616


section Z6969Source0617
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet Shape atX jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (CutCover emptyCut joinCuts joinCuts_cost mass mass_mono weight dot
  sectionDegree sum_dot)
open K1_14_3 (Surface Parent)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open P1_7_4 (Mass massQ massQ_mono dotQ weightedBill bill_bound bill_bound_with_final)
open Far6969RescueGeometry (Model Family OnMark OnSurface word contact_at_mark zero_of_contact
  proper_cut beforeCuts)
open Prefix6969Wide (terminalShape TerminalPass SurfacePass terminal_failure)
open scoped BigOperators Classical

variable {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

structure Book (R : Run F Crt G plan) where
  steps : ℕ
  live : ℕ → Finset (Ideal Ambient)
  shape : ℕ → Shape
  capacity : ℕ → Mass
  start : live 0 = R.initial.parents
  next : ∀ i < steps, live (i + 1) ⊆ live i
  bound : ∀ i < steps, ∀ k, massQ (live i) k ≤ capacity i k
  initial_bound : ∀ i < steps, ∀ k, massQ (live i) k ≤ (plan.initialCap k : ℚ)
  cut : ℕ → CutCover
  cut_cost : ∀ i < steps, ∀ fee,
    (cut i).cost fee ≤ dot (weight (shape i) fee) (mass (live i \ live (i + 1)))
  cut_cover : ∀ i < steps, ∀ γ ∈ Γ,
    (∃ J ∈ live i \ live (i + 1), OnMark F J γ) →
    γ ∈ (cut i).direct ∨ ∃ J ∈ (cut i).curves, OnMark F J γ

variable (R : Run F Crt G plan)

def Book.lost {R : Run F Crt G plan} (B : Book R) (i : ℕ) := B.live i \ B.live (i + 1)
def Book.final {R : Run F Crt G plan} (B : Book R) := B.live B.steps

theorem Book.early (stop : ℕ) (fits : stop < plan.count) :
    ∃ B : Book R, B.steps = stop ∧ B.final = R.live stop ∧
      B.shape = plan.cutShape ∧ B.capacity = plan.history := by
  have pick (i : ℕ) : ∃ C : CutCover, i < stop →
      (∀ fee, C.cost fee ≤ dot (weight (plan.cutShape i) fee) (mass (R.lost i))) ∧
      ∀ γ∈Γ, (∃ J∈R.lost i, OnMark F J γ) →
        γ∈C.direct ∨ ∃ J∈C.curves, OnMark F J γ := by
    by_cases hi : i < stop
    · obtain ⟨C, cost, cover⟩ := R.cut_cover (i := i) (by omega)
      exact ⟨C, fun _ => ⟨cost, cover⟩⟩
    · exact ⟨emptyCut, fun h => (hi h).elim⟩
  choose C valid using pick
  have initialCap (i : ℕ) (k : Fin 4) :
      massQ (R.live i) k ≤ (plan.initialCap k : ℚ) := by
    have sub : R.live i ⊆ R.initial.rankExit ∪ R.initial.parents := by
      rw [← R.start]
      exact (R.antitone (Nat.zero_le _)).trans subset_union_right
    exact (Nat.cast_le (α := ℚ)).mpr ((mass_mono sub k).trans (R.initial.fits k))
  exact ⟨⟨stop, R.live, plan.cutShape, plan.history, R.live_start, fun i _ => R.next_sub i,
    fun i hi k => R.live_mass i (hi.trans fits) k, fun i _ k => initialCap i k, C,
    fun i h => (valid i h).1, fun i h => (valid i h).2⟩, rfl, rfl, rfl, rfl⟩

def Run.terminal (R : Run F Crt G plan) : Finset (Ideal Ambient) :=
  (R.live (plan.count - 1)).filter (TerminalPass Crt (word M))

private theorem Run.terminal_cut
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ C : CutCover,
      (∀ fee, C.cost fee ≤ dot (weight terminalShape fee) (mass (R.live (plan.count - 1) \ R.terminal))) ∧
      ∀ γ∈Γ, (∃ J ∈ R.live (plan.count - 1) \ R.terminal, OnMark F J γ) →
        γ∈C.direct ∨ ∃ J∈C.curves, OnMark F J γ := by
  let lost := R.live (plan.count - 1) \ R.terminal
  have oneCut (J : Ideal Ambient) (mem : J∈lost) :
      ∃ C : CutCover, (∀ fee, C.cost fee ≤ dot (weight terminalShape fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈C.direct ∨ ∃ Q∈C.curves, OnMark F Q γ := by
    obtain ⟨present, absent⟩ := mem_sdiff.mp mem
    have hfail : ¬ TerminalPass Crt (word M) J :=
      fun pass => absent (mem_filter.mpr ⟨present, pass⟩)
    obtain ⟨s, P, multiplicity, inside, cap, avoids⟩ := terminal_failure Crt (word M) hfail
    have zero (γ : K) (hit : γ ∈ Γ) : jetAt P (M.label γ) (F.scalar γ) = 0 := by
      apply zero_of_contact (r := 0)
      apply contact_at_mark F Crt noPole residues inside _ γ hit
      simpa only [Nat.mul_zero, Nat.add_zero] using
        Nat.sub_lt (Nat.mul_pos multiplicity (by decide : 0 < 179730)) (by decide : 0 < 1)
    exact proper_cut F _ (by decide) (R.parent_geom present).1 cap avoids zero
  let C (J : Ideal Ambient) : CutCover :=
    if mem : J∈lost then Classical.choose (oneCut J mem) else emptyCut
  have spec (J : Ideal Ambient) (mem : J∈lost) :
      (∀ fee, (C J).cost fee ≤ dot (weight terminalShape fee) (sectionDegree J)) ∧
        ∀ γ∈Γ, OnMark F J γ → γ∈(C J).direct ∨ ∃ Q∈(C J).curves, OnMark F Q γ := by
    simpa only [C, dite_eq_left mem] using Classical.choose_spec (oneCut J mem)
  refine ⟨joinCuts lost C, ?_, ?_⟩
  · intro fee
    exact (joinCuts_cost _ _ _).trans
      ((sum_le_sum fun J mem => (spec J mem).1 fee).trans_eq (sum_dot _ _))
  · rintro γ hγ ⟨J, mem, on⟩
    rcases (spec J mem).2 γ hγ on with point | ⟨Q, hQ, hmark⟩
    · exact Or.inl (mem_biUnion.mpr ⟨J, mem, point⟩)
    · exact Or.inr ⟨Q, mem_biUnion.mpr ⟨J, mem, hQ⟩, hmark⟩

def Plan.normalShape (plan : Plan) (i : ℕ) : Shape :=
  if i + 1 < plan.count then plan.cutShape i else terminalShape

/-- The final cut is the actual terminal-bank test, with its own envelope. -/
theorem Book.normal
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ B : Book R, B.steps = plan.count ∧ B.final = R.terminal ∧
      B.shape = plan.normalShape ∧ B.capacity = plan.history := by
  obtain ⟨Cₜ, cₜ, hₜ⟩ := R.terminal_cut noPole residues
  let live (i : ℕ) := if i < plan.count then R.live i else R.terminal
  let shape := plan.normalShape
  have step (i : ℕ) (hi : i < plan.count) : live (i + 1) ⊆ live i := by
    by_cases next : i + 1 < plan.count
    · simpa only [live, ite_eq_left hi, ite_eq_left next] using R.next_sub i
    · have eq : i = plan.count - 1 := by omega
      have old : live i = R.live (plan.count - 1) := by rw [show live i = R.live i from if_pos hi, eq]
      have new : live (i + 1) = R.terminal := by simp only [live, ite_eq_right next]
      rw [old, new]
      exact filter_subset _ _
  have pick (i : ℕ) : ∃ C : CutCover, i < plan.count →
      (∀ fee, C.cost fee ≤ dot (weight (shape i) fee) (mass (live i \ live (i+1)))) ∧
      ∀ γ∈Γ, (∃ J ∈ live i \ live (i+1), OnMark F J γ) →
        γ∈C.direct ∨ ∃ J∈C.curves, OnMark F J γ := by
    by_cases hn : i < plan.count
    · by_cases next : i+1 < plan.count
      · obtain ⟨C, c, hC⟩ := R.cut_cover next
        exact ⟨C, fun _ => by simpa only [shape, Plan.normalShape, live, ite_eq_left hn, ite_eq_left next,
          Run.lost] using And.intro c hC⟩
      · have eq : i = plan.count - 1 := by omega
        have old : live i = R.live (plan.count - 1) := by rw [show live i = R.live i from if_pos hn, eq]
        have new : live (i + 1) = R.terminal := by simp only [live, ite_eq_right next]
        have last : shape i = terminalShape := by simp only [shape, Plan.normalShape, ite_eq_right next]
        exact ⟨Cₜ, fun _ => by simpa only [last, old, new] using And.intro cₜ hₜ⟩
    · exact ⟨emptyCut, fun h => (hn h).elim⟩
  choose C valid using pick
  have initialCap (i : ℕ) (hi : i < plan.count) (k : Fin 4) :
      massQ (live i) k ≤ (plan.initialCap k : ℚ) := by
    simp only [live, ite_eq_left hi]
    have sub : R.live i ⊆ R.initial.rankExit ∪ R.initial.parents := by
      rw [← R.start]
      exact (R.antitone (Nat.zero_le _)).trans subset_union_right
    exact (Nat.cast_le (α := ℚ)).mpr ((mass_mono sub k).trans (R.initial.fits k))
  refine ⟨⟨plan.count, live, shape, plan.history, ?_, step,
    fun i hi k => by simpa only [live, ite_eq_left hi] using R.live_mass i hi k,
    initialCap, C, fun i h => (valid i h).1, fun i h => (valid i h).2⟩, rfl, ?_, rfl, rfl⟩
  · simpa only [live, ite_eq_left plan.positive] using R.live_start
  · change live plan.count = R.terminal
    simp only [live, Nat.lt_irrefl, ite_false]

variable {R} (B : Book R)

theorem Book.retained_or_lost {J : Ideal Ambient} (mem : J∈R.initial.parents) :
    J∈B.final ∨ ∃ i < B.steps, J∈B.lost i := by
  by_cases h : ∃ i < B.steps, J∈B.lost i
  · exact Or.inr h
  · left
    have live : ∀ n ≤ B.steps, J∈B.live n := by
      intro n hn
      induction n with
      | zero => exact B.start.symm ▸ mem
      | succ n ih =>
        by_contra absent
        exact h ⟨n, by omega, mem_sdiff.mpr ⟨ih (by omega), absent⟩⟩
    exact live B.steps le_rfl

theorem Book.cut_marks {γ : K} (hγ : γ ∈ Γ)
    (roots : jetAt G (M.label γ) (F.scalar γ) = 0) :
    R.initial.seeds.Covers (M.label γ) ∨ atX (F.scalar γ) ∈ R.initial.ordinates ∨
    (∃ J∈R.initial.rankExit, OnMark F J γ) ∨
    (∃ i < B.steps, γ ∈ (B.cut i).direct ∨ ∃ Q∈(B.cut i).curves, OnMark F Q γ) ∨
    ∃ J∈B.final, OnMark F J γ := by
  rcases R.initial.covers γ hγ roots with seed | ordinate | rank | ⟨J, parent, marked⟩
  · exact Or.inl seed
  · exact Or.inr (Or.inl ordinate)
  · exact Or.inr (Or.inr (Or.inl rank))
  · rcases B.retained_or_lost parent with live | ⟨i, hi, lost⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨J, live, marked⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, hi, B.cut_cover i hi γ hγ ⟨J,lost,marked⟩⟩)))

private def Book.jointLive : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit ∪ R.initial.parents
  | i + 1 => B.live i

private def Book.jointLost : ℕ → Finset (Ideal Ambient)
  | 0 => R.initial.rankExit
  | i + 1 => B.lost i

theorem Book.joint_bill (rank : Mass) (cut : ℕ → Mass) :
    dotQ rank (massQ R.initial.rankExit) +
      (∑ i∈range B.steps, dotQ (cut i) (massQ (B.lost i))) +
      dotQ (P1_7_4.running (beforeCuts rank cut) (B.steps + 1)) (massQ B.final) ≤
      weightedBill (B.steps + 1) (beforeCuts rank cut)
        (beforeCuts (fun k => plan.initialCap k) B.capacity) := by
  have bill := bill_bound_with_final (B.steps + 1) (beforeCuts rank cut)
    (beforeCuts (fun k => plan.initialCap k) B.capacity) B.jointLive B.jointLost ?_ ?_ ?_
  · rw [sum_range_succ'] at bill
    simp only [beforeCuts, Book.jointLost, Book.jointLive, Book.final] at bill ⊢
    linarith only [bill]
  · intro i hi
    cases i with
    | zero => simpa only [Book.jointLive, B.start] using
        (subset_union_right : R.initial.parents ⊆ R.initial.rankExit ∪ R.initial.parents)
    | succ i => exact B.next i (by omega)
  · intro i hi
    cases i with
    | zero =>
      intro J mem
      apply mem_sdiff.mpr
      refine ⟨mem_union_left _ mem, ?_⟩
      rw [Book.jointLive, B.start]
      exact fun h => (disjoint_left.mp R.initial.disjoint) mem h
    | succ i => exact subset_rfl
  · intro i hi k
    cases i with
    | zero => exact (Nat.cast_le (α := ℚ)).mpr (R.initial.fits k)
    | succ i => exact B.bound i (by omega) k

end


end Lower6960.Prefix6969Rescue
end Z6969Source0617


section Z6969Source0636
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

namespace Lower6960.Prefix6969Rescue

noncomputable section

open Polynomial Finset ProximityPrize.Benchmark
open K1 (K I p)
open K1_14 (Jet FX Shape atX graphEval jetAt)
open K1_14_2 (OnJet)
open K1_14_2_2 (CutCover RowCaps)
open K1_14_2_2_2_1 (jetDegree)
open Far6969RescueGeometry (Model Family OnMark label_injective)
open Research6966
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open Research6969
open scoped Classical Differential
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds

abbrev graphShape (a u : ℕ) : Shape := ⟨0, a, 1, u⟩

abbrev denominator (G : Jet) : Eqn (Fin 2) FX := G.coeff 1
abbrev numerator (G : Jet) : Eqn (Fin 2) FX := -G.coeff 0

def regular (G : Jet) (z : K) (S : Polynomial K) : Prop :=
  evaluate (NativeLostCurve.seed z) (atX S) (denominator G) ≠ 0

private theorem evaluation_eq (P : Eqn (Fin 2) FX) (z : K) (S : Polynomial K) :
    evaluate (NativeLostCurve.seed z) (atX S) P = P.eval₂ (graphEval z) (atX S) := rfl

theorem graph_law {G : Jet} (slope : G.natDegree = 1) {z : K} {S : Polynomial K}
    (root : jetAt G z S = 0) :
    evaluate (NativeLostCurve.seed z) (atX S) (denominator G) * atX S.derivative =
      evaluate (NativeLostCurve.seed z) (atX S) (numerator G) := by
  simp only [evaluation_eq]
  let ev := eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  change ev G = 0 at root
  have id := congrArg ev (eq_X_add_C_of_natDegree_le_one slope.le)
  simp only [ev, map_add, map_mul, coe_eval₂RingHom, eval₂_C, eval₂_X] at id
  unfold numerator denominator
  rw [eval₂_neg]
  apply eq_neg_of_add_eq_zero_left
  exact id.symm.trans root

private theorem seed_cap {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u))
    (j i : ℕ) : ((G.coeff j).coeff i).totalDegree ≤ u := by
  by_cases hz : (G.coeff j).coeff i = 0
  · simp [hz]
  · exact (caps j i hz).2.2

theorem coefficient_cap {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u)) (j : ℕ) :
    cap (fun _ => 1) u (G.coeff j) := by
  intro i
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro m hm
  change m.weight (fun _ => 1) ≤ u
  rw [← Finsupp.degree_eq_weight_one]
  exact (MvPolynomial.le_totalDegree hm).trans (seed_cap caps j i)

private theorem denominator_degree {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u)) :
    (denominator G).natDegree ≤ a - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_contra hn
  have hb := (caps 1 i hn).1
  change i + 1 ≤ a at hb
  omega

private theorem numerator_degree {G : Jet} {a u : ℕ} (caps : RowCaps G (graphShape a u)) :
    (numerator G).natDegree ≤ a := by
  rw [show numerator G = -G.coeff 0 from rfl, natDegree_neg]
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  by_contra hn
  have hb := (caps 0 i hn).1
  change i + 0 ≤ a at hb
  omega

theorem regular_cut_count {u₀ deleted} {M : Model u₀ deleted} {Γ T : Finset K}
    (F : Family M Γ) (sub : T ⊆ Γ) (C : CutCover)
    (inside : ∀ z∈T, ∃ Q∈C.curves, OnMark F Q z)
    {G : Jet} {a u d : ℕ} (ha : 2 ≤ a) (hu : 0 < u) (slope : G.natDegree = 1)
    (caps : RowCaps G (graphShape a u))
    (roots : ∀ z∈T, jetAt G (M.label z) (F.scalar z) = 0)
    (good : ∀ z∈T, regular G (M.label z) (F.scalar z))
    (dp : 0 < d) (gap : d < 179730) (deg : ∀ z∈T, (F.scalar z).natDegree ≤ d) :
    (T.card : ℚ) ≤ ((u * C.cost 0 + (a-1) * C.cost 1 : ℕ) : ℚ) *
      MarkedAdaptive.price 262144 d 179730 := by
  have bcap : cap (fun _ => 1) u (numerator G) := by
    intro i
    rw [show numerator G = -G.coeff 0 from rfl, coeff_neg]
    exact Submodule.neg_mem _ (coefficient_cap caps 0 i)
  have possible : 179730 ≤ Fintype.card I := by
    rw [IRSProfile.card_index]
    decide
  have tame : d < p := gap.trans (by decide)
  have numDegree : (numerator G).natDegree ≤ a - 1 + 1 :=
    (numerator_degree caps).trans (by omega)
  have bound := NativeLostCurve.cut_count F sub C inside
    (show 1 ≤ a - 1 by omega) hu dp gap possible tame
    (denominator G) (numerator G) (denominator_degree caps) numDegree (coefficient_cap caps 1)
    bcap deg (fun z hz => graph_law slope (roots z hz)) good
  simpa only [IRSProfile.card_index] using bound

theorem singular_count {u₀ deleted} {M : Model u₀ deleted} {Γ T : Finset K}
    (F : Family M Γ) {G : Jet} {a u : ℕ} (prime : Prime G) (slope : G.natDegree = 1)
    (caps : RowCaps G (graphShape a u)) (small : (2 * a - 1) * u < p)
    (roots : ∀ z∈T, jetAt G (M.label z) (F.scalar z) = 0)
    (bad : ∀ z∈T, ¬ regular G (M.label z) (F.scalar z)) :
    T.card ≤ (2 * a - 1) * ((p + 1) * u) := by
  let H := PhysicalHelperTariff.graphOf G
  let N := PhysicalHelperTariff.realization prime slope
  have prim := PhysicalHelperTariff.primitive prime slope
  have graph : H.graphDegree ≤ a := by
    rw [← HelperWeightCap.native_degree N prim]
    apply (K1_14_2_2_2_1.jetDegree_le G a).mpr
    intro j i nz
    exact (caps j i nz).1
  have char : (2 * H.graphDegree - 1) * u < p := by
    exact (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left _ graph) _)).trans_lt small
  have coeff (j i : ℕ) (z : Fin 2) : ((G.coeff j).coeff i).degreeOf z ≤ u :=
    (((G.coeff j).coeff i).degreeOf_le_totalDegree z).trans (seed_cap caps j i)
  have zeros (z : K) (hz : z∈T) :
      (G.coeff 1).eval₂ (graphEval (M.label z)) (atX (F.scalar z)) = 0 := by
    have hb := not_ne_iff.mp (bad z hz)
    simpa only [regular, denominator, evaluation_eq] using hb
  have other (z : K) (hz : z∈T) :
      (-G.coeff 0).eval₂ (graphEval (M.label z)) (atX (F.scalar z)) = 0 := by
    have law := graph_law slope (roots z hz)
    rw [evaluation_eq, evaluation_eq, zeros z hz, zero_mul] at law
    exact law.symm
  have bound := NativeGraphExceptional.singular_count N prim (fun _ => u) coeff char
    T M.label (label_injective M).injOn (fun z => atX (F.scalar z)) zeros other
  exact bound.trans (by
    have rate : 2 * H.graphDegree - 1 ≤ 2 * a - 1 :=
      Nat.sub_le_sub_right (Nat.mul_le_mul_left _ graph) _
    calc
      _ ≤ (2 * a - 1) * (u + p * u) := Nat.mul_le_mul_right _ rate
      _ = _ := by ring)


end
end Lower6960.Prefix6969Rescue
end Z6969Source0636


section Z6969Source0637
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.Invoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet atX jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient fixedAt ODE)
open K1_14_2_2 (ODECaps RowCaps mass mass_mono weight dot)
open K1_14_3 (seed_count scalar_atX_injective)
open P1_7_4 (Mass massQ dotQ dotQ_scale_add weightedBill bill_bound ODEGuard)
open HighCore82268JointRank (fixed_fee_linear)
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)
open Research6970.Height2313.Lower6960.Prefix6969Rates (fixedFee fixed_count fixed_word endpointDegree)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Research6969
open scoped BigOperators Classical

private abbrev lambda := Band.lambda .near
private abbrev mu := Band.mu .near

private theorem fixedFee_eq (B J : ℕ) : fixedFee B J =
    (P1_7_4_3.mix B J (mu+2*lambda*(B-1 : ℕ))
      (min (mu+2*lambda*(B-1 : ℕ)) (lambda*(2*J-1 : ℕ)))).ceil.toNat+B^2 :=
  Band.fixedFee_eq .near B J

private theorem ceil_up (q : ℚ) : q ≤ (q.ceil.toNat : ℚ) := by
  have hn : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact Rat.le_ceil.trans hn

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ) ≤ q) : a ≤ q.ceil.toNat := by
  exact_mod_cast bound.trans (ceil_up q)

def incidence : ℚ := MarkedAdaptive.price 262144 endpointDegree 179730
def seedRate (u : ℕ) : ℕ := (incidence * u).ceil.toNat + 4
def ordRate (a : ℕ) : ℕ := (incidence * (a - 1 : ℕ) + mu).ceil.toNat + 4

theorem seed_le (u : ℕ) : incidence * u ≤ (seedRate u : ℚ) :=
  (ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4)

theorem ord_le (a : ℕ) : incidence * (a - 1 : ℕ) ≤ (ordRate a : ℚ) := by
  have h : incidence * (a - 1 : ℕ) ≤ incidence * (a - 1 : ℕ) + mu :=
    le_add_of_nonneg_right (by decide +kernel)
  exact h.trans ((ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4))

def rankB (plan : Plan) : ℕ := plan.initialCap 2 + 2
def rankJ (plan : Plan) : ℕ := plan.initialCap 1 + 1
def pivot (plan : Plan) (τ scale : ℚ) : ℚ := min (scale * rankJ plan) (τ * rankB plan)
def rankWeight (plan : Plan) (τ scale : ℚ) : Mass :=
  ![0, 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale,
    4*lambda*rankJ plan*(1-τ) + rankB plan, 0]
def rankRound (plan : Plan) (τ scale : ℚ) : ℚ :=
  rankWeight plan τ scale 1 + 2*rankWeight plan τ scale 2 + 2*lambda*(pivot plan τ scale)^2 + 1

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable (R : Run F Crt G plan)

def rankMarks : Finset K :=
  Γ.filter (fun γ => ∃ J∈R.initial.rankExit, OnMark F J γ)
def seedMarks : Finset K :=
  Γ.filter (fun γ => R.initial.seeds.Covers (M.label γ))
def ordinateMarks : Finset K :=
  Γ.filter (fun γ => atX (F.scalar γ) ∈ R.initial.ordinates)
def singularMarks (G : Jet) : Finset K :=
  Γ.filter (fun γ => ¬ regular G (M.label γ) (F.scalar γ))

theorem seed_count : (seedMarks R).card ≤ (p+1) * plan.initialCap 2 + plan.initialCap 3 := by
  have h := K1_14_3.seed_count (T := seedMarks R) (label_injective M).injOn R.initial.seeds
    (R.initial.seed_degree.trans_lt (plan.initial_small 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ R.initial.seed_degree) R.initial.seed_points)

theorem ordinate_count : (ordinateMarks R).card ≤ plan.initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ => atX (F.scalar γ))
    (fun _ hγ => (mem_filter.mp hγ).2) ?_).trans R.initial.ordinate_card
  intro γ hγ δ hδ same
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (scalar_atX_injective same)

theorem rank_count (hi : M.overhead.toNat ≤ 2313) {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1)
    (small : rankB plan < p) :
    ((rankMarks R).card : ℚ) ≤ dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) +
      rankRound plan τ scale := by
  let S := R.initial.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E, caps, roots⟩ := R.initial.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ plan.initialCap k :=
    (mass_mono (subset_union_left : S ⊆ R.initial.rankExit ∪ R.initial.parents) k).trans
      (R.initial.fits k)
  have hBm : B ≤ mass S 2 + 2 := max_le (by omega) (by omega)
  have hJm : J ≤ mass S 1 + 1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B ≤ rankB plan := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J ≤ rankJ plan := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hJB : J ≤ B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree ≤ B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1, (le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard : ODEGuard B J := ⟨le_max_left _ _, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), hJB, hB.trans_lt small⟩
  have count : (rankMarks R).card ≤ fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ hγ => roots γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
  have lin := fixed_fee_linear lambda mu τ (pivot plan τ scale)
    (by decide +kernel) (by decide +kernel) htau htau' hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤ rankWeight plan τ scale 1 * J +
      rankWeight plan τ scale 2 * B + 2*lambda*(pivot plan τ scale)^2 + 1 := by
    rw [fixedFee_eq]
    exact lin
  have pmax : pivot plan τ scale ≤ τ * rankB plan := min_le_right _ _
  have hlambda : (0 : ℚ) ≤ 4 * lambda := by decide +kernel
  have hmu : (0 : ℚ) ≤ mu := by decide +kernel
  have cj : 0 ≤ rankWeight plan τ scale 1 := by
    change 0 ≤ 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale
    have key := mul_le_mul_of_nonneg_left pmax hlambda
    linarith only [hmu, show 4*lambda*pivot plan τ scale ≤ 4*lambda*rankB plan*τ by
      calc _ ≤ _ := key
           _ = _ := by ring]
  have cB : 0 ≤ rankWeight plan τ scale 2 := by
    change 0 ≤ 4*lambda*rankJ plan*(1-τ) + rankB plan
    exact add_nonneg (mul_nonneg (mul_nonneg hlambda (Nat.cast_nonneg _)) (sub_nonneg.mpr htau'))
      (Nat.cast_nonneg _)
  have hJq : (J : ℚ) ≤ (mass S 1 : ℚ) + 1 := by exact_mod_cast hJm
  have hBq : (B : ℚ) ≤ (mass S 2 : ℚ) + 2 := by exact_mod_cast hBm
  have advanceJ := mul_le_mul_of_nonneg_left hJq cj
  have advanceB := mul_le_mul_of_nonneg_left hBq cB
  have expand : dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) =
      rankWeight plan τ scale 1 * (mass S 1 : ℚ) + rankWeight plan τ scale 2 * (mass S 2 : ℚ) := by
    simp [dotQ, rankWeight, massQ, Fin.sum_univ_succ, S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [expand, rankRound]
  linarith only [advanceJ, advanceB]

variable {R} (B : Book R)

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k => weight (B.shape i) fee k
def seedLimit : ℚ := weightedBill B.steps (cutWeight B 0) B.capacity
def pointLimit : ℚ := weightedBill B.steps (cutWeight B 2) (fun _ k => plan.initialCap k)

theorem costQ {i : ℕ} (hi : i < B.steps) (fee : Fin 3) :
    ((B.cut i).cost fee : ℚ) ≤ dotQ (cutWeight B fee i) (massQ (B.lost i)) := by
  exact (by simpa only [cutWeight,dotQ,dot,massQ,Book.lost,Nat.cast_sum,Nat.cast_mul] using
    ((Nat.cast_le (α := ℚ)).mpr (B.cut_cost i hi fee)))

theorem seed_bill : (∑ i∈range B.steps, ((B.cut i).cost 0 : ℚ)) ≤ seedLimit B :=
  (sum_le_sum fun _ hi => costQ B (mem_range.mp hi) 0).trans
    (bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.bound i hi))

def pointMarks : Finset K := (range B.steps).biUnion (fun i => (B.cut i).direct)

theorem point_bill : ((pointMarks B).card : ℚ) ≤ pointLimit B := by
  calc
    _ ≤ ∑ i∈range B.steps, ((B.cut i).cost 2 : ℚ) := by
      exact_mod_cast (show (pointMarks B).card ≤ ∑ i∈range B.steps,(B.cut i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range B.steps, dotQ (cutWeight B 2 i) (massQ (B.lost i)) :=
      sum_le_sum fun i hi => costQ B (mem_range.mp hi) 2
    _ ≤ _ := bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.initial_bound i hi)

def regularCutMarks (i : ℕ) : Finset K :=
  Γ.filter (fun γ => regular G (M.label γ) (F.scalar γ) ∧
    ∃ Q∈(B.cut i).curves, OnMark F Q γ)

def lossWeight (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * cutWeight B 0 i k + (ordRate a : ℚ) * cutWeight B 1 i k

theorem curve_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (hiM : M.overhead.toNat ≤ 2313)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {i : ℕ} (hi : i < B.steps) :
    ((regularCutMarks B i).card : ℚ) ≤ dotQ (lossWeight B a u i) (massQ (B.lost i)) := by
  let T := regularCutMarks B i
  have sub : T ⊆ Γ := filter_subset _ _
  have deg := fixed_word F hiM sub
  have cut := regular_cut_count F sub (B.cut i)
    (fun γ hγ => (mem_filter.mp hγ).2.2) ha hu slope caps
    (fun γ hγ => roots γ (sub hγ)) (fun γ hγ => (mem_filter.mp hγ).2.1)
    (by decide : 0 < endpointDegree) (by decide) deg.degree
  have shape : (T.card : ℚ) ≤ incidence * (u : ℚ) * (B.cut i).cost 0 +
      incidence * (a - 1 : ℕ) * (B.cut i).cost 1 := by
    push_cast at cut
    unfold incidence
    linarith only [cut]
  calc
    _ ≤ (seedRate u : ℚ) * (B.cut i).cost 0 + (ordRate a : ℚ) * (B.cut i).cost 1 :=
      shape.trans (add_le_add (mul_le_mul_of_nonneg_right (seed_le _) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (ord_le _) (Nat.cast_nonneg _)))
    _ ≤ (seedRate u : ℚ) * dotQ (cutWeight B 0 i) (massQ (B.lost i)) +
        (ordRate a : ℚ) * dotQ (cutWeight B 1 i) (massQ (B.lost i)) :=
      add_le_add (mul_le_mul_of_nonneg_left (costQ B hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (costQ B hi 1) (Nat.cast_nonneg _))
    _ = _ := by rw [dotQ_scale_add]; rfl

def lossMarks : Finset K := rankMarks R ∪ (range B.steps).biUnion (regularCutMarks B)
def paid : Finset K :=
  ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R)) ∪ singularMarks (M := M) (F := F) G

def eventCut (shape : ℕ → K1_14.Shape) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (shape i) fee k

def eventLossWeight (shape : ℕ → K1_14.Shape) (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * eventCut shape 0 i k + (ordRate a : ℚ) * eventCut shape 1 i k

def eventRunning (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (a u : ℕ) (τ scale : ℚ) : Mass :=
  P1_7_4.running (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u)) (steps + 1)

def eventLossLimit (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℚ :=
  weightedBill (steps + 1) (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u))
    (beforeCuts (fun k => plan.initialCap k) capacity) +
    weightedBill steps (eventCut shape 0) capacity + rankRound plan τ scale

def eventFee (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℕ :=
  (eventLossLimit plan steps shape capacity a u τ scale).ceil.toNat +
    (weightedBill steps (eventCut shape 2) (fun _ k => plan.initialCap k)).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 +
    (2*a-1)*((p+1)*u)

def lossLimit (a u : ℕ) (τ scale : ℚ) : ℚ :=
  eventLossLimit plan B.steps B.shape B.capacity a u τ scale

def fee (a u : ℕ) (τ scale : ℚ) : ℕ :=
  eventFee plan B.steps B.shape B.capacity a u τ scale


theorem eventRunning_eq (a u : ℕ) (τ scale : ℚ) :
    P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) =
      eventRunning plan B.steps B.shape a u τ scale := rfl

def charge (credit : Fin 4 → ℕ) : ℕ := ∑ k, credit k * mass B.final k

theorem paid_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (small : (2*a-1)*u < p) (hiM : M.overhead.toNat ≤ 2313)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ) (retained : ∀ k, (credit k : ℚ) ≤
      P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) k) :
    (paid B).card + charge B credit ≤ fee B a u τ scale := by
  have cuts := sum_le_sum (fun i (mem : i ∈ range B.steps) =>
    curve_count B ha hu slope caps hiM roots (mem_range.mp mem))
  have lossRail : ((lossMarks B).card : ℚ) ≤ ((rankMarks R).card : ℚ) +
      ∑ i∈range B.steps, ((regularCutMarks B i).card : ℚ) := by
    exact_mod_cast (show (lossMarks B).card ≤ (rankMarks R).card +
      ∑ i∈range B.steps, (regularCutMarks B i).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have subtotal := lossRail.trans (add_le_add (rank_count R hiM (scale := scale) htau htau' rankSmall) cuts)
  have joint := B.joint_bill (rankWeight plan τ scale) (lossWeight B a u)
  have creditBill : (charge B credit : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
        (B.steps+1)) (massQ B.final) := by
    unfold charge dotQ massQ
    push_cast
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (retained k) (Nat.cast_nonneg _)
  have seedNonneg : 0 ≤ seedLimit B := le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (seed_bill B)
  have loss : (lossMarks B).card + charge B credit ≤ (lossLimit B a u τ scale).ceil.toNat := by
    apply card_round
    push_cast
    change _ ≤ weightedBill (B.steps + 1)
      (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
      (beforeCuts (fun k => plan.initialCap k) B.capacity) + seedLimit B + rankRound plan τ scale
    linarith only [subtotal, joint, creditBill, seedNonneg]
  have point := card_round (point_bill B)
  have singular : (singularMarks (M:=M) (F:=F) G).card ≤ (2*a-1)*((p+1)*u) :=
    singular_count F prime slope caps small (fun γ hγ => roots γ (mem_filter.mp hγ).1)
      (fun _ hγ => (mem_filter.mp hγ).2)
  have union₀ := card_union_le ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R))
    (singularMarks (M:=M) (F:=F) G)
  have union₁ := card_union_le (lossMarks B ∪ pointMarks B) (seedMarks R ∪ ordinateMarks R)
  have union₂ := card_union_le (lossMarks B) (pointMarks B)
  have union₃ := card_union_le (seedMarks R) (ordinateMarks R)
  have seed := seed_count R
  have ord := ordinate_count R
  unfold paid
  change _ ≤ (lossLimit B a u τ scale).ceil.toNat + (pointLimit B).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 + (2*a-1)*((p+1)*u)
  omega

/-- Every graph mark is paid by this actual book or lies on a surviving parent. -/
theorem paid_cover {γ : K} (mem : γ ∈ Γ) (root : jetAt G (M.label γ) (F.scalar γ) = 0) :
    γ ∈ paid B ∨ ∃ J∈B.final, OnMark F J γ := by
  by_cases bad : ¬ regular G (M.label γ) (F.scalar γ)
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem, bad⟩))
  have good := not_not.mp bad
  rcases B.cut_marks mem root with seed | ord | rank | lost | final
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,rank⟩)))))
  · obtain ⟨i, hi, hit | hit⟩ := lost
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi,hit⟩))))
    · have mark : γ ∈ (range B.steps).biUnion (regularCutMarks B) := mem_biUnion.mpr ⟨i,mem_range.mpr hi,
        mem_filter.mpr ⟨mem,good,hit⟩⟩
      exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
  · exact Or.inr final


end
end Lower6960.Prefix6969Rescue.Invoice
end Z6969Source0637


section Z6969Source0638
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.Invoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (RowCaps)
open Far6969RescueGeometry (Model Family OnMark)

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

structure Event (R : Run F Crt G plan) (survivors : Finset (Ideal Ambient))
    (feeBound : ℕ) (credit : Fin 4 → ℕ) where
  book : Book R
  final : book.final = survivors
  count : (paid book).card + charge book credit ≤ feeBound
  cover : ∀ γ∈Γ, γ ∈ paid book ∨ ∃ J∈survivors, OnMark F J γ

variable (R : Run F Crt G plan) {a u : ℕ}
variable (ha : 2 ≤ a) (hu : 0 < u)
variable (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
variable (small : (2*a-1)*u < p) (hi : M.overhead.toNat ≤ 2313)
variable (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
variable {τ scale : ℚ} (t0 : 0 ≤ τ) (t1 : τ ≤ 1) (rankSmall : rankB plan < p)
variable {bound : ℕ} (credit : Fin 4 → ℕ)

include ha hu prime slope caps small hi roots t0 t1 rankSmall

private theorem event_of_book (B : Book R) {survivors : Finset (Ideal Ambient)}
    (final : B.final = survivors)
    (checkFee : eventFee plan B.steps B.shape B.capacity a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan B.steps B.shape a u τ scale k) :
    Nonempty (Event R survivors bound credit) := by
  refine ⟨B, final, ?_, ?_⟩
  · exact (paid_count B ha hu prime slope caps small hi roots t0 t1 rankSmall credit
      (fun k => by rw [eventRunning_eq B a u τ scale]; exact checkCredit k)).trans checkFee
  · intro γ mem
    rw [← final]
    exact paid_cover B mem (roots γ mem)

/-- A certificate at a real early stop prices precisely the rows preceding that stop. -/
theorem early_event {stop : ℕ} (fits : stop < plan.count)
    (checkFee : eventFee plan stop plan.cutShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan stop plan.cutShape a u τ scale k) :
    Nonempty (Event R (R.live stop) bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.early R stop fits
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]

/-- The normal event adds the last cut from the production terminal bank. -/
theorem normal_event
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (checkFee : eventFee plan plan.count plan.normalShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤
      eventRunning plan plan.count plan.normalShape a u τ scale k) :
    Nonempty (Event R R.terminal bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.normal R noPole residues
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]


end
end Lower6960.Prefix6969Rescue.Invoice
end Z6969Source0638


section Z6969Source0639
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.MiddleInvoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet atX jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (Ambient fixedAt ODE)
open K1_14_2_2 (ODECaps RowCaps mass mass_mono weight dot)
open K1_14_3 (seed_count scalar_atX_injective)
open P1_7_4 (Mass massQ dotQ dotQ_scale_add weightedBill bill_bound ODEGuard)
open HighCore82268JointRank (fixed_fee_linear)
open Prefix6969Middle (lambda mu fixedFee_eq)
open Prefix6969MiddleRates (fixedFee fixed_count fixed_word endpointDegree)
open Far6969RescueGeometry (Model Family OnMark label_injective beforeCuts)
open Research6969
open scoped BigOperators Classical

private theorem ceil_up (q : ℚ) : q ≤ (q.ceil.toNat : ℚ) := by
  have hn : (q.ceil : ℚ) ≤ (q.ceil.toNat : ℚ) := by exact_mod_cast Int.self_le_toNat q.ceil
  exact Rat.le_ceil.trans hn

private theorem card_round {a : ℕ} {q : ℚ} (bound : (a : ℚ) ≤ q) : a ≤ q.ceil.toNat := by
  exact_mod_cast bound.trans (ceil_up q)

def incidence : ℚ := MarkedAdaptive.price 262144 endpointDegree 179730
def seedRate (u : ℕ) : ℕ := (incidence * u).ceil.toNat + 4
def ordRate (a : ℕ) : ℕ := (incidence * (a - 1 : ℕ) + mu).ceil.toNat + 4

theorem seed_le (u : ℕ) : incidence * u ≤ (seedRate u : ℚ) :=
  (ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4)

theorem ord_le (a : ℕ) : incidence * (a - 1 : ℕ) ≤ (ordRate a : ℚ) := by
  have h : incidence * (a - 1 : ℕ) ≤ incidence * (a - 1 : ℕ) + mu :=
    le_add_of_nonneg_right (by decide +kernel)
  exact h.trans ((ceil_up _).trans (by exact_mod_cast Nat.le_add_right _ 4))

def rankB (plan : Plan) : ℕ := plan.initialCap 2 + 2
def rankJ (plan : Plan) : ℕ := plan.initialCap 1 + 1
def pivot (plan : Plan) (τ scale : ℚ) : ℚ := min (scale * rankJ plan) (τ * rankB plan)
def rankWeight (plan : Plan) (τ scale : ℚ) : Mass :=
  ![0, 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale,
    4*lambda*rankJ plan*(1-τ) + rankB plan, 0]
def rankRound (plan : Plan) (τ scale : ℚ) : ℚ :=
  rankWeight plan τ scale 1 + 2*rankWeight plan τ scale 2 + 2*lambda*(pivot plan τ scale)^2 + 1

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable (R : Run F Crt G plan)

def rankMarks : Finset K :=
  Γ.filter (fun γ => ∃ J∈R.initial.rankExit, OnMark F J γ)
def seedMarks : Finset K :=
  Γ.filter (fun γ => R.initial.seeds.Covers (M.label γ))
def ordinateMarks : Finset K :=
  Γ.filter (fun γ => atX (F.scalar γ) ∈ R.initial.ordinates)
def singularMarks (G : Jet) : Finset K :=
  Γ.filter (fun γ => ¬ regular G (M.label γ) (F.scalar γ))

theorem seed_count : (seedMarks R).card ≤ (p+1) * plan.initialCap 2 + plan.initialCap 3 := by
  have h := K1_14_3.seed_count (T := seedMarks R) (label_injective M).injOn R.initial.seeds
    (R.initial.seed_degree.trans_lt (plan.initial_small 2)) (fun _ hγ => (mem_filter.mp hγ).2)
  exact h.trans (Nat.add_le_add (Nat.mul_le_mul_left _ R.initial.seed_degree) R.initial.seed_points)

theorem ordinate_count : (ordinateMarks R).card ≤ plan.initialCap 0 := by
  apply (card_le_card_of_injOn (fun γ => atX (F.scalar γ))
    (fun _ hγ => (mem_filter.mp hγ).2) ?_).trans R.initial.ordinate_card
  intro γ hγ δ hδ same
  exact F.distinct (mem_filter.mp hγ).1 (mem_filter.mp hδ).1 (scalar_atX_injective same)

theorem rank_count (hi : M.overhead.toNat ≤ 2557) {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1)
    (small : rankB plan < p) :
    ((rankMarks R).card : ℚ) ≤ dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) +
      rankRound plan τ scale := by
  let S := R.initial.rankExit
  let B := max 2 (mass S 2)
  let J := max 1 (min (mass S 1) B)
  obtain ⟨E, caps, roots⟩ := R.initial.rank_ode
  have mass_cap (k : Fin 4) : mass S k ≤ plan.initialCap k :=
    (mass_mono (subset_union_left : S ⊆ R.initial.rankExit ∪ R.initial.parents) k).trans
      (R.initial.fits k)
  have hBm : B ≤ mass S 2 + 2 := max_le (by omega) (by omega)
  have hJm : J ≤ mass S 1 + 1 := max_le (by omega) ((min_le_left _ _).trans (by omega))
  have hB : B ≤ rankB plan := hBm.trans (Nat.add_le_add_right (mass_cap 2) 2)
  have hJ : J ≤ rankJ plan := hJm.trans (Nat.add_le_add_right (mass_cap 1) 1)
  have hJB : J ≤ B := max_le (by omega) (min_le_right _ _)
  have degree : E.natDegree ≤ B := by
    have top : E.coeff E.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr caps.1
    have hn : (E.coeff E.natDegree).coeff (E.coeff E.natDegree).natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr top
    exact (Nat.le_add_left _ _).trans ((caps.2.2 _ _ hn).trans (le_max_right _ _))
  have ocaps : ODECaps E B J := ⟨caps.1, (le_min caps.2.1 degree).trans (le_max_right _ _),
    fun j i hz => (caps.2.2 j i hz).trans (le_max_right _ _)⟩
  have guard : ODEGuard B J := ⟨le_max_left _ _, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), hJB, hB.trans_lt small⟩
  have count : (rankMarks R).card ≤ fixedFee B J :=
    fixed_count F hi guard E ocaps (filter_subset _ _)
      (fun γ hγ => roots γ (mem_filter.mp hγ).1 (mem_filter.mp hγ).2)
  have lin := fixed_fee_linear lambda mu τ (pivot plan τ scale)
    (by decide +kernel) (by decide +kernel) htau htau' hJB hB hJ
  have fee : (fixedFee B J : ℚ) ≤ rankWeight plan τ scale 1 * J +
      rankWeight plan τ scale 2 * B + 2*lambda*(pivot plan τ scale)^2 + 1 := by
    rw [fixedFee_eq]
    exact lin
  have pmax : pivot plan τ scale ≤ τ * rankB plan := min_le_right _ _
  have hlambda : (0 : ℚ) ≤ 4 * lambda := by decide +kernel
  have hmu : (0 : ℚ) ≤ mu := by decide +kernel
  have cj : 0 ≤ rankWeight plan τ scale 1 := by
    change 0 ≤ 4*lambda*rankB plan*τ + mu - 4*lambda*pivot plan τ scale
    have key := mul_le_mul_of_nonneg_left pmax hlambda
    linarith only [hmu, show 4*lambda*pivot plan τ scale ≤ 4*lambda*rankB plan*τ by
      calc _ ≤ _ := key
           _ = _ := by ring]
  have cB : 0 ≤ rankWeight plan τ scale 2 := by
    change 0 ≤ 4*lambda*rankJ plan*(1-τ) + rankB plan
    exact add_nonneg (mul_nonneg (mul_nonneg hlambda (Nat.cast_nonneg _)) (sub_nonneg.mpr htau'))
      (Nat.cast_nonneg _)
  have hJq : (J : ℚ) ≤ (mass S 1 : ℚ) + 1 := by exact_mod_cast hJm
  have hBq : (B : ℚ) ≤ (mass S 2 : ℚ) + 2 := by exact_mod_cast hBm
  have advanceJ := mul_le_mul_of_nonneg_left hJq cj
  have advanceB := mul_le_mul_of_nonneg_left hBq cB
  have expand : dotQ (rankWeight plan τ scale) (massQ R.initial.rankExit) =
      rankWeight plan τ scale 1 * (mass S 1 : ℚ) + rankWeight plan τ scale 2 * (mass S 2 : ℚ) := by
    simp [dotQ, rankWeight, massQ, Fin.sum_univ_succ, S]
  refine (Nat.cast_le.mpr count).trans (fee.trans ?_)
  rw [expand, rankRound]
  linarith only [advanceJ, advanceB]

variable {R} (B : Book R)

def cutWeight (fee : Fin 3) (i : ℕ) : Mass := fun k => weight (B.shape i) fee k
def seedLimit : ℚ := weightedBill B.steps (cutWeight B 0) B.capacity
def pointLimit : ℚ := weightedBill B.steps (cutWeight B 2) (fun _ k => plan.initialCap k)

theorem costQ {i : ℕ} (hi : i < B.steps) (fee : Fin 3) :
    ((B.cut i).cost fee : ℚ) ≤ dotQ (cutWeight B fee i) (massQ (B.lost i)) := by
  exact (by simpa only [cutWeight,dotQ,dot,massQ,Book.lost,Nat.cast_sum,Nat.cast_mul] using
    ((Nat.cast_le (α := ℚ)).mpr (B.cut_cost i hi fee)))

theorem seed_bill : (∑ i∈range B.steps, ((B.cut i).cost 0 : ℚ)) ≤ seedLimit B :=
  (sum_le_sum fun _ hi => costQ B (mem_range.mp hi) 0).trans
    (bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.bound i hi))

def pointMarks : Finset K := (range B.steps).biUnion (fun i => (B.cut i).direct)

theorem point_bill : ((pointMarks B).card : ℚ) ≤ pointLimit B := by
  calc
    _ ≤ ∑ i∈range B.steps, ((B.cut i).cost 2 : ℚ) := by
      exact_mod_cast (show (pointMarks B).card ≤ ∑ i∈range B.steps,(B.cut i).direct.card from card_biUnion_le)
    _ ≤ ∑ i∈range B.steps, dotQ (cutWeight B 2 i) (massQ (B.lost i)) :=
      sum_le_sum fun i hi => costQ B (mem_range.mp hi) 2
    _ ≤ _ := bill_bound B.steps _ _ B.live B.lost (fun i hi => B.next i hi)
      (fun _ _ => subset_rfl) (fun i hi => B.initial_bound i hi)

def regularCutMarks (i : ℕ) : Finset K :=
  Γ.filter (fun γ => regular G (M.label γ) (F.scalar γ) ∧
    ∃ Q∈(B.cut i).curves, OnMark F Q γ)

def lossWeight (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * cutWeight B 0 i k + (ordRate a : ℚ) * cutWeight B 1 i k

theorem curve_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (hiM : M.overhead.toNat ≤ 2557)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {i : ℕ} (hi : i < B.steps) :
    ((regularCutMarks B i).card : ℚ) ≤ dotQ (lossWeight B a u i) (massQ (B.lost i)) := by
  let T := regularCutMarks B i
  have sub : T ⊆ Γ := filter_subset _ _
  have deg := fixed_word F hiM sub
  have cut := regular_cut_count F sub (B.cut i)
    (fun γ hγ => (mem_filter.mp hγ).2.2) ha hu slope caps
    (fun γ hγ => roots γ (sub hγ)) (fun γ hγ => (mem_filter.mp hγ).2.1)
    (by decide : 0 < endpointDegree) (by decide) deg.degree
  have shape : (T.card : ℚ) ≤ incidence * (u : ℚ) * (B.cut i).cost 0 +
      incidence * (a - 1 : ℕ) * (B.cut i).cost 1 := by
    push_cast at cut
    unfold incidence
    linarith only [cut]
  calc
    _ ≤ (seedRate u : ℚ) * (B.cut i).cost 0 + (ordRate a : ℚ) * (B.cut i).cost 1 :=
      shape.trans (add_le_add (mul_le_mul_of_nonneg_right (seed_le _) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_right (ord_le _) (Nat.cast_nonneg _)))
    _ ≤ (seedRate u : ℚ) * dotQ (cutWeight B 0 i) (massQ (B.lost i)) +
        (ordRate a : ℚ) * dotQ (cutWeight B 1 i) (massQ (B.lost i)) :=
      add_le_add (mul_le_mul_of_nonneg_left (costQ B hi 0) (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left (costQ B hi 1) (Nat.cast_nonneg _))
    _ = _ := by rw [dotQ_scale_add]; rfl

def lossMarks : Finset K := rankMarks R ∪ (range B.steps).biUnion (regularCutMarks B)
def paid : Finset K :=
  ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R)) ∪ singularMarks (M := M) (F := F) G

def eventCut (shape : ℕ → K1_14.Shape) (fee : Fin 3) (i : ℕ) : Mass :=
  fun k => weight (shape i) fee k

def eventLossWeight (shape : ℕ → K1_14.Shape) (a u : ℕ) (i : ℕ) : Mass :=
  fun k => (seedRate u : ℚ) * eventCut shape 0 i k + (ordRate a : ℚ) * eventCut shape 1 i k

def eventRunning (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (a u : ℕ) (τ scale : ℚ) : Mass :=
  P1_7_4.running (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u)) (steps + 1)

def eventLossLimit (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℚ :=
  weightedBill (steps + 1) (beforeCuts (rankWeight plan τ scale) (eventLossWeight shape a u))
    (beforeCuts (fun k => plan.initialCap k) capacity) +
    weightedBill steps (eventCut shape 0) capacity + rankRound plan τ scale

def eventFee (plan : Plan) (steps : ℕ) (shape : ℕ → K1_14.Shape)
    (capacity : ℕ → Mass) (a u : ℕ) (τ scale : ℚ) : ℕ :=
  (eventLossLimit plan steps shape capacity a u τ scale).ceil.toNat +
    (weightedBill steps (eventCut shape 2) (fun _ k => plan.initialCap k)).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 +
    (2*a-1)*((p+1)*u)

def lossLimit (a u : ℕ) (τ scale : ℚ) : ℚ :=
  eventLossLimit plan B.steps B.shape B.capacity a u τ scale

def fee (a u : ℕ) (τ scale : ℚ) : ℕ :=
  eventFee plan B.steps B.shape B.capacity a u τ scale


theorem eventRunning_eq (a u : ℕ) (τ scale : ℚ) :
    P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) =
      eventRunning plan B.steps B.shape a u τ scale := rfl

def charge (credit : Fin 4 → ℕ) : ℕ := ∑ k, credit k * mass B.final k

theorem paid_count {a u : ℕ} (ha : 2 ≤ a) (hu : 0 < u)
    (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
    (small : (2*a-1)*u < p) (hiM : M.overhead.toNat ≤ 2557)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
    {τ scale : ℚ} (htau : 0 ≤ τ) (htau' : τ ≤ 1) (rankSmall : rankB plan < p)
    (credit : Fin 4 → ℕ) (retained : ∀ k, (credit k : ℚ) ≤
      P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u)) (B.steps+1) k) :
    (paid B).card + charge B credit ≤ fee B a u τ scale := by
  have cuts := sum_le_sum (fun i (mem : i ∈ range B.steps) =>
    curve_count B ha hu slope caps hiM roots (mem_range.mp mem))
  have lossRail : ((lossMarks B).card : ℚ) ≤ ((rankMarks R).card : ℚ) +
      ∑ i∈range B.steps, ((regularCutMarks B i).card : ℚ) := by
    exact_mod_cast (show (lossMarks B).card ≤ (rankMarks R).card +
      ∑ i∈range B.steps, (regularCutMarks B i).card from
        (card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have subtotal := lossRail.trans (add_le_add (rank_count R hiM (scale := scale) htau htau' rankSmall) cuts)
  have joint := B.joint_bill (rankWeight plan τ scale) (lossWeight B a u)
  have creditBill : (charge B credit : ℚ) ≤
      dotQ (P1_7_4.running (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
        (B.steps+1)) (massQ B.final) := by
    unfold charge dotQ massQ
    push_cast
    exact Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_right (retained k) (Nat.cast_nonneg _)
  have seedNonneg : 0 ≤ seedLimit B := le_trans (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (seed_bill B)
  have loss : (lossMarks B).card + charge B credit ≤ (lossLimit B a u τ scale).ceil.toNat := by
    apply card_round
    push_cast
    change _ ≤ weightedBill (B.steps + 1)
      (beforeCuts (rankWeight plan τ scale) (lossWeight B a u))
      (beforeCuts (fun k => plan.initialCap k) B.capacity) + seedLimit B + rankRound plan τ scale
    linarith only [subtotal, joint, creditBill, seedNonneg]
  have point := card_round (point_bill B)
  have singular : (singularMarks (M:=M) (F:=F) G).card ≤ (2*a-1)*((p+1)*u) :=
    singular_count F prime slope caps small (fun γ hγ => roots γ (mem_filter.mp hγ).1)
      (fun _ hγ => (mem_filter.mp hγ).2)
  have union₀ := card_union_le ((lossMarks B ∪ pointMarks B) ∪ (seedMarks R ∪ ordinateMarks R))
    (singularMarks (M:=M) (F:=F) G)
  have union₁ := card_union_le (lossMarks B ∪ pointMarks B) (seedMarks R ∪ ordinateMarks R)
  have union₂ := card_union_le (lossMarks B) (pointMarks B)
  have union₃ := card_union_le (seedMarks R) (ordinateMarks R)
  have seed := seed_count R
  have ord := ordinate_count R
  unfold paid
  change _ ≤ (lossLimit B a u τ scale).ceil.toNat + (pointLimit B).ceil.toNat +
    ((p+1)*plan.initialCap 2 + plan.initialCap 3) + plan.initialCap 0 + (2*a-1)*((p+1)*u)
  omega

/-- Every graph mark is paid by this actual book or lies on a surviving parent. -/
theorem paid_cover {γ : K} (mem : γ ∈ Γ) (root : jetAt G (M.label γ) (F.scalar γ) = 0) :
    γ ∈ paid B ∨ ∃ J∈B.final, OnMark F J γ := by
  by_cases bad : ¬ regular G (M.label γ) (F.scalar γ)
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem, bad⟩))
  have good := not_not.mp bad
  rcases B.cut_marks mem root with seed | ord | rank | lost | final
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨mem,seed⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨mem,ord⟩))))
  · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem,rank⟩)))))
  · obtain ⟨i, hi, hit | hit⟩ := lost
    · exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_range.mpr hi,hit⟩))))
    · have mark : γ ∈ (range B.steps).biUnion (regularCutMarks B) := mem_biUnion.mpr ⟨i,mem_range.mpr hi,
        mem_filter.mpr ⟨mem,good,hit⟩⟩
      exact Or.inl (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_union_right _ mark))))
  · exact Or.inr final


end
end Lower6960.Prefix6969Rescue.MiddleInvoice
end Z6969Source0639


section Z6969Source0640
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.MiddleInvoice
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient)
open K1_14_2_2 (RowCaps)
open Far6969RescueGeometry (Model Family OnMark)

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}

structure Event (R : Run F Crt G plan) (survivors : Finset (Ideal Ambient))
    (feeBound : ℕ) (credit : Fin 4 → ℕ) where
  book : Book R
  final : book.final = survivors
  count : (paid book).card + charge book credit ≤ feeBound
  cover : ∀ γ∈Γ, γ ∈ paid book ∨ ∃ J∈survivors, OnMark F J γ

variable (R : Run F Crt G plan) {a u : ℕ}
variable (ha : 2 ≤ a) (hu : 0 < u)
variable (prime : Prime G) (slope : G.natDegree = 1) (caps : RowCaps G (graphShape a u))
variable (small : (2*a-1)*u < p) (hi : M.overhead.toNat ≤ 2557)
variable (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0)
variable {τ scale : ℚ} (t0 : 0 ≤ τ) (t1 : τ ≤ 1) (rankSmall : rankB plan < p)
variable {bound : ℕ} (credit : Fin 4 → ℕ)

include ha hu prime slope caps small hi roots t0 t1 rankSmall

private theorem event_of_book (B : Book R) {survivors : Finset (Ideal Ambient)}
    (final : B.final = survivors)
    (checkFee : eventFee plan B.steps B.shape B.capacity a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan B.steps B.shape a u τ scale k) :
    Nonempty (Event R survivors bound credit) := by
  refine ⟨B, final, ?_, ?_⟩
  · exact (paid_count B ha hu prime slope caps small hi roots t0 t1 rankSmall credit
      (fun k => by rw [eventRunning_eq B a u τ scale]; exact checkCredit k)).trans checkFee
  · intro γ mem
    rw [← final]
    exact paid_cover B mem (roots γ mem)

/-- A certificate at a real early stop prices precisely the rows preceding that stop. -/
theorem early_event {stop : ℕ} (fits : stop < plan.count)
    (checkFee : eventFee plan stop plan.cutShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤ eventRunning plan stop plan.cutShape a u τ scale k) :
    Nonempty (Event R (R.live stop) bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.early R stop fits
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]

/-- The normal event adds the last cut from the production terminal bank. -/
theorem normal_event
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (checkFee : eventFee plan plan.count plan.normalShape plan.history a u τ scale ≤ bound)
    (checkCredit : ∀ k, (credit k : ℚ) ≤
      eventRunning plan plan.count plan.normalShape a u τ scale k) :
    Nonempty (Event R R.terminal bound credit) := by
  obtain ⟨B, steps, final, shape, capacity⟩ := Book.normal R noPole residues
  apply event_of_book R ha hu prime slope caps small hi roots t0 t1 rankSmall credit B final
  · rwa [steps, shape, capacity]
  · rwa [steps, shape]


end
end Lower6960.Prefix6969Rescue.MiddleInvoice
end Z6969Source0640


section Z6969Source0641
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 2000000

namespace Lower6960.Prefix6969Rescue.Invoice
noncomputable section

open Finset
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_2 (toJet)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ massQ_mono)
open P0_10R.Bridge (surfaceOf parent_of_dual)
open Far6969RescueGeometry (Model Family OnMark OnSurface word)
open scoped Classical

variable {u₀ deleted} {M : Model u₀ deleted} {Γ} {F : Family M Γ}
variable {D : PoleData M.overhead.toNat} {Crt : CRTLift D} {G : Jet} {plan : Plan}
variable {R : Run F Crt G plan}

theorem Book.final_initial (B : Book R) : B.final ⊆ R.live 0 := by
  have sub (n : ℕ) (hn : n ≤ B.steps) : B.live n ⊆ B.live 0 := by
    induction n with
    | zero => exact subset_rfl
    | succ n ih => exact (B.next n (by omega)).trans (ih (by omega))
  rw [R.live_start, ← B.start]
  exact sub B.steps le_rfl

theorem Book.paid_or_regular {γ : K1.K} (B : Book R) (mem : γ∈Γ)
    (root : jetAt G (M.label γ) (F.scalar γ) = 0) :
    γ∈paid B ∨ regular G (M.label γ) (F.scalar γ) ∧
      ∃ J∈B.final, OnMark F J γ := by
  by_cases good : regular G (M.label γ) (F.scalar γ)
  · rcases paid_cover B mem root with hit | survivor
    · exact Or.inl hit
    · exact Or.inr ⟨good, survivor⟩
  · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem, good⟩))

/-- Both terminal modes yield genuine parent surfaces for all unpaid graph marks. -/
theorem Book.surfaces (B : Book R) :
    ∃ S : Finset Surface,
      (∀ q∈S, Parent q ∧ ∃ J∈B.final, q.asIdeal = J.comap toJet) ∧
      ∀ γ∈Γ, (∃ J∈B.final, OnMark F J γ) → ∃ q∈S, OnSurface F q γ := by
  let getGeom (J : B.final) := R.parent_geom (Book.final_initial B J.property)
  let surface (J : B.final) := surfaceOf J.val (getGeom J).1.prime
  let S := B.final.attach.image surface
  refine ⟨S, ?_, ?_⟩
  · intro q hq
    obtain ⟨J, _, rfl⟩ := mem_image.mp hq
    have hJ := getGeom J
    exact ⟨parent_of_dual hJ.1 hJ.2.2.1 hJ.2.1, J.val, J.property, rfl⟩
  · rintro γ _ ⟨J, hJ, on⟩
    let q : B.final := ⟨J, hJ⟩
    refine ⟨surface q, mem_image.mpr ⟨q, mem_attach _ _, rfl⟩, ?_⟩
    intro P mem
    rw [← K1_14_2.eval_toJet]
    exact RingHom.mem_ker.mp (on mem)

theorem Book.terminal_parent (B : Book R) (final : B.final = R.terminal)
    {q : Surface} {J : Ideal K1_14_2.Ambient} (mem : J∈B.final)
    (origin : q.asIdeal = J.comap toJet) :
    Prefix6969Wide.SurfacePass Crt (word M) q ∧ G∈q.asIdeal := by
  have pass := (mem_filter.mp (final ▸ mem)).2
  have zero := (R.parent_geom (Book.final_initial B mem)).2.2.2.1
  refine ⟨?_, ?_⟩
  · intro s fit P inside
    rw [origin]
    exact pass s fit P inside
  · rw [origin]
    exact zero

theorem Run.mass_terminal (R : Run F Crt G plan) (k : Fin 4) :
    massQ R.terminal k ≤ plan.history (plan.count - 1) k := by
  have fits : plan.count - 1 < plan.count := by have := plan.positive; omega
  exact (massQ_mono (filter_subset _ _) k).trans (R.live_mass (plan.count-1) fits k)


end
end Lower6960.Prefix6969Rescue.Invoice
end Z6969Source0641


section Z6969Source0642
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (Ambient UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ Mass)
open Far6969RescueGeometry (Model Family OnMark OnSurface)
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)
open Research6966

structure EarlyPrice where
  degree : ℕ
  seed : ℕ
  stop : ℕ
  tau : ℚ
  scale : ℚ
  credit : Fin 4 → ℕ
  fee : ℕ

namespace EarlyPrice

def calculatedFee (x : EarlyPrice) (plan : Plan) : Band → ℕ
  | .near => Invoice.eventFee plan x.stop plan.cutShape plan.history x.degree x.seed x.tau x.scale
  | .middle => MiddleInvoice.eventFee plan x.stop plan.cutShape plan.history x.degree x.seed x.tau x.scale

def running (x : EarlyPrice) (plan : Plan) : Band → Mass
  | .near => Invoice.eventRunning plan x.stop plan.cutShape x.degree x.seed x.tau x.scale
  | .middle => MiddleInvoice.eventRunning plan x.stop plan.cutShape x.degree x.seed x.tau x.scale

structure Valid (x : EarlyPrice) (plan : Plan) (band : Band) : Prop where
  fits : x.stop < plan.count
  degree_min : 2 ≤ x.degree
  seed_pos : 0 < x.seed
  char : (2*x.degree-1)*x.seed < p
  graph_shape : plan.primeShape = graphShape x.degree x.seed
  slope_floor : plan.slopeFloor = 1
  tau_nonneg : 0 ≤ x.tau
  tau_le_one : x.tau ≤ 1
  rank_small : Invoice.rankB plan < p
  exact_fee : x.calculatedFee plan band ≤ x.fee
  retained : ∀ k, (x.credit k : ℚ) ≤ x.running plan band k

end EarlyPrice

/-- The same early rescue producer supplies a full-credit invoice at either height band. -/
theorem early_prefix {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    {plan : Plan} {first : ℕ} {band : Band} {x : EarlyPrice}
    (S : plan.Sources first band.last) (cert : x.Valid plan band)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0) :
    ∃ (R : Run F Crt G plan) (B : Book R) (Q : Finset Surface),
      B.final = R.live x.stop ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee ∧
      (∀ k, massQ B.final k ≤ plan.history x.stop k) ∧
      (∀ q∈Q, Parent q ∧ G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈Invoice.paid B ∨
        (regular G (M.label γ) (F.scalar γ) ∧ ∃ q∈Q, OnSurface F q γ) := by
  obtain ⟨R⟩ := S.run F Crt lo hi noPole residues phys prime
    (le_of_eq (cert.slope_floor.trans slope.symm)) seeded caps degree seed physical
  have geomCaps : RowCaps G (graphShape x.degree x.seed) := cert.graph_shape ▸ caps
  have bill : ∃ B : Book R, B.final = R.live x.stop ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee := by
    cases band
    · obtain ⟨event⟩ := Invoice.early_event R cert.degree_min cert.seed_pos prime slope geomCaps
        cert.char hi roots cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit cert.fits
        cert.exact_fee cert.retained
      exact ⟨event.book, event.final, event.count⟩
    · obtain ⟨event⟩ := MiddleInvoice.early_event R cert.degree_min cert.seed_pos prime slope geomCaps
        cert.char hi roots cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit cert.fits
        cert.exact_fee cert.retained
      exact ⟨event.book, event.final, event.count⟩
  obtain ⟨B, bend, count⟩ := bill
  obtain ⟨surfaces, geom, marked⟩ := Invoice.Book.surfaces B
  refine ⟨R, B, surfaces, bend, count, ?_, ?_, ?_⟩
  · intro k
    rw [bend]
    exact R.live_mass _ cert.fits k
  · intro q mem
    obtain ⟨parent, J, live, origin⟩ := geom q mem
    have inIdeal : G∈q.asIdeal := by
      rw [origin]
      exact (R.parent_geom (Invoice.Book.final_initial B live)).2.2.2.1
    exact ⟨parent, inIdeal, J, live, origin⟩
  · intro γ mem
    rcases Invoice.Book.paid_or_regular B mem (roots γ mem) with paid | ⟨reg, survivor⟩
    · exact Or.inl paid
    · exact Or.inr ⟨reg, marked γ mem survivor⟩

end
end Lower6960.Prefix6969Rescue
end Z6969Source0642


section Z6969Source0768
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Rescue
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ Mass)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6966

structure NormalPrice where
  seed : ℕ
  tau : ℚ
  scale : ℚ
  credit : Fin 4 → ℕ
  fee : ℕ

namespace NormalPrice

def calculatedFee (x : NormalPrice) (plan : Plan) : ℕ :=
  Invoice.eventFee plan plan.count plan.normalShape plan.history 2 x.seed x.tau x.scale

def running (x : NormalPrice) (plan : Plan) : Mass :=
  Invoice.eventRunning plan plan.count plan.normalShape 2 x.seed x.tau x.scale

structure Valid (x : NormalPrice) (plan : Plan) : Prop where
  seed_pos : 0 < x.seed
  char : 3*x.seed < p
  graph_shape : plan.primeShape = graphShape 2 x.seed
  slope_floor : plan.slopeFloor = 1
  tau_nonneg : 0 ≤ x.tau
  tau_le_one : x.tau ≤ 1
  rank_small : Invoice.rankB plan < p
  exact_fee : x.calculatedFee plan ≤ x.fee
  retained : ∀ k, (x.credit k : ℚ) ≤ x.running plan k

end NormalPrice

/-- Run the full slope-one rescue schedule, including the proper terminal-bank cut. -/
theorem normal_prefix {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    {plan : Plan} {x : NormalPrice}
    (S : plan.Sources 2308 2313) (cert : x.Valid plan)
    (lo : 2308 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2313)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G plan.primeShape)
    (degree : plan.degree ≤ jetDegree G) (seed : plan.seedFloor ≤ seedDegree G)
    (physical : plan.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (roots : ∀ γ∈Γ, jetAt G (M.label γ) (F.scalar γ) = 0) :
    ∃ (R : Run F Crt G plan) (B : Book R) (Q : Finset Surface),
      B.final = R.terminal ∧
      (Invoice.paid B).card + Invoice.charge B x.credit ≤ x.fee ∧
      (∀ k, massQ B.final k ≤ plan.history (plan.count-1) k) ∧
      (∀ q∈Q, Parent q ∧ Prefix6969Wide.SurfacePass Crt (word M) q ∧
        G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈Invoice.paid B ∨
        (regular G (M.label γ) (F.scalar γ) ∧ ∃ q∈Q, OnSurface F q γ) := by
  obtain ⟨R⟩ := S.run F Crt lo hi noPole residues phys prime
    (le_of_eq (cert.slope_floor.trans slope.symm)) seeded caps degree seed physical
  have geomCaps : RowCaps G (graphShape 2 x.seed) := cert.graph_shape ▸ caps
  obtain ⟨event⟩ := Invoice.normal_event R (le_refl 2) cert.seed_pos prime slope geomCaps cert.char hi roots
    cert.tau_nonneg cert.tau_le_one cert.rank_small x.credit noPole residues cert.exact_fee cert.retained
  let B := event.book
  obtain ⟨surfaces, geom, marked⟩ := Invoice.Book.surfaces B
  refine ⟨R, B, surfaces, event.final, event.count, ?_, ?_, ?_⟩
  · intro k
    show massQ event.book.final k ≤ _
    rw [event.final]
    exact Invoice.Run.mass_terminal R k
  · intro q hq
    obtain ⟨parent, J, mem, origin⟩ := geom q hq
    obtain ⟨pass, inIdeal⟩ := Invoice.Book.terminal_parent B event.final mem origin
    exact ⟨parent, pass, inIdeal, J, mem, origin⟩
  · intro γ mem
    rcases Invoice.Book.paid_or_regular B mem (roots γ mem) with paid | ⟨reg, survivor⟩
    · exact Or.inl paid
    · exact Or.inr ⟨reg, marked γ mem survivor⟩


end
end Lower6960.Prefix6969Rescue
end Z6969Source0768


section Z6969Source0643
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Pair
noncomputable section

open Finset Polynomial
open K1 (K)
open K1_14 (Jet jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2 (UsesSeed toJet)
open K1_14_2_2 (RowCaps)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open P1_7_4 (massQ)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6970.Height2313.Lower6960.Prefix6969Main (Band)
open PrefixRows (Common)
open Research6966
open scoped Classical

def zeros {u del} {M : Model u del} {Γ} (F : Family M Γ) (G : Jet) : Finset K :=
  Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ) = 0)

def zeros_family {u del} {M : Model u del} {Γ} (F : Family M Γ) (G : Jet) :
    Family M (zeros F G) :=
  ⟨F.scalar, fun γ hγ => F.mark γ (mem_filter.mp hγ).1, F.distinct.mono (filter_subset _ _)⟩

/-- One paired production theorem for every saved early rescue event. -/
theorem produce {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {first extra a low floor : ℕ} {outer : P1_7.Bank} {band : Band}
    {main : Prefix6969Main.Plan} {mp : Prefix6969Main.Pricing}
    (mainValid : main.Valid) (mainPrice : mp.Valid main band)
    (mainSource : main.Sources first band.last outer extra a low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : Prefix6969Rescue.EarlyPrice}
    (rescueSource : rescue.Sources first band.last) (rescuePrice : rp.Valid rescue band)
    (firstPos : 0 < first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G)
    (caps : RowCaps G rescue.primeShape)
    (known : Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (mainDegree : a ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    ∃ (R : Prefix6969Main.Rows main F Crt) (I : Prefix6969Main.Initial R)
      (Q : Prefix6969Rescue.Run (zeros_family F G) Crt G rescue)
      (B : Prefix6969Rescue.Book Q) (paid : Finset K) (A S : Finset Surface),
      B.final=Q.live rp.stop ∧
      paid.card + mp.charge I.final + Prefix6969Rescue.Invoice.charge B rp.credit ≤ mp.fee+rp.fee ∧
      (∀ k, massQ I.final k ≤ main.history main.last k) ∧
      (∀ k, massQ B.final k ≤ rescue.history rp.stop k) ∧
      (∀ q∈A, Parent q ∧ Prefix6969Main.SurfacePass Crt (word M) q) ∧
      (∀ q∈A, ∃ J∈I.final, q.asIdeal=J.comap toJet) ∧
      (∀ q∈S, Parent q ∧ G∈q.asIdeal ∧ ∃ J∈B.final, q.asIdeal=J.comap toJet) ∧
      ∀ γ∈Γ, γ∈paid ∨ (jetAt G (M.label γ) (F.scalar γ) ≠ 0 ∧ ∃ q∈A, OnSurface F q γ) ∨
        (jetAt G (M.label γ) (F.scalar γ) = 0 ∧ Prefix6969Rescue.regular G (M.label γ) (F.scalar γ) ∧
          ∃ q∈S, OnSurface F q γ) := by
  obtain ⟨R, I, C, A, identity, mainCount, mainMass, mainGeom, mainOrigin, mainCover⟩ :=
    Prefix6969Main.main_prefix F Crt main mainValid band mp mainPrice mainSource firstPos lo hi
      noPole residues phys known mainDegree mainSeed mainFloor
  have subRes : ∀ γ∈zeros F G, MarkResidues D (M.label γ) ((zeros_family F G).scalar γ) :=
    fun γ hγ => residues γ (mem_filter.mp hγ).1
  have roots : ∀ γ∈zeros F G, jetAt G (M.label γ) ((zeros_family F G).scalar γ) = 0 :=
    fun γ hγ => (mem_filter.mp hγ).2
  obtain ⟨Q, B, S, bend, rescueCount, rescueMass, rescueGeom, rescueCover⟩ :=
    Prefix6969Rescue.early_prefix (zeros_family F G) (Crt := Crt) rescueSource rescuePrice lo hi noPole subRes
      phys prime slope seeded caps rescueDegree rescueSeed rescueFloor roots
  refine ⟨R, I, Q, B, C.paid ∪ Prefix6969Rescue.Invoice.paid B, A, S, bend,
    ?_, mainMass, rescueMass, mainGeom, mainOrigin, rescueGeom, ?_⟩
  · have union := card_union_le C.paid (Prefix6969Rescue.Invoice.paid B)
    omega
  · intro γ hγ
    by_cases root : jetAt G (M.label γ) (F.scalar γ) = 0
    · rcases rescueCover γ (mem_filter.mpr ⟨hγ, root⟩) with paid | ⟨reg, on⟩
      · exact Or.inl (mem_union_right _ paid)
      · exact Or.inr (Or.inr ⟨root, reg, on⟩)
    · have inMain : γ∈R.marks := mem_filter.mpr ⟨hγ, by simpa only [identity] using root⟩
      rcases mainCover γ inMain with paid | on
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr (Or.inl ⟨root, on⟩)

end
end Lower6960.Prefix6969Pair
end Z6969Source0643


section Z6969Source0659
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet atX jetAt)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_3 (Surface Parent)
open Far6969RescueGeometry (Model Family OnSurface)
open Research6970.Height2313.Lower6960.Prefix6969Rescue (graphShape regular)
open Research6969 Research6966
open scoped Classical Differential BigOperators

theorem compensate (w c n v : ℕ) (cap : n ≤ v) :
    w*n ≤ c*n+(w-c)*v := by
  have le : w ≤ c+(w-c) := by omega
  exact (Nat.mul_le_mul_right n le).trans (by
    rw [Nat.add_mul]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ cap) _)

theorem graph_exit {u del} {M : Model u del} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ) {G : Jet} (prime : Prime G) (slope : G.natDegree=1)
    {a U d : ℕ} (low : 2≤K1_14_2_2_2_1.jetDegree G) (hp : 0<U) (caps : RowCaps G (graphShape a U))
    (physical : 131071+M.overhead≤(d:ℤ)) (dp : 0<d) (gap : d<179730) (tame : d<p)
    {S : Finset Surface} (geo : ∀q∈S,Parent q)
    (src : Finset (Ideal Ambient)) (active : ∀J∈src,Active J)
    (origin : ∀q∈S,∃J∈src,q.asIdeal=J.comap toJet)
    (on : ∀γ∈T,∃q∈S,OnSurface F q γ)
    (roots : ∀γ∈T,jetAt G (M.label γ) (F.scalar γ)=0)
    (reg : ∀γ∈T,regular G (M.label γ) (F.scalar γ))
    (credit : Fin 4→ℕ) {e v : ℕ} (ec : mass src 0 ≤ e) (vc : mass src 1 ≤ v) :
    T.card ≤ (∑k,credit k*mass src k)+
      (JointRouted.seedWeight d U^2-credit 0)*e+
      (2*JointRouted.seedWeight d U*JointRouted.ordWeight d (a-1)-credit 1)*v := by
  obtain ⟨H,N,gp,eq,degree⟩ := HelperGraph.of_prime prime slope
  have hg : K1_14_2_2_2_1.jetDegree G ≤ a :=
    (K1_14_2_2_2_1.jetDegree_le G a).mpr fun j i hn => (caps j i hn).1
  have nonlinear : 2≤H.graphDegree := degree.symm ▸ low
  obtain ⟨f,proj⟩ := JointProjection.exists_product S geo
  have measures := JointProjection.measures proj src active origin
  have width (j i : ℕ) : ((N.poly.coeff j).coeff i).totalDegree≤U := by
    rw [eq]
    by_cases hz : (G.coeff j).coeff i = 0
    · simp [hz]
    · exact (caps j i hz).2.2
  have fit : 179730≤Fintype.card I := by
    rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)]
    decide
  have counted := NativeSurfaceCount.regular_equation F sub proj.primitive.ne_zero
    N gp nonlinear hp width ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) physical dp gap fit tame
    (fun γ mem => by simpa only [NativeGraphExceptional.den,NativeGraphExceptional.rhs,eq] using
      Prefix6969Rescue.graph_law slope (roots γ mem))
    (fun γ mem => by
      obtain ⟨q,hq,mark⟩ := on γ mem
      have hit := mark _ (proj.vanishes hq)
      simpa [jetAt,NonlinearMarkRows.evaluate,NativeSurfaceCount.label,K1_14.graphEval] using hit)
    (fun γ mem => by simpa only [NativeGraphExceptional.den,eq,regular,Prefix6969Rescue.denominator,
      NativeLostCurve.seed,NativeSurfaceCount.label] using reg γ mem)
  have rounded := NativeSurfaceCount.round_price (bad:=0) (marks:=T.card) (g:=f.natDegree)
    (v:=K1_14_4.seedDegree f) (r:=H.graphDegree-1) (u:=U) (n:=Fintype.card I)
    (a:=179730) (d:=d) (by simpa using counted)
  simp only [Nat.zero_add] at rounded
  change T.card≤f.natDegree*JointRouted.seedWeight d U^2+
    2*K1_14_4.seedDegree f*JointRouted.seedWeight d U*JointRouted.ordWeight d (H.graphDegree-1) at rounded
  have ord : JointRouted.ordWeight d (H.graphDegree-1) ≤ JointRouted.ordWeight d (a-1) := by
    apply Nat.add_le_add_right
    apply Int.toNat_le_toNat
    apply Int.ceil_mono
    apply add_le_add_left
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast Nat.sub_le_sub_right (degree.trans_le hg) 1
    · unfold MarkedAdaptive.price
      positivity
  have payE := compensate (JointRouted.seedWeight d U^2) (credit 0) (mass src 0) e ec
  have payV := compensate (2*JointRouted.seedWeight d U*JointRouted.ordWeight d (a-1))
    (credit 1) (mass src 1) v vc
  have nd := rounded.trans (Nat.add_le_add (Nat.mul_le_mul_right _ measures.1)
    (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 measures.2)) ord))
  rw [show mass src 0 * JointRouted.seedWeight d U ^ 2 =
    JointRouted.seedWeight d U ^ 2 * mass src 0 by ring,
    show 2 * mass src 1 * JointRouted.seedWeight d U * JointRouted.ordWeight d (a-1) =
    (2*JointRouted.seedWeight d U*JointRouted.ordWeight d (a-1))*mass src 1 by ring] at nd
  simp only [Fin.sum_univ_four]
  omega

theorem coefficient_mono : Monotone JointLedger.coefficient := by
  intro j k le
  unfold JointLedger.coefficient
  apply Nat.mul_le_mul_right
  apply Nat.sub_le_sub_right
  exact Nat.add_le_add (Near6969FactorPrice.rate_mono (max_le_max le_rfl le))
    (Nat.mul_le_mul_left _ le)

theorem marked_exit {u del} {M : Model u del} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ) (hi : M.overhead.toNat≤2557)
    {S : Finset Surface} (geo : ∀q∈S,Parent q)
    (src : Finset (Ideal Ambient)) (active : ∀J∈src,Active J)
    (origin : ∀q∈S,∃J∈src,q.asIdeal=J.comap toJet)
    (on : ∀γ∈T,∃q∈S,OnSurface F q γ)
    (credit : Fin 4→ℕ) {e v : ℕ} (ec : mass src 0 ≤ e) (vc : mass src 1 ≤ v)
    (small : e<64) (char : (2*e-1)*v<p) :
    T.card ≤ (∑k,credit k*mass src k)+
      (JointLedger.coefficient e-credit 1)*v+2*e^2 := by
  obtain ⟨f,proj⟩ := JointProjection.exists_product S geo
  have measures := JointProjection.measures proj src active origin
  have deg := measures.1.trans ec
  have actual := JointMarked.owned_count F sub hi f proj.primitive proj.separable
    (deg.trans_lt small) measures.2
    ((Nat.mul_le_mul
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 deg) 1) vc).trans_lt char) (by
      intro γ mem
      obtain ⟨q,hq,mark⟩ := on γ mem
      simpa [jetAt,Polynomial.eval_map] using mark _ (proj.vanishes hq))
  by_cases z : f.natDegree=0
  · simp only [z, JointMarked.price, if_true] at actual
    exact actual.trans (Nat.zero_le _)
  rw [JointMarked.price, if_neg z] at actual
  have lin : (Near6969FactorPrice.rate (max 3 f.natDegree)+2*f.natDegree-1)*
      (p*mass src 1) ≤ JointLedger.coefficient e * mass src 1 := by
    rw [←Nat.mul_assoc]
    exact Nat.mul_le_mul (coefficient_mono deg) le_rfl
  have curve : (max 3 f.natDegree-1)*f.natDegree ≤ 2*e^2 := by
    have ep : 1≤e := (Nat.pos_of_ne_zero z).trans_le deg
    have b : max 3 f.natDegree-1 ≤ 2*e := by
      have h : max 3 f.natDegree ≤ 2*e+1 := max_le (by omega) (by omega)
      omega
    simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul b deg
  have pay := compensate (JointLedger.coefficient e) (credit 1) (mass src 1) v vc
  simp only [Fin.sum_univ_four]
  omega

end
end Lower6960.Prefix6969Early
end Z6969Source0659


end Research6970.Height2313
