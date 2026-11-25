import ProximityPrize.SubmissionLower.R6966ProofPadeIntegralGraph

set_option Elab.async false

namespace Research6966.PadeConcentration
open Polynomial Finset
open K1_14 (Jet L Shape)
open K1_14_1 (PoleData CRTLift RawSource jetConstant centerEval)
open K1_14_1_4 (doubleMap specialized)
open K1_14_3 (SeedClosure SeedField Parent Surface fibreRow)
open PadeRank (Plane)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev E:=SeedClosure
private abbrev extField:=algebraMap SeedField E

/-- One primitive integral physical polynomial for the descended graph
at this CRT chart. Its choice precedes the choice of bank, row and cutoff. -/
structure Model {h} {D:PoleData h} (Crt:CRTLift D) (G:Pade.Row SeedField) where
  raw : RawSource
  primitive : raw.IsPrimitive
  transform : Plane E →ₐ[E] Plane E
  scalar : E
  nonzero : scalar≠0
  equation : doubleMap PadeRawField.rawField raw = jetConstant scalar*transform ((G.map extField).polynomial)
  onRows : ∀ P:Jet, transform (fibreRow P)=doubleMap extField (specialized Crt P)
  leading : ∀ {P:Plane E},P≠0 → (transform P).natDegree=P.natDegree ∧
    (transform P).leadingCoeff.natDegree=P.leadingCoeff.natDegree ∧ transform P≠0

theorem exists_model {h} {D:PoleData h} (Crt:CRTLift D) {G:Pade.Row SeedField} (gp:G.primitive) :
    Nonempty (Model Crt G) := by
  obtain ⟨a,b,u,d,ne,form⟩:=K1_14_1_4.specialized_affine_form Crt
  let f:=extField
  let T:=PadeChart.chart (f a) (f b) (f u) (f d)
  let T₀:=PadeChart.chart a b u d
  obtain ⟨g,c,prim,cn,eq⟩:=PadeIntegralGraph.raw_model (T₀ G.polynomial)
    (PadeChart.chart_graph_primitive a b u d ne gp)
  refine ⟨⟨g,prim,T,f c,(map_ne_zero f).mpr cn,?_,?_,?_⟩⟩
  · have mapped:=congrArg (doubleMap f) eq
    rw [map_mul] at mapped
    have lhs:doubleMap f (doubleMap K1_14_1_4.evalRaw g)=doubleMap PadeRawField.rawField g := by
      ext j i;simp only [doubleMap,coe_mapRingHom,coeff_map,PadeRawField.rawField,RingHom.comp_apply];rfl
    have unit:doubleMap f (jetConstant c)=jetConstant (f c) := by
      simp only [jetConstant,doubleMap,RingHom.comp_apply,coe_mapRingHom,Polynomial.map_C]
    have mappedGraph : doubleMap f G.polynomial=(G.map f).polynomial:=by
      simp only [Pade.Row.polynomial,Pade.Row.map,doubleMap,coe_mapRingHom,Polynomial.map_C,
        Polynomial.map_X,map_sub,map_mul]
    have natural:=PadeFiltered.base_change (RingHom.id SeedField) f a b u d
    rw [RingHom.comp_id] at natural
    have commute:=RingHom.congr_fun natural G.polynomial
    change T (doubleMap f G.polynomial)=doubleMap f (T₀ G.polynomial) at commute
    rw [mappedGraph] at commute
    rwa [lhs,unit,←commute] at mapped
  · intro P
    change T.toRingHom.comp (doubleMap (f.comp (algebraMap K1_14.Seeds SeedField))) P =
      (doubleMap f).comp (specialized Crt).toRingHom P
    rw [form,PadeFiltered.base_change]
  · intro P pn
    exact K1_14_1_4.affine_leading (RingHom.id E) Function.injective_id ((map_ne_zero f).mpr ne)
      (b:=f b) (C (f u)*Polynomial.X+C (f d)) pn

/-- Every actual complete source has an integral quotient with the raw
physical weight reduced by the full rounded number of forced powers. -/
theorem Model.quotient {h A W r:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    {Crt:CRTLift D} {G:Pade.Row SeedField} (m:Model Crt G) (gp:G.primitive)
    (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    (ys:Finset E) (v:E→E)
    (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ (G.map extField).err v y=0)
    (many:2*G.graphDegree-1<ys.card) (b:ℕ) (bound:min s.B ((W+s.J)/(131071-h))≤b)
    {P:K1_14_1.Source} (member:P∈KoalaRect.rectComplete Crt word s W U) :
    let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
    ∃ Q:RawSource,K1_14_1.forward Crt P=jetConstant ((K1_14_1.rawBlock D)^(s.B+s.J))*(m.raw^t*Q) ∧
      K1_14_1_4.Bounded (131071-h) (131071-h-1) (W-t*RawPhysicalDegree.weight (131071-h) (131071-h-1) m.raw) Q := by
  classical
  let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
  have cMem:centerEval P∈KoalaRect.rectEvaluated Crt word s W U:=Submodule.subset_span ⟨P,member,rfl⟩
  have inBank:fibreRow (centerEval P)∈PadeBankRank.rows Crt word s W U:=
    Submodule.subset_span ⟨centerEval P,cMem,rfl⟩
  have fieldPow:=PadeFiltered.forced_bank_layers hp hl Crt word U fits small cut geo pass ys v
    ((G.primitive_map extField).mpr gp) sheets (by rwa [Pade.Row.degree_map]) b bound inBank
  rw [Pade.Row.degree_map] at fieldPow
  change (G.map extField).polynomial^t ∣ fibreRow (centerEval P) at fieldPow
  have transformed:=map_dvd m.transform fieldPow
  rw [map_pow,m.onRows] at transformed
  apply PadeRawField.quotient_of_fibre_power hp hl Crt word member.1 m.primitive t
  have unit:IsUnit (jetConstant m.scalar:Plane E):=isUnit_C.mpr (isUnit_C.mpr m.nonzero.isUnit)
  rw [m.equation,mul_pow]
  exact (associated_unit_mul_left _ _ (unit.pow t)).dvd.trans transformed

#print axioms exists_model
#print axioms Model.quotient
end
end Research6966.PadeConcentration
