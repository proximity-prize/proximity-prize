import ProximityPrize.SubmissionLower.R6966ProofPadeDescent
import ProximityPrize.SubmissionLower.PortHighFinish
import Mathlib.FieldTheory.Minpoly.IsConjRoot

set_option Elab.async false

namespace Research6966.Pade
open Polynomial Finset
open scoped Polynomial
noncomputable section
variable {K E : Type*} [Field K] [Field E]

/-- Exactly the two types of graph tested by the interpolation rank receipts.
The ordinates in the witness are pairwise distinct by construction. -/
def Spread (sheet:E→E→Prop) (e c amax:ℕ) : Prop :=
  ∃ (G:Row E) (s:Finset E) (v:E→E), G.primitive ∧
    (∀y∈s,sheet y (v y) ∧ G.err v y=0) ∧
    ((amax<G.graphDegree ∧ G.graphDegree≤c ∧ e-c+G.graphDegree≤s.card) ∨
     (e+1-(e+1)/2≤G.graphDegree ∧ G.graphDegree≤e-c ∧ e≤s.card))

theorem native_or_spread [Algebra K E] [IsGalois K E] [Infinite E]
    (sheet:E→E→Prop) (e c amax:ℕ) (large:2≤e) (gap:2*c<e)
    (initial:∃ (s:Finset E) (v:E→E),s.card=e ∧ ∀y∈s,sheet y (v y))
    (stable : ∀ (σ:E≃ₐ[K]E) x y,sheet x y → sheet (σ x) (σ y)) :
    Spread sheet e c amax ∨
      ∃ G:Row K,G.primitive ∧ G.graphDegree≤amax ∧ Controls (G.map (algebraMap K E)) sheet c := by
  classical
  by_cases prohibited:Spread sheet e c amax
  · exact Or.inl prohibited
  right
  obtain ⟨F,fp,degree,ctrl⟩ := global_of_local sheet e c amax gap initial (by
    intro s v se allSheets
    obtain ⟨l,lp,upper,⟨G,t,gp,sub,gdeg,kept,gh⟩,⟨H,hp,full,hits⟩⟩ :=
      interpolation_alternatives s v (by omega)
    have small : l≤c := by
      by_contra! above
      exact prohibited ⟨H,s,v,hp,fun y hy=> ⟨allSheets y hy,hits y hy⟩,Or.inr (by omega)⟩
    have maxdeg:G.graphDegree≤amax := by
      by_contra! above
      exact prohibited ⟨G,t,v,gp,fun y hy=>⟨allSheets y (sub hy),gh y hy⟩,
        Or.inl ⟨above,by omega,by omega⟩⟩
    have outside : misses G v s ⊆ s\t := by
      intro x hx
      obtain ⟨xs,no⟩:=mem_filter.mp hx
      exact mem_sdiff.mpr ⟨xs,fun xt=>no (gh x xt)⟩
    have bound:=card_le_card outside
    have sum:=card_sdiff_add_card_eq_card sub
    exact ⟨G,gp,maxdeg,by omega⟩)
  obtain ⟨G,gp,size,gc⟩:=descend_control (K:=K) sheet e c gap initial stable fp ctrl
  exact ⟨G,gp,size.le.trans degree,gc⟩

namespace Native
open K1_14 (Jet Seeds)
open K1_14_3 (SeedField SeedClosure OnSeedFibre Surface Parent)
abbrev Sep := separableClosure SeedField SeedClosure

private def jetEval {L:Type*} [Field L] [Algebra SeedField L] (y v:L) : Jet →+* L :=
  eval₂RingHom (eval₂RingHom ((algebraMap SeedField L).comp (algebraMap Seeds SeedField)) y) v

private theorem natural_eval {L M : Type*} [Field L] [Field M]
    [Algebra SeedField L] [Algebra SeedField M] (f:L→ₐ[SeedField]M) (y v:L) :
    f.toRingHom.comp (jetEval y v)=jetEval (f y) (f v) := by
  apply Polynomial.ringHom_ext'
  · apply Polynomial.ringHom_ext
    · intro z
      simp [jetEval,RingHom.comp_apply,AlgHom.commutes]
    · simp [jetEval,RingHom.comp_apply]
  · simp [jetEval,RingHom.comp_apply]

private theorem kernel_natural {L M : Type*} [Field L] [Field M]
    [Algebra SeedField L] [Algebra SeedField M] (f:L→ₐ[SeedField]M) (y v:L) :
    RingHom.ker (jetEval (f y) (f v))=RingHom.ker (jetEval y v) := by
  rw [←natural_eval f y v]
  ext Q
  change f (jetEval y v Q)=0 ↔ jetEval y v Q=0
  exact map_eq_zero_iff f f.injective

def sheets (parents:Finset Surface) (y v:Sep) : Prop :=
  ∃ q∈parents,RingHom.ker (jetEval y v)=q.asIdeal

theorem sheets_iff (parents:Finset Surface) (y v:Sep) :
    sheets parents y v ↔ ∃ q∈parents,OnSeedFibre q (y:SeedClosure) (v:SeedClosure) := by
  have eq := kernel_natural (IntermediateField.val (separableClosure SeedField SeedClosure)) y v
  change (∃ q∈parents,RingHom.ker (jetEval y v)=q.asIdeal) ↔
    (∃ q∈parents,RingHom.ker (jetEval (y:SeedClosure) (v:SeedClosure))=q.asIdeal)
  rw [←eq]
  rfl

/-- Every actual parent supplies a point on the separable fibre used by
the interpolation argument. No perfection of the seed field is required. -/
theorem parent_witness {parents:Finset Surface} {q:Surface} (mem:q∈parents) (geo:Parent q) :
    ∃ y v:Sep, sheets parents y v ∧ OnSeedFibre q (y:SeedClosure) (v:SeedClosure) := by
  obtain ⟨y,v,fibre,ys,vs⟩ := geo.seed_side
  let y':Sep:=⟨y,mem_separableClosure_iff.mpr ys⟩
  let v':Sep:=⟨v,mem_separableClosure_iff.mpr vs⟩
  exact ⟨y',v',(sheets_iff ..).mpr ⟨q,mem,fibre⟩,fibre⟩

theorem stable (parents:Finset Surface) (σ:Sep≃ₐ[SeedField]Sep) {y v:Sep}
    (h:sheets parents y v) : sheets parents (σ y) (σ v) := by
  obtain ⟨q,mem,hq⟩:=h
  exact ⟨q,mem,(kernel_natural σ.toAlgHom y v).trans hq⟩

/-- The native projected degree is precisely the size of a selection with
distinct separable ordinates and genuine parent slopes at every one. -/
theorem projected_sheets (parents:Finset Surface) (nonempty:parents.Nonempty)
    (geo:∀ q∈parents,Parent q) :
    ∃ (f:K1_14.Equation) (s:Finset Sep) (v:Sep→Sep),
      K1_14_3.ProjectedProduct parents f ∧ s.card=f.natDegree ∧
        ∀ x∈s,sheets parents x (v x) := by
  classical
  choose y v witnessed using fun q : ↥parents=>parent_witness q.property (geo q q.property)
  let m (q:↥parents):=minpoly SeedField ((y q):SeedClosure)
  let factors:=parents.attach.image m
  let g : Polynomial SeedField := ∏ p∈factors,p
  obtain ⟨f,pf,model⟩ := K1_14_3_7.projected_from_points parents nonempty
    (fun q=>(y q:SeedClosure)) (fun q=>(v q:SeedClosure))
    (fun q=>(witnessed q).2) (fun q=>mem_separableClosure_iff.mp (y q).property)
  change Associated (f.map (algebraMap Seeds SeedField)) g at model
  have sep : g.Separable := pf.separable.of_dvd model.dvd'
  have mf : ∀ q,m q=minpoly SeedField (y q) :=
    fun q=>minpoly.algHom_eq (IntermediateField.val (separableClosure SeedField SeedClosure))
              (fun _ _ eq=>Subtype.ext eq) (y q)
  have pre {p:Polynomial SeedField} (hp:p∈factors) : ∃ q,m q=p := by
    obtain ⟨q,_,hq⟩:=mem_image.mp hp
    exact ⟨q,hq⟩
  have split : (g.map (algebraMap SeedField Sep)).Splits := by
    dsimp only [g];rw [Polynomial.map_prod]
    apply Polynomial.Splits.prod
    intro p hp
    obtain ⟨q,rfl⟩:=pre hp
    rw [mf]
    exact Normal.splits (inferInstance:Normal SeedField Sep) _
  let s:Finset Sep:=(g.aroots Sep).toFinset
  have cs:s.card=g.natDegree := by
    dsimp only [s,aroots_def]
    rw [Multiset.toFinset_card_of_nodup (nodup_roots sep.map),←split.natDegree_eq_card_roots,
      natDegree_map_eq_of_injective (algebraMap SeedField Sep).injective]
  have deg:g.natDegree=f.natDegree := by
    have fn : f.map (algebraMap Seeds SeedField)≠0 :=
      (map_ne_zero_iff (mapRingHom _) (map_injective _ (IsFractionRing.injective Seeds SeedField))).mpr pf.primitive.ne_zero
    have de := le_antisymm (natDegree_le_of_dvd model.dvd' fn) (natDegree_le_of_dvd model.dvd sep.ne_zero)
    rwa [natDegree_map_eq_of_injective (IsFractionRing.injective Seeds SeedField)] at de
  have each (x:Sep) (hx:x∈s) : ∃ t,sheets parents x t := by
    have root := (mem_aroots.mp (Multiset.mem_toFinset.mp hx)).2
    change aeval x (∏ p∈factors,p)=0 at root
    rw [map_prod,prod_eq_zero_iff] at root
    obtain ⟨p,hp,hz⟩:=root
    obtain ⟨q,rfl⟩:=pre hp
    rw [mf] at hz
    have conj := (isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral (R:=SeedField) (y q))).mpr hz
    obtain ⟨σ,actual⟩:=conj.symm.exists_algEquiv
    exact ⟨σ (v q),actual ▸ stable parents σ (witnessed q).1⟩
  let slope (x:Sep):=if hx:x∈s then Classical.choose (each x hx) else 0
  exact ⟨f,s,slope,pf,cs.trans deg,fun x hx=>by simpa [slope,hx] using Classical.choose_spec (each x hx)⟩

/-- Terminal packet dichotomy on the actual native seed fraction field. -/
theorem classify (parents:Finset Surface) (e c amax:ℕ) (large:2≤e) (gap:2*c<e)
    (initial:∃ (s:Finset Sep) (v:Sep→Sep),s.card=e ∧ ∀y∈s,sheets parents y (v y)) :
    Spread (sheets parents) e c amax ∨ ∃ G:Row SeedField,
      G.primitive ∧ G.graphDegree≤amax ∧ Controls (G.map (algebraMap SeedField Sep)) (sheets parents) c := by
  let emb:K1_14.L→+*SeedField := ((algebraMap Seeds SeedField).comp MvPolynomial.C).comp
    (algebraMap K1_14.L K1_14.FX)
  have : Infinite SeedField:=Infinite.of_injective emb emb.injective
  have : Infinite Sep:=Infinite.of_injective (algebraMap SeedField Sep) (algebraMap SeedField Sep).injective
  exact native_or_spread (sheets parents) e c amax large gap initial (fun σ _ _ h=>stable parents σ h)


/-- No extra assumption about the size or realizability of the seed fibre
is needed at the terminal consumer. -/
theorem packet_cases (parents:Finset Surface) (nonempty:parents.Nonempty)
    (geo:∀ q∈parents,Parent q) (e c amax:ℕ) (large:2≤e) (gap:2*c<e) :
    ∃ f:K1_14.Equation, K1_14_3.ProjectedProduct parents f ∧
      (f.natDegree<e ∨ Spread (sheets parents) e c amax ∨ ∃ G:Row SeedField,
       G.primitive ∧ G.graphDegree≤amax ∧ Controls (G.map (algebraMap SeedField Sep)) (sheets parents) c) := by
  classical
  obtain ⟨f,s,v,pf,size,all_sheets⟩:=projected_sheets parents nonempty geo
  refine ⟨f,pf,?_⟩
  by_cases small:f.natDegree<e
  · exact Or.inl small
  obtain ⟨T,sub,n⟩:=exists_subset_card_eq (show e≤s.card by omega)
  exact Or.inr (classify parents e c amax large gap ⟨T,v,n,fun x hx=>all_sheets x (sub hx)⟩)

/-- Project on the actual parents off the graph. This pays only the
exceptional ordinates even if several parents share an ordinate. -/
theorem off_graph_product {Kset S:Finset Surface} (sub:S⊆Kset) (nonempty:S.Nonempty)
    (geo:∀ q∈S,Parent q) (G:Row SeedField) (c:ℕ)
    (control:Controls (G.map (algebraMap SeedField Sep)) (sheets Kset) c)
    (off:∀ y v:Sep,sheets S y v → (G.map (algebraMap SeedField Sep)).a.eval y*v ≠
      (G.map (algebraMap SeedField Sep)).b.eval y) :
    ∃ f:K1_14.Equation,K1_14_3.ProjectedProduct S f ∧ f.natDegree+G.graphDegree≤c := by
  obtain ⟨f,t,v,hf,size,pts⟩:=projected_sheets S nonempty geo
  refine ⟨f,hf,?_⟩
  have paid := control t v (by
    intro x hx
    obtain ⟨q,hq,hp⟩:=pts x hx
    exact ⟨⟨q,sub hq,hp⟩,sub_ne_zero.mpr (off _ _ (pts x hx))⟩)
  rwa [size,Row.degree_map] at paid

end Native
end
end Research6966.Pade
