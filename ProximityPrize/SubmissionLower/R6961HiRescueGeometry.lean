import ProximityPrize.SubmissionLower.R6961ExceptionalStage
import ProximityPrize.SubmissionLower.R6961HiRescueSourceException
import ProximityPrize.SubmissionLower.R6961PoleChartTypes

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 18000

namespace Lower6961.Hi.RescueGeometry
open Finset Polynomial
open K1 (I K)
open K1_14 (L FX Shape Jet jetAt atX liftPoly)
open K1_14_1 (PoleData CRTLift evaluated evaluated_shape MarkResidues nodeL)
open K1_14_2 (Ambient OnJet toJet jetMarkHom UsesSeed ODE)
open K1_14_2_2 (RowCaps Active dual Fits mass sectionDegree ordinateIncl ODECaps fixedOn)
open K1_14_2_2_2 (FiniteSections residualBudget ordinate_eq length_le_mass)
open K1_14_2_2_2_1 (rowCaps_iff jetDegree seedDegree)
open K1_14_2_2_4 (pairCap)
open K1_14_3 (SeedCover joinCovers joinCovers_covers joinCovers_degree joinCovers_points)
open RescueSource (bank reserve cutoff jetCap seedCap)
open Lower6960.DifferentialContact (Native)
open Lower6961.RescueGeometry (Model Family word OnMark label_injective contact_at_mark zero_of_contact OnSurface)
open scoped Classical
open K1_14_2_2_3 (shiftedWord)
open P0_10R_1 (seed_projection section_bound component_height)
open P1_7_4_1 (irreducible_cut)


def primeShape (rect : Fin 4) : Shape := ⟨0,jetCap rect,1,seedCap rect⟩

def initialCap (rect : Fin 4) : Fin 4 → ℕ := pairCap (primeShape rect) (bank rect 0).shape

theorem prime_shape_fit (rect : Fin 4) : (primeShape rect).J≤(primeShape rect).B := by
  fin_cases rect <;> decide

theorem initial_small (rect : Fin 4) (k : Fin 4) : initialCap rect k<K1.p := by
  fin_cases rect <;> fin_cases k <;> decide +kernel

theorem reserve_small (i : Fin 17) : reserve i<K1.p := by
  fin_cases i <;> decide +kernel


/-- The exceptional initial pair feeds the native section bound and retains
both row memberships on every component. -/
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

/-- Initial books and projective parents for the marks that lie on the
exceptional prime. The rank exit and dual parents share the original cap. -/
structure Initial {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    (G Q₀ : Jet) (rect : Fin 4) where
  seeds : SeedCover
  seed_degree : seeds.curve.totalDegree ≤ initialCap rect 2
  seed_points : seeds.points.card ≤ initialCap rect 3
  ordinates : Finset FX
  ordinate_card : ordinates.card ≤ initialCap rect 0
  rankExit : Finset (Ideal Ambient)
  parents : Finset (Ideal Ambient)
  rank_geom : ∀ J∈rankExit,Active J ∧ ¬dual J
  parent_geom : ∀ J∈parents,Active J ∧ dual J ∧ J.height=2 ∧ toJet G∈J ∧ toJet Q₀∈J
  disjoint : Disjoint rankExit parents
  fits : Fits (rankExit∪parents) (initialCap rect)
  covers : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 →
    seeds.Covers (M.label γ) ∨ atX (F.scalar γ)∈ordinates ∨
      (∃ J∈rankExit,OnMark F J γ) ∨ ∃ J∈parents,OnMark F J γ

private theorem classify {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {G Q₀ : Jet} {rect : Fin 4} {A : Finset (Ideal Ambient)}
    (geom : P1_7_4_1.SectionGeometry A) (fit : Fits A (initialCap rect))
    (rows : ∀ J∈A,toJet G∈J ∧ toJet Q₀∈J)
    (cover : ∀ γ∈Γ,jetAt G (M.label γ) (F.scalar γ)=0 → ∃ J∈A,OnMark F J γ) :
    Nonempty (Initial F G Q₀ rect) := by
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
    have small (k : Fin 4) := (length_le_mass hin k).trans_lt ((fit k).trans_lt (initial_small rect k))
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
    {G Q₀ : Jet} {rect : Fin 4} (irr : Irreducible G) (avoid : ¬G∣Q₀)
    (capsG : RowCaps G (primeShape rect)) (capsQ : RowCaps Q₀ (bank rect 0).shape)
    (zero : ∀ γ∈Γ,jetAt Q₀ (M.label γ) (F.scalar γ)=0) :
    Nonempty (Initial F G Q₀ rect) := by
  obtain ⟨A,geom,fit,rows,cover⟩ := initial_sections irr avoid capsG capsQ (prime_shape_fit rect)
    (RescueSource.shape_guards rect 0).2.1
  exact classify F geom fit rows (fun γ hγ hG => cover _ _ hG (zero γ hγ))

theorem Initial.rank_ode {u deleted} {M : Model u deleted} {Γ} {F : Family M Γ}
    {G Q₀ : Jet} {rect : Fin 4} (initial : Initial F G Q₀ rect) :
    ∃ E : ODE, ODECaps E (mass initial.rankExit 2) (mass initial.rankExit 1) ∧
      ∀ γ∈Γ,(∃ J∈initial.rankExit,OnMark F J γ) → K1_14_2.fixedAt E (F.scalar γ)=0 := by
  obtain ⟨E,caps,roots⟩ := P1_7_4.rank_equation initial.rankExit initial.rank_geom le_rfl le_rfl
  refine ⟨E,caps,?_⟩
  rintro γ _ ⟨J,hJ,on⟩
  simpa only [K1_14_2_2.eval_fixed] using RingHom.mem_ker.mp (on (roots J hJ))

#print axioms initial_cover
#print axioms Initial.rank_ode

end Lower6961.Hi.RescueGeometry
