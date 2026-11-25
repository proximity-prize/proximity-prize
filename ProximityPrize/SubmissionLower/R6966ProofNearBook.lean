import ProximityPrize.SubmissionLower.R6966ProofNearMarkedCount
import ProximityPrize.SubmissionLower.High6966RescueCharge

set_option Elab.async false

namespace Research6966.NearBook
open Finset
open K1 (K)
open K1_14 (Jet Equation)
open K1_14_1 (CRTLift PoleData)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active mass mass_mono sectionDegree)
open K1_14_3 (Surface Parent ProjectedProduct)
open Lower6960.Rescue6966 (Model Family word SurfacePass OnSurface)
open KoalaRect (axisDegree axisDegree_le_iff)
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Packet {u deleted} (M:Model u deleted) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) where
  paid : Finset K
  parents : Finset Surface
  sources : Finset (Ideal Ambient)
  active : ∀ J∈sources,Active J
  geo : ∀ q∈parents,Parent q ∧ SurfacePass Crt (word M) q
  origin : ∀ q∈parents,∃ J∈sources,q.asIdeal=J.comap toJet

variable {u deleted} {M:Model u deleted} {D:PoleData M.overhead.toNat} {Crt:CRTLift D}

def empty : Packet M Crt := ⟨∅,∅,∅,by simp,by simp,by simp⟩

structure Paid (b:Packet M Crt) (fee credit seed degree:ℕ) : Prop where
  price : b.paid.card+credit*mass b.sources 1≤fee
  seedCap : mass b.sources 1≤seed
  degreeCap : mass b.sources 0≤degree

theorem empty_paid : Paid (empty:Packet M Crt) 0 0 0 0 :=
  ⟨by simp [empty],by simp [empty,mass],by simp [empty,mass]⟩

def parents (b c:Packet M Crt) := b.parents∪c.parents
def sources (b c:Packet M Crt) := b.sources∪c.sources

theorem parents_geo (b c:Packet M Crt) {q} (hq:q∈parents b c) :
    Parent q ∧ SurfacePass Crt (word M) q :=
  (mem_union.mp hq).elim (b.geo q) (c.geo q)

theorem sources_active (b c:Packet M Crt) {J} (h:J∈sources b c) : Active J :=
  (mem_union.mp h).elim (b.active J) (c.active J)

theorem origin (b c:Packet M Crt) {q} (h:q∈parents b c) :
    ∃ J∈sources b c,q.asIdeal=J.comap toJet := by
  rcases mem_union.mp h with left|right
  · obtain ⟨J,hJ,eq⟩:=b.origin q left
    exact ⟨J,mem_union_left _ hJ,eq⟩
  · obtain ⟨J,hJ,eq⟩:=c.origin q right
    exact ⟨J,mem_union_right _ hJ,eq⟩

theorem mass_union (b c:Packet M Crt) (k:Fin 4) :
    mass (sources b c) k≤mass b.sources k+mass c.sources k :=
  K1_14_2_2.sum_union_le (fun J=>sectionDegree J k) _ _

theorem projected_cap (b c:Packet M Crt) {S:Finset Surface} (sub:S⊆parents b c)
    {f:Equation} (pr:ProjectedProduct S f) :
    f.natDegree≤mass b.sources 0+mass c.sources 0 :=
  (NativeOrdinateMass.projected_degree pr (sources b c) (fun _=>sources_active b c)
    (fun _ h=>origin b c (sub h))).trans (mass_union b c 0)

def owning (G:Jet) (S:Finset Surface) := S.filter (fun q=>G∈q.asIdeal)
def outside (G:Jet) (S:Finset Surface) := S.filter (fun q=>G∉q.asIdeal)
def ownerSources (G:Jet) (J:Finset (Ideal Ambient)) := J.filter (fun j=>toJet G∈j)
def otherSources (G:Jet) (J:Finset (Ideal Ambient)) := J.filter (fun j=>toJet G∉j)

theorem split_mass (G:Jet) (J:Finset (Ideal Ambient)) (k:Fin 4) :
    mass (ownerSources G J) k+mass (otherSources G J) k=mass J k :=
  sum_filter_add_sum_filter_not .. 

theorem owner_cap (b c:Packet M Crt) (G:Jet) {f:Equation}
    (pr:ProjectedProduct (owning G (parents b c)) f) (i:ℕ) :
    (f.coeff i).totalDegree≤mass (ownerSources G (sources b c)) 1 := by
  apply NativeSeedDegree.projected_seed pr _ _ _ i
  · intro J h;exact sources_active b c (mem_filter.mp h).1
  · intro q h
    obtain ⟨J,hJ,eq⟩:=origin b c (mem_filter.mp h).1
    exact ⟨J,mem_filter.mpr ⟨hJ,by
      have own: G∈q.asIdeal:=(mem_filter.mp h).2
      rwa [eq] at own⟩,eq⟩

theorem outside_cap (b c:Packet M Crt) (G:Jet) {f:Equation}
    (pr:ProjectedProduct (outside G (parents b c)) f) (i:ℕ) :
    (f.coeff i).totalDegree≤mass (otherSources G (sources b c)) 1 := by
  apply NativeSeedDegree.projected_seed pr _ _ _ i
  · intro J h;exact sources_active b c (mem_filter.mp h).1
  · intro q h
    obtain ⟨J,hJ,eq⟩:=origin b c (mem_filter.mp h).1
    exact ⟨J,mem_filter.mpr ⟨hJ,by
      have off:G∉q.asIdeal:=(mem_filter.mp h).2
      rwa [eq] at off⟩,eq⟩

theorem axis_total {f:Equation} {d:ℕ} (cap:∀ i,(f.coeff i).totalDegree≤d) (z:Fin 2) :
    axisDegree f z≤d := (axisDegree_le_iff ..).mpr (fun i=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (cap i))

theorem marks_roots {Γ T:Finset K} (F:Family M Γ) {S:Finset Surface} {f:Equation}
    (pr:ProjectedProduct S f) (owns:∀γ∈T,∃q∈S,OnSurface F q γ) :
    ∀γ∈T,(f.map (K1_14.graphEval (M.label γ))).eval (K1_14.atX (F.scalar γ))=0 := by
  intro γ h
  obtain ⟨q,hq,on⟩:=owns γ h
  have zero:=on _ (pr.vanishes q hq)
  simpa only [K1_14.jetAt,Polynomial.eval₂_C,Polynomial.coe_eval₂RingHom,Polynomial.eval_map] using zero

#print axioms projected_cap
#print axioms owner_cap
#print axioms outside_cap
#print axioms marks_roots
end
end Research6966.NearBook
