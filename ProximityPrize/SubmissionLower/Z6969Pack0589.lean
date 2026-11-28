import ProximityPrize.SubmissionLower.Z6970PoleFormulaBound
import ProximityPrize.SubmissionLower.R6966ProofNativeGraphExceptional
import ProximityPrize.SubmissionLower.R6966ProofNonlinearMarkDegrees
import ProximityPrize.SubmissionLower.R6966ProofPhysicalHelperTariff
import ProximityPrize.SubmissionLower.R6966ProofNativeWitnessBank
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0575
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowMoment1
import ProximityPrize.SubmissionLower.R6966ProofSpreadInterval
import ProximityPrize.SubmissionLower.Z6969Pack0559
import ProximityPrize.SubmissionLower.R6966ProofHelperWeightCap
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineTariff
import ProximityPrize.SubmissionLower.R6960HelperSourceArithmetic
import ProximityPrize.SubmissionLower.R6960HelperPrefix

set_option Elab.async false

-- merged module Z6969Pack0588
section Merged_Z6969Pack0588

-- Source: Research6969.GraphIntersection
section Z6969Source0656
set_option autoImplicit true
namespace Research6969.GraphIntersection
noncomputable section
open Polynomial
open K1_14 (FX Seeds Equation)
open K1_14_3 (SeedField)
open Research6966
open NativeGraphExceptional (den rhs)
open PadeNativeQuotient (Native)
open NonlinearMarkDegrees (cap)

/-- Common solutions of two slope-linear equations lie on this ordinate equation. -/
def determinant {g h:Pade.Row SeedField} (a:Native g) (b:Native h) : Equation :=
  den a*rhs b-den b*rhs a

theorem vanishes {g h:Pade.Row SeedField} (a:Native g) (b:Native h)
    {K:Type*} [Field K] (ev:Equation→+*K) (velocity:K)
    (left:ev (den a)*velocity=ev (rhs a)) (right:ev (den b)*velocity=ev (rhs b)) :
    ev (determinant a b)=0 := by
  rw [determinant,map_sub,map_mul,map_mul,←left,←right]
  ring

/-- When the determinant is identically zero, a regular mark on the second
graph satisfies the original helper, even if its first denominator vanishes. -/
theorem propagates {g h:Pade.Row SeedField} (a:Native g) (b:Native h)
    (same:determinant a b=0) {K:Type*} [Field K] (ev:Equation→+*K) (v:K)
    (regular:ev (den b)≠0) (law:ev (den b)*v=ev (rhs b)) :
    ev (den a)*v=ev (rhs a) := by
  have id:=congrArg ev same
  rw [determinant,map_sub,map_zero,sub_eq_zero,map_mul,map_mul,←law] at id
  apply mul_left_cancel₀ regular
  calc ev (den b)*(ev (den a)*v)=ev (den a)*(ev (den b)*v) := by ring
    _ = _ := id

private theorem product_cap {w:Fin 2→ℕ} {v u:ℕ} {A B:Equation}
    (a:cap w v A) (b:cap w u B):cap w (v+u) (A*B) := by
  intro i
  rw [coeff_mul]
  exact Submodule.sum_mem _ (fun ij _=>MvPolynomial.mul_mem_restrictWeightAtMost (a ij.1) (b ij.2))

theorem bounds {g h:Pade.Row SeedField} (a:Native g) (b:Native h)
    (ga:g.primitive) (hb:h.primitive) (gp:0<g.graphDegree) (hp:0<h.graphDegree)
    (w:Fin 2→ℕ) (u v:ℕ) (aD:cap w u (den a)) (aB:cap w u (rhs a))
    (bD:cap w v (den b)) (bB:cap w v (rhs b)) :
    (determinant a b).natDegree≤g.graphDegree+h.graphDegree-1 ∧
      cap w (u+v) (determinant a b) := by
  obtain ⟨d₁,y₁⟩:=NativeGraphMarks.equation_degrees a ga
  obtain ⟨d₂,y₂⟩:=NativeGraphMarks.equation_degrees b hb
  change (den a).natDegree≤_ at d₁
  change (den b).natDegree≤_ at d₂
  change (rhs a).natDegree≤_ at y₁
  change (rhs b).natDegree≤_ at y₂
  constructor
  · apply (natDegree_sub_le ..).trans (max_le _ _)
    · exact (natDegree_mul_le.trans (Nat.add_le_add d₁ y₂)).trans (by omega)
    · exact (natDegree_mul_le.trans (Nat.add_le_add d₂ y₁)).trans (by omega)
  · intro i
    rw [determinant,coeff_sub]
    exact Submodule.sub_mem _ (product_cap aD bB i) (Nat.add_comm v u ▸ product_cap bD aB i)

end
end Research6969.GraphIntersection
end Z6969Source0656

-- Source: Research6969.HelperGraph
section Z6969Source0657
set_option autoImplicit true
namespace Research6969.HelperGraph
noncomputable section
open K1_14 (Seeds Jet Equation)
open K1_14_1_4 (doubleMap)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_mul seedDegree_mul)
open K1_14_3 (SeedField SeedClosure fibreRow)
open Research6966
open NativeGraphExceptional (den rhs)
open PadeNativeQuotient (Native)
open Polynomial
open scoped Polynomial
set_option maxHeartbeats 950000
set_option maxRecDepth 7000

/-- Every actual slope-one prime in the helper prefix has a native model
for its own rational graph, including nonlinear ordinate dependence. -/
theorem of_prime {H:Jet} (prime:Prime H) (slope:H.natDegree=1) :
    ∃ (G:Pade.Row SeedField) (N:Native G),G.primitive ∧ N.poly=H ∧ G.graphDegree=jetDegree H := by
  let N:=PhysicalHelperTariff.realization prime slope
  have gp:=(PhysicalHelperTariff.primitive prime slope)
  exact ⟨PhysicalHelperTariff.graphOf H,N,gp,rfl,(HelperWeightCap.native_degree N gp).symm⟩

/-- A zero graph determinant identifies both primitive integer representatives
up to a unit, and therefore identifies the two measured native degrees. -/
theorem associated_of_zero {G H:Pade.Row SeedField} (A:Native G) (B:Native H)
    (ga:G.primitive) (hb:H.primitive) (zero:GraphIntersection.determinant A B=0):
    Associated A.poly B.poly := by
  classical
  let _:=UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let _:=UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  letI : UniqueFactorizationMonoid Jet:=Polynomial.uniqueFactorizationMonoid (D:=Equation)
  have equal:den A*rhs B=den B*rhs A:=sub_eq_zero.mp zero
  have cross:C (den B)*A.poly=C (den A)*B.poly:=by
    rw [←NativeProjectedWitness.graph_eq A ga,←NativeProjectedWitness.graph_eq B hb]
    have same:=congrArg (fun x:Equation=>C x:Equation→Jet) equal
    simp only [map_mul] at same
    linear_combination same
  have ir:=NativeWitnessBank.irreducible A ga
  have mult:A.poly∣C (den A)*B.poly:=cross ▸ dvd_mul_left A.poly _
  have d:A.poly∣B.poly:=ir.prime.dvd_or_dvd mult |>.resolve_left (by
    intro dv
    have le:=natDegree_le_of_dvd dv (C_ne_zero.mpr (NativeGraphExceptional.den_ne A ga))
    rw [NativeGraphMarks.slope_degree A ga,natDegree_C] at le
    omega)
  exact ir.associated_of_dvd (NativeWitnessBank.irreducible B hb) d

theorem same_degrees {G H:Pade.Row SeedField} (A:Native G) (B:Native H)
    (ga:G.primitive) (hb:H.primitive) (zero:GraphIntersection.determinant A B=0):
    G.graphDegree=H.graphDegree ∧ seedDegree A.poly=seedDegree B.poly := by
  have assoc:=associated_of_zero A B ga hb zero
  have mono {x y:Jet} (nz:y≠0) (div:x∣y):jetDegree x≤jetDegree y ∧ seedDegree x≤seedDegree y:=by
    obtain ⟨z,eq⟩:=div
    have ne:x*z≠0:=eq ▸ nz
    rw [eq,jetDegree_mul (left_ne_zero_of_mul ne) (right_ne_zero_of_mul ne),
      seedDegree_mul (left_ne_zero_of_mul ne) (right_ne_zero_of_mul ne)]
    omega
  obtain ⟨y1,z1⟩:=mono B.primitive.ne_zero assoc.dvd
  obtain ⟨y2,z2⟩:=mono A.primitive.ne_zero assoc.symm.dvd
  rw [←HelperWeightCap.native_degree A ga,←HelperWeightCap.native_degree B hb]
  exact ⟨Nat.le_antisymm y1 y2,Nat.le_antisymm z1 z2⟩


theorem same_mark {G H:Pade.Row SeedField} (A:Native G) (B:Native H) (ga:G.primitive)
    (hb:H.primitive) (zero:GraphIntersection.determinant A B=0)
    {F:Type*} [Field F] (eval:Jet→+*F) : eval A.poly=0 ↔ eval B.poly=0 := by
  have same:=associated_of_zero A B ga hb zero
  constructor
  · intro h
    exact zero_dvd_iff.mp (h ▸ _root_.map_dvd eval same.dvd)
  · intro h
    exact zero_dvd_iff.mp (h ▸ _root_.map_dvd eval same.symm.dvd)

end
end Research6969.HelperGraph
end Z6969Source0657

-- Source: Research6969.JointClosure
section Z6969Source0658
set_option autoImplicit true
namespace Research6969.JointClosure
noncomputable section
open Finset Polynomial
open K1 (K p)
open K1_14 (Equation FX Jet Seeds graphEval atX jetAt)
open K1_14_2 (Ambient toJet)
open K1_14_2_2 (Active mass)
open K1_14_3 (Surface Parent SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open NativeSurfaceCount (label)
open JointLedger (Book Pass)
open JointRouted (seedWeight ordWeight)
open scoped Classical Differential
set_option maxRecDepth 9000
set_option maxHeartbeats 1600000

theorem bounded {u del} {M:P1.ModelAt 33755 u del} {Γ:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (hi:M.overhead.toNat≤2557) (paid:Finset K) (A B:Finset Surface) (mainGeo:∀q∈A,Parent q) (rescueGeo:∀q∈B,Parent q)
    (mainSources rescueSources:Finset (Ideal Ambient)) (ma:∀Q∈mainSources,Active Q) (ra:∀Q∈rescueSources,Active Q)
    (mo:∀q∈A,∃Q∈mainSources,q.asIdeal=Q.comap toJet) (ro:∀q∈B,∃Q∈rescueSources,q.asIdeal=Q.comap toJet)
    (m r:Book) (wm wr:Fin 4→ℕ) (m0:m.ordinateCredit=wm 0) (m12:m.seedCredit=wm 1+wm 2)
    (r0:r.ordinateCredit=wr 0) (r12:r.seedCredit=wr 1+wr 2)
    (paidCap:paid.card+(∑k,wm k*mass mainSources k)+(∑k,wr k*mass rescueSources k)≤m.fee+r.fee)
    (sizeM:mass mainSources 1≤m.seedMass) (sizeR:mass rescueSources 1≤r.seedMass)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {degree U limit:ℕ} (pos:0<U) (dp:0<degree) (phys:131071+M.overhead≤(degree:ℤ))
    (gap:degree<179730) (tame:degree<p) (width:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (cover:∀ z∈Γ,z∈paid ∨ (∃q∈A,∀P∈q.asIdeal,jetAt P (M.label z) (F.scalar z)=0) ∨
      ((evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
        evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N)) ∧
       evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0 ∧
       ∃q∈B,∀P∈q.asIdeal,jetAt P (M.label z) (F.scalar z)=0))
    {maxDegree:ℕ} (allowed:maxDegree<64) {h:Equation} (union:JointProjection.Product (A∪B) h) (grade:h.natDegree≤maxDegree)
    (guardM:(2*maxDegree-1)*m.seedMass<p) (guardR:(2*maxDegree-1)*r.seedMass<p)
    (table:∀ i j:Fin (maxDegree+1),i.val+j.val≤maxDegree→Pass m r (seedWeight degree U)
      (ordWeight degree (G.graphDegree-1)) limit i.val j.val) : Γ.card≤limit := by
  classical
  obtain ⟨f,main⟩:=JointProjection.exists_product A mainGeo
  obtain ⟨g,rescue⟩:=JointProjection.exists_product B rescueGeo
  let S:=Γ\paid
  have sub:S⊆Γ:=sdiff_subset
  have mainSeed:=((JointProjection.measures main mainSources ma mo).2).trans sizeM
  have rescueSeed:=((JointProjection.measures rescue rescueSources ra ro).2).trans sizeR
  have details z (hz:z∈S) (miss:jetAt (C f) (M.label z) (F.scalar z)≠0) :
      (evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
        evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N)) ∧
        evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0 := by
    rcases (cover z (sub hz)).resolve_left (mem_sdiff.mp hz).2 with ⟨q,hq,mark⟩ | ⟨law,reg,_⟩
    · exact (miss (mark _ (main.vanishes hq))).elim
    · exact ⟨law,reg⟩
  have owners z (hz:z∈S) : ∃q∈A∪B,∀P∈q.asIdeal,jetAt P (M.label z) (F.scalar z)=0:=by
    rcases (cover z (sub hz)).resolve_left (mem_sdiff.mp hz).2 with ⟨q,hq,mark⟩|⟨_,_,q,hq,mark⟩
    · exact ⟨q,mem_union_left _ hq,mark⟩
    · exact ⟨q,mem_union_right _ hq,mark⟩
  have coef:2*h.natDegree-1≤2*maxDegree-1:=by omega
  obtain ⟨j,w,sum,jcap,wcap,count⟩:=JointRouted.invoice_optional F sub hi main rescue union N gp nonlinear pos dp phys
    gap tame width (by omega) ((Nat.mul_le_mul coef mainSeed).trans_lt guardM)
    ((Nat.mul_le_mul coef rescueSeed).trans_lt guardR) owners
    (fun z hz miss=>(details z hz miss).1) (fun z hz miss=>(details z hz miss).2)
  have cm:=JointProjection.credit main mainSources ma mo wm (e:=f.natDegree) (v:=K1_14_4.seedDegree f) le_rfl le_rfl
  have cr:=JointProjection.credit rescue rescueSources ra ro wr jcap wcap
  rw [←m0,←m12] at cm
  rw [←r0,←r12] at cr
  have fair:=table ⟨f.natDegree,by omega⟩ ⟨j,by omega⟩ (by simpa using sum.trans_le grade)
  apply JointLedger.consume m r (i:=f.natDegree) (j:=j) (v:=K1_14_4.seedDegree f) (w:=w) (paid:=paid.card)
    (surviving:=S.card) card_le_card_sdiff_add_card _ count mainSeed (wcap.trans rescueSeed) fair
  omega

theorem small {u del} {M:P1.ModelAt 33755 u del} {Γ:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (hi:M.overhead.toNat≤2557) (paid:Finset K) (A B:Finset Surface) (mainGeo:∀q∈A,Parent q) (rescueGeo:∀q∈B,Parent q)
    (mainSources rescueSources:Finset (Ideal Ambient)) (ma:∀Q∈mainSources,Active Q) (ra:∀Q∈rescueSources,Active Q)
    (mo:∀q∈A,∃Q∈mainSources,q.asIdeal=Q.comap toJet) (ro:∀q∈B,∃Q∈rescueSources,q.asIdeal=Q.comap toJet)
    (m r:Book) (wm wr:Fin 4→ℕ) (m0:m.ordinateCredit=wm 0) (m12:m.seedCredit=wm 1+wm 2)
    (r0:r.ordinateCredit=wr 0) (r12:r.seedCredit=wr 1+wr 2)
    (paidCap:paid.card+(∑k,wm k*mass mainSources k)+(∑k,wr k*mass rescueSources k)≤m.fee+r.fee)
    (sizeM:mass mainSources 1≤m.seedMass) (sizeR:mass rescueSources 1≤r.seedMass)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {degree U limit:ℕ} (pos:0<U) (dp:0<degree) (phys:131071+M.overhead≤(degree:ℤ))
    (gap:degree<179730) (tame:degree<p) (width:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (cover:∀ z∈Γ,z∈paid ∨ (∃q∈A,∀P∈q.asIdeal,jetAt P (M.label z) (F.scalar z)=0) ∨
      ((evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
        evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N)) ∧
       evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0 ∧
       ∃q∈B,∀P∈q.asIdeal,jetAt P (M.label z) (F.scalar z)=0))
    {h:Equation} (union:JointProjection.Product (A∪B) h) (grade:h.natDegree≤21)
    (guardM:41*m.seedMass<p) (guardR:41*r.seedMass<p)
    (table:∀ i j:Fin 22,i.val+j.val≤21→Pass m r (seedWeight degree U)
      (ordWeight degree (G.graphDegree-1)) limit i.val j.val) : Γ.card≤limit :=
  bounded F hi paid A B mainGeo rescueGeo mainSources rescueSources ma ra mo ro m r wm wr m0 m12 r0 r12 paidCap
    sizeM sizeR N gp nonlinear pos dp phys gap tame width cover (maxDegree:=21) (by decide)
    union grade guardM guardR table


end
end Research6969.JointClosure
end Z6969Source0658

-- Source: Research6969.PrefixEarlySettlement
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
open Prefix6969Rescue (graphShape regular)
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

-- Source: Research6969.SpreadMoment
section Z6969Source0660
set_option autoImplicit true
namespace Research6969.SpreadMomentProof
open Research6966.HelperWindowMoments (Block packedBlock Checked grouped_from_blocks)
set_option maxRecDepth 12000
set_option maxHeartbeats 0

theorem moment4184_900 : P1_7_1.groupedPoleMoment 4184 900 ≤ 8370437628682 :=
  _root_.PoleAffine6970.certified 4184 900 8370437628682 (by decide) (by decide +kernel)

end Research6969.SpreadMomentProof
end Z6969Source0660

-- Source: Research6969.SpreadRanks
section Z6969Source0661
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
open K1_14 (Shape)
def shape : Shape := ⟨3000, 4184, 900, 530820⟩
def box : Fin 2 → ℕ := ![265410, 265410]
def nodes : ℕ := 808165480857600
def moment : ℕ := 8370437628682

theorem node_eq : P1_7_1.nodeRows shape = nodes := by
  have rank := P1_7_1_2.six_nodeRows shape (by decide) (by decide)
  have closed : 262144*P1_7_1_2.sixPerNode (shape.m-2*shape.J) shape.J = 6*nodes := by decide
  rw [closed] at rank
  omega

theorem pole_cap : P1_7_1.groupedPoleMoment shape.B shape.J ≤ moment :=
  Research6969.SpreadMomentProof.moment4184_900

end Research6969.SpreadCatalogue
end Z6969Source0661

-- Source: Research6969.SpreadEdges
section ShiftedSpreadEdges
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem shiftedEdge64_3_55_2314_2365_cost : SpreadInterval.costSum shape 179730 64 3 55 2314 2365 ≤ 1332030853 := by
  decide +kernel

theorem shiftedEdge64_3_55_2314_2365 : SpreadInterval.Positive shape 179730 64 3 55 nodes moment 2314 2365 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_3_55_2314_2365_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_3_55_2366_2557_cost : SpreadInterval.costSum shape 179730 64 3 55 2366 2557 ≤ 1334585080 := by
  decide +kernel

theorem shiftedEdge64_3_55_2366_2557 : SpreadInterval.Positive shape 179730 64 3 55 nodes moment 2366 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_3_55_2366_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_32_41_2314_2465_cost : SpreadInterval.costSum shape 179730 41 32 41 2314 2465 ≤ 1332035192 := by
  decide +kernel

theorem shiftedEdge41_32_41_2314_2465 : SpreadInterval.Positive shape 179730 41 32 41 nodes moment 2314 2465 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_32_41_2314_2465_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_32_41_2466_2557_cost : SpreadInterval.costSum shape 179730 41 32 41 2466 2557 ≤ 1331936362 := by
  decide +kernel

theorem shiftedEdge41_32_41_2466_2557 : SpreadInterval.Positive shape 179730 41 32 41 nodes moment 2466 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_32_41_2466_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge22_7_20_2314_2557_cost : SpreadInterval.costSum shape 179730 22 7 20 2314 2557 ≤ 1312164065 := by
  decide +kernel

theorem shiftedEdge22_7_20_2314_2557 : SpreadInterval.Positive shape 179730 22 7 20 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge22_7_20_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge22_8_21_2314_2557_cost : SpreadInterval.costSum shape 179730 22 8 21 2314 2557 ≤ 1273824428 := by
  decide +kernel

theorem shiftedEdge22_8_21_2314_2557 : SpreadInterval.Positive shape 179730 22 8 21 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge22_8_21_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge22_9_22_2314_2557_cost : SpreadInterval.costSum shape 179730 22 9 22 2314 2557 ≤ 1246105497 := by
  decide +kernel

theorem shiftedEdge22_9_22_2314_2557 : SpreadInterval.Positive shape 179730 22 9 22 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge22_9_22_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge22_12_22_2314_2557_cost : SpreadInterval.costSum shape 179730 22 12 22 2314 2557 ≤ 1297640081 := by
  decide +kernel

theorem shiftedEdge22_12_22_2314_2557 : SpreadInterval.Positive shape 179730 22 12 22 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge22_12_22_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge22_13_22_2314_2557_cost : SpreadInterval.costSum shape 179730 22 13 22 2314 2557 ≤ 1328207456 := by
  decide +kernel

theorem shiftedEdge22_13_22_2314_2557 : SpreadInterval.Positive shape 179730 22 13 22 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge22_13_22_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge23_7_21_2314_2557_cost : SpreadInterval.costSum shape 179730 23 7 21 2314 2557 ≤ 1286340623 := by
  decide +kernel

theorem shiftedEdge23_7_21_2314_2557 : SpreadInterval.Positive shape 179730 23 7 21 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge23_7_21_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge23_8_22_2314_2557_cost : SpreadInterval.costSum shape 179730 23 8 22 2314 2557 ≤ 1247167331 := by
  decide +kernel

theorem shiftedEdge23_8_22_2314_2557 : SpreadInterval.Positive shape 179730 23 8 22 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge23_8_22_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge23_9_23_2314_2557_cost : SpreadInterval.costSum shape 179730 23 9 23 2314 2557 ≤ 1218878502 := by
  decide +kernel

theorem shiftedEdge23_9_23_2314_2557 : SpreadInterval.Positive shape 179730 23 9 23 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge23_9_23_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge23_12_23_2314_2557_cost : SpreadInterval.costSum shape 179730 23 12 23 2314 2557 ≤ 1262217557 := by
  decide +kernel

theorem shiftedEdge23_12_23_2314_2557 : SpreadInterval.Positive shape 179730 23 12 23 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge23_12_23_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge23_13_23_2314_2557_cost : SpreadInterval.costSum shape 179730 23 13 23 2314 2557 ≤ 1290009672 := by
  decide +kernel

theorem shiftedEdge23_13_23_2314_2557 : SpreadInterval.Positive shape 179730 23 13 23 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge23_13_23_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge23_14_23_2314_2557_cost : SpreadInterval.costSum shape 179730 23 14 23 2314 2557 ≤ 1322392455 := by
  decide +kernel

theorem shiftedEdge23_14_23_2314_2557 : SpreadInterval.Positive shape 179730 23 14 23 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge23_14_23_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_6_22_2314_2557_cost : SpreadInterval.costSum shape 179730 25 6 22 2314 2557 ≤ 1297292490 := by
  decide +kernel

theorem shiftedEdge25_6_22_2314_2557 : SpreadInterval.Positive shape 179730 25 6 22 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_6_22_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_7_23_2314_2557_cost : SpreadInterval.costSum shape 179730 25 7 23 2314 2557 ≤ 1241268569 := by
  decide +kernel

theorem shiftedEdge25_7_23_2314_2557 : SpreadInterval.Positive shape 179730 25 7 23 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_7_23_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_8_24_2314_2557_cost : SpreadInterval.costSum shape 179730 25 8 24 2314 2557 ≤ 1200450253 := by
  decide +kernel

theorem shiftedEdge25_8_24_2314_2557 : SpreadInterval.Positive shape 179730 25 8 24 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_8_24_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_9_25_2314_2557_cost : SpreadInterval.costSum shape 179730 25 9 25 2314 2557 ≤ 1170948237 := by
  decide +kernel

theorem shiftedEdge25_9_25_2314_2557 : SpreadInterval.Positive shape 179730 25 9 25 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_9_25_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_13_25_2314_2557_cost : SpreadInterval.costSum shape 179730 25 13 25 2314 2557 ≤ 1222763867 := by
  decide +kernel

theorem shiftedEdge25_13_25_2314_2557 : SpreadInterval.Positive shape 179730 25 13 25 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_13_25_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_14_25_2314_2557_cost : SpreadInterval.costSum shape 179730 25 14 25 2314 2557 ≤ 1250238025 := by
  decide +kernel

theorem shiftedEdge25_14_25_2314_2557 : SpreadInterval.Positive shape 179730 25 14 25 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_14_25_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_15_25_2314_2557_cost : SpreadInterval.costSum shape 179730 25 15 25 2314 2557 ≤ 1281462886 := by
  decide +kernel

theorem shiftedEdge25_15_25_2314_2557 : SpreadInterval.Positive shape 179730 25 15 25 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_15_25_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge25_16_25_2314_2557_cost : SpreadInterval.costSum shape 179730 25 16 25 2314 2557 ≤ 1315790611 := by
  decide +kernel

theorem shiftedEdge25_16_25_2314_2557 : SpreadInterval.Positive shape 179730 25 16 25 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge25_16_25_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_5_24_2314_2557_cost : SpreadInterval.costSum shape 179730 28 5 24 2314 2557 ≤ 1322888802 := by
  decide +kernel

theorem shiftedEdge28_5_24_2314_2557 : SpreadInterval.Positive shape 179730 28 5 24 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_5_24_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_6_25_2314_2557_cost : SpreadInterval.costSum shape 179730 28 6 25 2314 2557 ≤ 1245221918 := by
  decide +kernel

theorem shiftedEdge28_6_25_2314_2557 : SpreadInterval.Positive shape 179730 28 6 25 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_6_25_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_7_26_2314_2557_cost : SpreadInterval.costSum shape 179730 28 7 26 2314 2557 ≤ 1186410855 := by
  decide +kernel

theorem shiftedEdge28_7_26_2314_2557 : SpreadInterval.Positive shape 179730 28 7 26 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_7_26_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_8_27_2314_2557_cost : SpreadInterval.costSum shape 179730 28 8 27 2314 2557 ≤ 1143245881 := by
  decide +kernel

theorem shiftedEdge28_8_27_2314_2557 : SpreadInterval.Positive shape 179730 28 8 27 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_8_27_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_9_28_2314_2557_cost : SpreadInterval.costSum shape 179730 28 9 28 2314 2557 ≤ 1111874088 := by
  decide +kernel

theorem shiftedEdge28_9_28_2314_2557 : SpreadInterval.Positive shape 179730 28 9 28 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_9_28_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_15_28_2314_2557_cost : SpreadInterval.costSum shape 179730 28 15 28 2314 2557 ≤ 1186449899 := by
  decide +kernel

theorem shiftedEdge28_15_28_2314_2557 : SpreadInterval.Positive shape 179730 28 15 28 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_15_28_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_16_28_2314_2557_cost : SpreadInterval.costSum shape 179730 28 16 28 2314 2557 ≤ 1214684284 := by
  decide +kernel

theorem shiftedEdge28_16_28_2314_2557 : SpreadInterval.Positive shape 179730 28 16 28 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_16_28_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_17_28_2314_2557_cost : SpreadInterval.costSum shape 179730 28 17 28 2314 2557 ≤ 1245526749 := by
  decide +kernel

theorem shiftedEdge28_17_28_2314_2557 : SpreadInterval.Positive shape 179730 28 17 28 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_17_28_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_18_28_2314_2557_cost : SpreadInterval.costSum shape 179730 28 18 28 2314 2557 ≤ 1278564610 := by
  decide +kernel

theorem shiftedEdge28_18_28_2314_2557 : SpreadInterval.Positive shape 179730 28 18 28 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_18_28_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge28_19_28_2314_2557_cost : SpreadInterval.costSum shape 179730 28 19 28 2314 2557 ≤ 1313456441 := by
  decide +kernel

theorem shiftedEdge28_19_28_2314_2557 : SpreadInterval.Positive shape 179730 28 19 28 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge28_19_28_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_5_29_2314_2557_cost : SpreadInterval.costSum shape 179730 33 5 29 2314 2557 ≤ 1262780135 := by
  decide +kernel

theorem shiftedEdge33_5_29_2314_2557 : SpreadInterval.Positive shape 179730 33 5 29 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_5_29_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_6_30_2314_2557_cost : SpreadInterval.costSum shape 179730 33 6 30 2314 2557 ≤ 1180970615 := by
  decide +kernel

theorem shiftedEdge33_6_30_2314_2557 : SpreadInterval.Positive shape 179730 33 6 30 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_6_30_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_7_31_2314_2557_cost : SpreadInterval.costSum shape 179730 33 7 31 2314 2557 ≤ 1118233856 := by
  decide +kernel

theorem shiftedEdge33_7_31_2314_2557 : SpreadInterval.Positive shape 179730 33 7 31 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_7_31_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_8_32_2314_2557_cost : SpreadInterval.costSum shape 179730 33 8 32 2314 2557 ≤ 1071588587 := by
  decide +kernel

theorem shiftedEdge33_8_32_2314_2557 : SpreadInterval.Positive shape 179730 33 8 32 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_8_32_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_9_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 9 33 2314 2557 ≤ 1037253701 := by
  decide +kernel

theorem shiftedEdge33_9_33_2314_2557 : SpreadInterval.Positive shape 179730 33 9 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_9_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_17_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 17 33 2314 2557 ≤ 1110076546 := by
  decide +kernel

theorem shiftedEdge33_17_33_2314_2557 : SpreadInterval.Positive shape 179730 33 17 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_17_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_18_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 18 33 2314 2557 ≤ 1135381626 := by
  decide +kernel

theorem shiftedEdge33_18_33_2314_2557 : SpreadInterval.Positive shape 179730 33 18 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_18_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_19_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 19 33 2314 2557 ≤ 1162528627 := by
  decide +kernel

theorem shiftedEdge33_19_33_2314_2557 : SpreadInterval.Positive shape 179730 33 19 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_19_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_20_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 20 33 2314 2557 ≤ 1191296719 := by
  decide +kernel

theorem shiftedEdge33_20_33_2314_2557 : SpreadInterval.Positive shape 179730 33 20 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_20_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_21_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 21 33 2314 2557 ≤ 1221465956 := by
  decide +kernel

theorem shiftedEdge33_21_33_2314_2557 : SpreadInterval.Positive shape 179730 33 21 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_21_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_22_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 22 33 2314 2557 ≤ 1252818162 := by
  decide +kernel

theorem shiftedEdge33_22_33_2314_2557 : SpreadInterval.Positive shape 179730 33 22 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_22_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_23_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 23 33 2314 2557 ≤ 1285252778 := by
  decide +kernel

theorem shiftedEdge33_23_33_2314_2557 : SpreadInterval.Positive shape 179730 33 23 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_23_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge33_24_33_2314_2557_cost : SpreadInterval.costSum shape 179730 33 24 33 2314 2557 ≤ 1318661007 := by
  decide +kernel

theorem shiftedEdge33_24_33_2314_2557 : SpreadInterval.Positive shape 179730 33 24 33 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge33_24_33_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_4_36_2314_2557_cost : SpreadInterval.costSum shape 179730 41 4 36 2314 2557 ≤ 1299827724 := by
  decide +kernel

theorem shiftedEdge41_4_36_2314_2557 : SpreadInterval.Positive shape 179730 41 4 36 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_4_36_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_5_37_2314_2557_cost : SpreadInterval.costSum shape 179730 41 5 37 2314 2557 ≤ 1199451341 := by
  decide +kernel

theorem shiftedEdge41_5_37_2314_2557 : SpreadInterval.Positive shape 179730 41 5 37 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_5_37_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_6_38_2314_2557_cost : SpreadInterval.costSum shape 179730 41 6 38 2314 2557 ≤ 1112728944 := by
  decide +kernel

theorem shiftedEdge41_6_38_2314_2557 : SpreadInterval.Positive shape 179730 41 6 38 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_6_38_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_7_39_2314_2557_cost : SpreadInterval.costSum shape 179730 41 7 39 2314 2557 ≤ 1045162012 := by
  decide +kernel

theorem shiftedEdge41_7_39_2314_2557 : SpreadInterval.Positive shape 179730 41 7 39 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_7_39_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_8_40_2314_2557_cost : SpreadInterval.costSum shape 179730 41 8 40 2314 2557 ≤ 994038473 := by
  decide +kernel

theorem shiftedEdge41_8_40_2314_2557 : SpreadInterval.Positive shape 179730 41 8 40 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_8_40_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_9_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 9 41 2314 2557 ≤ 955681019 := by
  decide +kernel

theorem shiftedEdge41_9_41_2314_2557 : SpreadInterval.Positive shape 179730 41 9 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_9_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_21_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 21 41 2314 2557 ≤ 1039450555 := by
  decide +kernel

theorem shiftedEdge41_21_41_2314_2557 : SpreadInterval.Positive shape 179730 41 21 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_21_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_22_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 22 41 2314 2557 ≤ 1062298489 := by
  decide +kernel

theorem shiftedEdge41_22_41_2314_2557 : SpreadInterval.Positive shape 179730 41 22 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_22_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_23_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 23 41 2314 2557 ≤ 1086221088 := by
  decide +kernel

theorem shiftedEdge41_23_41_2314_2557 : SpreadInterval.Positive shape 179730 41 23 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_23_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_24_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 24 41 2314 2557 ≤ 1111104928 := by
  decide +kernel

theorem shiftedEdge41_24_41_2314_2557 : SpreadInterval.Positive shape 179730 41 24 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_24_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_25_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 25 41 2314 2557 ≤ 1136779691 := by
  decide +kernel

theorem shiftedEdge41_25_41_2314_2557 : SpreadInterval.Positive shape 179730 41 25 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_25_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_26_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 26 41 2314 2557 ≤ 1163164122 := by
  decide +kernel

theorem shiftedEdge41_26_41_2314_2557 : SpreadInterval.Positive shape 179730 41 26 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_26_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_27_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 27 41 2314 2557 ≤ 1190237236 := by
  decide +kernel

theorem shiftedEdge41_27_41_2314_2557 : SpreadInterval.Positive shape 179730 41 27 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_27_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_28_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 28 41 2314 2557 ≤ 1217920889 := by
  decide +kernel

theorem shiftedEdge41_28_41_2314_2557 : SpreadInterval.Positive shape 179730 41 28 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_28_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_29_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 29 41 2314 2557 ≤ 1246109263 := by
  decide +kernel

theorem shiftedEdge41_29_41_2314_2557 : SpreadInterval.Positive shape 179730 41 29 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_29_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_30_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 30 41 2314 2557 ≤ 1274786937 := by
  decide +kernel

theorem shiftedEdge41_30_41_2314_2557 : SpreadInterval.Positive shape 179730 41 30 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_30_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge41_31_41_2314_2557_cost : SpreadInterval.costSum shape 179730 41 31 41 2314 2557 ≤ 1303914895 := by
  decide +kernel

theorem shiftedEdge41_31_41_2314_2557 : SpreadInterval.Positive shape 179730 41 31 41 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge41_31_41_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_4_44_2314_2557_cost : SpreadInterval.costSum shape 179730 50 4 44 2314 2557 ≤ 1261417620 := by
  decide +kernel

theorem shiftedEdge50_4_44_2314_2557 : SpreadInterval.Positive shape 179730 50 4 44 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_4_44_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_5_45_2314_2557_cost : SpreadInterval.costSum shape 179730 50 5 45 2314 2557 ≤ 1157989697 := by
  decide +kernel

theorem shiftedEdge50_5_45_2314_2557 : SpreadInterval.Positive shape 179730 50 5 45 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_5_45_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_6_46_2314_2557_cost : SpreadInterval.costSum shape 179730 50 6 46 2314 2557 ≤ 1067736781 := by
  decide +kernel

theorem shiftedEdge50_6_46_2314_2557 : SpreadInterval.Positive shape 179730 50 6 46 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_6_46_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_7_47_2314_2557_cost : SpreadInterval.costSum shape 179730 50 7 47 2314 2557 ≤ 996611726 := by
  decide +kernel

theorem shiftedEdge50_7_47_2314_2557 : SpreadInterval.Positive shape 179730 50 7 47 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_7_47_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_8_48_2314_2557_cost : SpreadInterval.costSum shape 179730 50 8 48 2314 2557 ≤ 942093193 := by
  decide +kernel

theorem shiftedEdge50_8_48_2314_2557 : SpreadInterval.Positive shape 179730 50 8 48 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_8_48_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_9_49_2314_2557_cost : SpreadInterval.costSum shape 179730 50 9 49 2314 2557 ≤ 900587937 := by
  decide +kernel

theorem shiftedEdge50_9_49_2314_2557 : SpreadInterval.Positive shape 179730 50 9 49 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_9_49_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_10_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 10 50 2314 2557 ≤ 869059923 := by
  decide +kernel

theorem shiftedEdge50_10_50_2314_2557 : SpreadInterval.Positive shape 179730 50 10 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_10_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_26_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 26 50 2314 2557 ≤ 996262108 := by
  decide +kernel

theorem shiftedEdge50_26_50_2314_2557 : SpreadInterval.Positive shape 179730 50 26 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_26_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_27_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 27 50 2314 2557 ≤ 1016991272 := by
  decide +kernel

theorem shiftedEdge50_27_50_2314_2557 : SpreadInterval.Positive shape 179730 50 27 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_27_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_28_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 28 50 2314 2557 ≤ 1038317124 := by
  decide +kernel

theorem shiftedEdge50_28_50_2314_2557 : SpreadInterval.Positive shape 179730 50 28 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_28_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_29_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 29 50 2314 2557 ≤ 1060162609 := by
  decide +kernel

theorem shiftedEdge50_29_50_2314_2557 : SpreadInterval.Positive shape 179730 50 29 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_29_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_30_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 30 50 2314 2557 ≤ 1082489504 := by
  decide +kernel

theorem shiftedEdge50_30_50_2314_2557 : SpreadInterval.Positive shape 179730 50 30 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_30_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_31_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 31 50 2314 2557 ≤ 1105258991 := by
  decide +kernel

theorem shiftedEdge50_31_50_2314_2557 : SpreadInterval.Positive shape 179730 50 31 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_31_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_32_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 32 50 2314 2557 ≤ 1128399304 := by
  decide +kernel

theorem shiftedEdge50_32_50_2314_2557 : SpreadInterval.Positive shape 179730 50 32 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_32_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_33_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 33 50 2314 2557 ≤ 1151925694 := by
  decide +kernel

theorem shiftedEdge50_33_50_2314_2557 : SpreadInterval.Positive shape 179730 50 33 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_33_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_34_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 34 50 2314 2557 ≤ 1175741089 := by
  decide +kernel

theorem shiftedEdge50_34_50_2314_2557 : SpreadInterval.Positive shape 179730 50 34 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_34_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_35_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 35 50 2314 2557 ≤ 1199927292 := by
  decide +kernel

theorem shiftedEdge50_35_50_2314_2557 : SpreadInterval.Positive shape 179730 50 35 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_35_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_36_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 36 50 2314 2557 ≤ 1224301794 := by
  decide +kernel

theorem shiftedEdge50_36_50_2314_2557 : SpreadInterval.Positive shape 179730 50 36 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_36_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_37_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 37 50 2314 2557 ≤ 1249038030 := by
  decide +kernel

theorem shiftedEdge50_37_50_2314_2557 : SpreadInterval.Positive shape 179730 50 37 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_37_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_38_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 38 50 2314 2557 ≤ 1273883800 := by
  decide +kernel

theorem shiftedEdge50_38_50_2314_2557 : SpreadInterval.Positive shape 179730 50 38 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_38_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_39_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 39 50 2314 2557 ≤ 1299135625 := by
  decide +kernel

theorem shiftedEdge50_39_50_2314_2557 : SpreadInterval.Positive shape 179730 50 39 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_39_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge50_40_50_2314_2557_cost : SpreadInterval.costSum shape 179730 50 40 50 2314 2557 ≤ 1324593148 := by
  decide +kernel

theorem shiftedEdge50_40_50_2314_2557 : SpreadInterval.Positive shape 179730 50 40 50 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge50_40_50_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_4_56_2314_2557_cost : SpreadInterval.costSum shape 179730 64 4 56 2314 2557 ≤ 1224153024 := by
  decide +kernel

theorem shiftedEdge64_4_56_2314_2557 : SpreadInterval.Positive shape 179730 64 4 56 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_4_56_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_5_57_2314_2557_cost : SpreadInterval.costSum shape 179730 64 5 57 2314 2557 ≤ 1117478645 := by
  decide +kernel

theorem shiftedEdge64_5_57_2314_2557 : SpreadInterval.Positive shape 179730 64 5 57 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_5_57_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_6_58_2314_2557_cost : SpreadInterval.costSum shape 179730 64 6 58 2314 2557 ≤ 1023447056 := by
  decide +kernel

theorem shiftedEdge64_6_58_2314_2557 : SpreadInterval.Positive shape 179730 64 6 58 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_6_58_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_7_59_2314_2557_cost : SpreadInterval.costSum shape 179730 64 7 59 2314 2557 ≤ 948450676 := by
  decide +kernel

theorem shiftedEdge64_7_59_2314_2557 : SpreadInterval.Positive shape 179730 64 7 59 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_7_59_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_8_60_2314_2557_cost : SpreadInterval.costSum shape 179730 64 8 60 2314 2557 ≤ 890159690 := by
  decide +kernel

theorem shiftedEdge64_8_60_2314_2557 : SpreadInterval.Positive shape 179730 64 8 60 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_8_60_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_9_61_2314_2557_cost : SpreadInterval.costSum shape 179730 64 9 61 2314 2557 ≤ 845061620 := by
  decide +kernel

theorem shiftedEdge64_9_61_2314_2557 : SpreadInterval.Positive shape 179730 64 9 61 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_9_61_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_10_62_2314_2557_cost : SpreadInterval.costSum shape 179730 64 10 62 2314 2557 ≤ 810161919 := by
  decide +kernel

theorem shiftedEdge64_10_62_2314_2557 : SpreadInterval.Positive shape 179730 64 10 62 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_10_62_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_11_63_2314_2557_cost : SpreadInterval.costSum shape 179730 64 11 63 2314 2557 ≤ 783152583 := by
  decide +kernel

theorem shiftedEdge64_11_63_2314_2557 : SpreadInterval.Positive shape 179730 64 11 63 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_11_63_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_12_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 12 64 2314 2557 ≤ 762292643 := by
  decide +kernel

theorem shiftedEdge64_12_64_2314_2557 : SpreadInterval.Positive shape 179730 64 12 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_12_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_33_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 33 64 2314 2557 ≤ 941086276 := by
  decide +kernel

theorem shiftedEdge64_33_64_2314_2557 : SpreadInterval.Positive shape 179730 64 33 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_33_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_34_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 34 64 2314 2557 ≤ 958545082 := by
  decide +kernel

theorem shiftedEdge64_34_64_2314_2557 : SpreadInterval.Positive shape 179730 64 34 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_34_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_35_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 35 64 2314 2557 ≤ 976384639 := by
  decide +kernel

theorem shiftedEdge64_35_64_2314_2557 : SpreadInterval.Positive shape 179730 64 35 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_35_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_36_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 36 64 2314 2557 ≤ 994415396 := by
  decide +kernel

theorem shiftedEdge64_36_64_2314_2557 : SpreadInterval.Positive shape 179730 64 36 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_36_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_37_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 37 64 2314 2557 ≤ 1012800696 := by
  decide +kernel

theorem shiftedEdge64_37_64_2314_2557 : SpreadInterval.Positive shape 179730 64 37 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_37_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_38_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 38 64 2314 2557 ≤ 1031284250 := by
  decide +kernel

theorem shiftedEdge64_38_64_2314_2557 : SpreadInterval.Positive shape 179730 64 38 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_38_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_39_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 39 64 2314 2557 ≤ 1050174977 := by
  decide +kernel

theorem shiftedEdge64_39_64_2314_2557 : SpreadInterval.Positive shape 179730 64 39 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_39_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_40_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 40 64 2314 2557 ≤ 1069291209 := by
  decide +kernel

theorem shiftedEdge64_40_64_2314_2557 : SpreadInterval.Positive shape 179730 64 40 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_40_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_41_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 41 64 2314 2557 ≤ 1088372573 := by
  decide +kernel

theorem shiftedEdge64_41_64_2314_2557 : SpreadInterval.Positive shape 179730 64 41 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_41_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_42_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 42 64 2314 2557 ≤ 1107910328 := by
  decide +kernel

theorem shiftedEdge64_42_64_2314_2557 : SpreadInterval.Positive shape 179730 64 42 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_42_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_43_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 43 64 2314 2557 ≤ 1127360199 := by
  decide +kernel

theorem shiftedEdge64_43_64_2314_2557 : SpreadInterval.Positive shape 179730 64 43 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_43_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_44_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 44 64 2314 2557 ≤ 1146887018 := by
  decide +kernel

theorem shiftedEdge64_44_64_2314_2557 : SpreadInterval.Positive shape 179730 64 44 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_44_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_45_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 45 64 2314 2557 ≤ 1166548277 := by
  decide +kernel

theorem shiftedEdge64_45_64_2314_2557 : SpreadInterval.Positive shape 179730 64 45 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_45_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_46_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 46 64 2314 2557 ≤ 1186804889 := by
  decide +kernel

theorem shiftedEdge64_46_64_2314_2557 : SpreadInterval.Positive shape 179730 64 46 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_46_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_47_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 47 64 2314 2557 ≤ 1206701038 := by
  decide +kernel

theorem shiftedEdge64_47_64_2314_2557 : SpreadInterval.Positive shape 179730 64 47 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_47_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_48_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 48 64 2314 2557 ≤ 1227139818 := by
  decide +kernel

theorem shiftedEdge64_48_64_2314_2557 : SpreadInterval.Positive shape 179730 64 48 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_48_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_49_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 49 64 2314 2557 ≤ 1247466932 := by
  decide +kernel

theorem shiftedEdge64_49_64_2314_2557 : SpreadInterval.Positive shape 179730 64 49 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_49_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_50_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 50 64 2314 2557 ≤ 1268156280 := by
  decide +kernel

theorem shiftedEdge64_50_64_2314_2557 : SpreadInterval.Positive shape 179730 64 50 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_50_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_51_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 51 64 2314 2557 ≤ 1288123883 := by
  decide +kernel

theorem shiftedEdge64_51_64_2314_2557 : SpreadInterval.Positive shape 179730 64 51 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_51_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

private theorem shiftedEdge64_52_64_2314_2557_cost : SpreadInterval.costSum shape 179730 64 52 64 2314 2557 ≤ 1309119787 := by
  decide +kernel

theorem shiftedEdge64_52_64_2314_2557 : SpreadInterval.Positive shape 179730 64 52 64 nodes moment 2314 2557 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ shiftedEdge64_52_64_2314_2557_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end ShiftedSpreadEdges

end Merged_Z6969Pack0588

-- merged module Z6969Pack0589
section Merged_Z6969Pack0589

-- Source: Research6969.SpreadCatalogue
section Z6969Source0675
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxHeartbeats 1200000

theorem case22_7_20 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 22 7 20 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge22_7_20_2314_2557

theorem case22_8_21 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 22 8 21 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge22_8_21_2314_2557

theorem case22_9_22 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 22 9 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge22_9_22_2314_2557

theorem case22_12_22 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 22 12 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge22_12_22_2314_2557

theorem case22_13_22 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 22 13 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge22_13_22_2314_2557

theorem case23_7_21 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 23 7 21 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge23_7_21_2314_2557

theorem case23_8_22 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 23 8 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge23_8_22_2314_2557

theorem case23_9_23 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 23 9 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge23_9_23_2314_2557

theorem case23_12_23 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 23 12 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge23_12_23_2314_2557

theorem case23_13_23 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 23 13 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge23_13_23_2314_2557

theorem case23_14_23 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 23 14 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge23_14_23_2314_2557

theorem case25_6_22 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 6 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_6_22_2314_2557

theorem case25_7_23 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 7 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_7_23_2314_2557

theorem case25_8_24 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 8 24 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_8_24_2314_2557

theorem case25_9_25 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 9 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_9_25_2314_2557

theorem case25_13_25 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 13 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_13_25_2314_2557

theorem case25_14_25 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 14 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_14_25_2314_2557

theorem case25_15_25 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 15 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_15_25_2314_2557

theorem case25_16_25 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 25 16 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge25_16_25_2314_2557

theorem case28_5_24 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 5 24 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_5_24_2314_2557

theorem case28_6_25 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 6 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_6_25_2314_2557

theorem case28_7_26 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 7 26 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_7_26_2314_2557

theorem case28_8_27 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 8 27 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_8_27_2314_2557

theorem case28_9_28 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 9 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_9_28_2314_2557

theorem case28_15_28 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 15 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_15_28_2314_2557

theorem case28_16_28 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 16 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_16_28_2314_2557

theorem case28_17_28 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 17 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_17_28_2314_2557

theorem case28_18_28 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 18 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_18_28_2314_2557

theorem case28_19_28 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 28 19 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge28_19_28_2314_2557

theorem case33_5_29 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 5 29 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_5_29_2314_2557

theorem case33_6_30 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 6 30 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_6_30_2314_2557

theorem case33_7_31 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 7 31 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_7_31_2314_2557

theorem case33_8_32 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 8 32 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_8_32_2314_2557

theorem case33_9_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 9 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_9_33_2314_2557

theorem case33_17_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 17 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_17_33_2314_2557

theorem case33_18_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 18 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_18_33_2314_2557

theorem case33_19_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 19 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_19_33_2314_2557

theorem case33_20_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 20 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_20_33_2314_2557

theorem case33_21_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 21 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_21_33_2314_2557

theorem case33_22_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 22 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_22_33_2314_2557

theorem case33_23_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 23 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_23_33_2314_2557

theorem case33_24_33 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 33 24 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge33_24_33_2314_2557

theorem case41_4_36 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 4 36 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_4_36_2314_2557

theorem case41_5_37 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 5 37 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_5_37_2314_2557

theorem case41_6_38 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 6 38 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_6_38_2314_2557

theorem case41_7_39 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 7 39 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_7_39_2314_2557

theorem case41_8_40 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 8 40 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_8_40_2314_2557

theorem case41_9_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 9 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_9_41_2314_2557

theorem case41_21_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 21 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_21_41_2314_2557

theorem case41_22_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 22 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_22_41_2314_2557

theorem case41_23_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 23 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_23_41_2314_2557

theorem case41_24_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 24 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_24_41_2314_2557

theorem case41_25_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 25 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_25_41_2314_2557

theorem case41_26_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 26 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_26_41_2314_2557

theorem case41_27_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 27 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_27_41_2314_2557

theorem case41_28_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 28 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_28_41_2314_2557

theorem case41_29_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 29 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_29_41_2314_2557

theorem case41_30_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 30 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_30_41_2314_2557

theorem case41_31_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 31 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_31_41_2314_2557

theorem case41_32_41 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 41 32 41 shape box nodes moment := by
  by_cases bound : h ≤ 2465
  · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_32_41_2314_2465
  · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge41_32_41_2466_2557

theorem case50_4_44 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 4 44 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_4_44_2314_2557

theorem case50_5_45 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 5 45 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_5_45_2314_2557

theorem case50_6_46 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 6 46 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_6_46_2314_2557

theorem case50_7_47 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 7 47 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_7_47_2314_2557

theorem case50_8_48 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 8 48 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_8_48_2314_2557

theorem case50_9_49 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 9 49 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_9_49_2314_2557

theorem case50_10_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 10 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_10_50_2314_2557

theorem case50_26_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 26 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_26_50_2314_2557

theorem case50_27_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 27 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_27_50_2314_2557

theorem case50_28_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 28 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_28_50_2314_2557

theorem case50_29_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 29 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_29_50_2314_2557

theorem case50_30_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 30 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_30_50_2314_2557

theorem case50_31_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 31 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_31_50_2314_2557

theorem case50_32_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 32 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_32_50_2314_2557

theorem case50_33_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 33 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_33_50_2314_2557

theorem case50_34_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 34 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_34_50_2314_2557

theorem case50_35_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 35 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_35_50_2314_2557

theorem case50_36_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 36 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_36_50_2314_2557

theorem case50_37_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 37 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_37_50_2314_2557

theorem case50_38_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 38 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_38_50_2314_2557

theorem case50_39_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 39 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_39_50_2314_2557

theorem case50_40_50 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 50 40 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge50_40_50_2314_2557

theorem case64_3_55 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 3 55 shape box nodes moment := by
  by_cases bound : h ≤ 2365
  · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_3_55_2314_2365
  · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_3_55_2366_2557

theorem case64_4_56 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 4 56 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_4_56_2314_2557

theorem case64_5_57 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 5 57 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_5_57_2314_2557

theorem case64_6_58 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 6 58 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_6_58_2314_2557

theorem case64_7_59 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 7 59 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_7_59_2314_2557

theorem case64_8_60 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 8 60 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_8_60_2314_2557

theorem case64_9_61 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 9 61 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_9_61_2314_2557

theorem case64_10_62 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 10 62 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_10_62_2314_2557

theorem case64_11_63 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 11 63 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_11_63_2314_2557

theorem case64_12_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 12 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_12_64_2314_2557

theorem case64_33_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 33 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_33_64_2314_2557

theorem case64_34_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 34 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_34_64_2314_2557

theorem case64_35_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 35 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_35_64_2314_2557

theorem case64_36_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 36 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_36_64_2314_2557

theorem case64_37_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 37 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_37_64_2314_2557

theorem case64_38_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 38 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_38_64_2314_2557

theorem case64_39_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 39 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_39_64_2314_2557

theorem case64_40_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 40 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_40_64_2314_2557

theorem case64_41_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 41 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_41_64_2314_2557

theorem case64_42_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 42 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_42_64_2314_2557

theorem case64_43_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 43 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_43_64_2314_2557

theorem case64_44_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 44 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_44_64_2314_2557

theorem case64_45_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 45 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_45_64_2314_2557

theorem case64_46_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 46 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_46_64_2314_2557

theorem case64_47_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 47 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_47_64_2314_2557

theorem case64_48_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 48 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_48_64_2314_2557

theorem case64_49_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 49 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_49_64_2314_2557

theorem case64_50_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 50 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_50_64_2314_2557

theorem case64_51_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 51 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_51_64_2314_2557

theorem case64_52_64 {h : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557) :
    PadeCutoff.excluded 179730 h 64 52 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) shiftedEdge64_52_64_2314_2557

theorem partial22 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 6 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179730 h 22 a (22-9+a) shape box nodes moment := by
  interval_cases a
  · exact case22_7_20 lo hi
  · exact case22_8_21 lo hi
  · exact case22_9_22 lo hi

theorem full22 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 12 ≤ a) (aHi : a ≤ 13) :
    PadeCutoff.excluded 179730 h 22 a 22 shape box nodes moment := by
  interval_cases a
  · exact case22_12_22 lo hi
  · exact case22_13_22 lo hi

theorem partial23 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 6 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179730 h 23 a (23-9+a) shape box nodes moment := by
  interval_cases a
  · exact case23_7_21 lo hi
  · exact case23_8_22 lo hi
  · exact case23_9_23 lo hi

theorem full23 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 12 ≤ a) (aHi : a ≤ 14) :
    PadeCutoff.excluded 179730 h 23 a 23 shape box nodes moment := by
  interval_cases a
  · exact case23_12_23 lo hi
  · exact case23_13_23 lo hi
  · exact case23_14_23 lo hi

theorem partial25 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 5 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179730 h 25 a (25-9+a) shape box nodes moment := by
  interval_cases a
  · exact case25_6_22 lo hi
  · exact case25_7_23 lo hi
  · exact case25_8_24 lo hi
  · exact case25_9_25 lo hi

theorem full25 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 13 ≤ a) (aHi : a ≤ 16) :
    PadeCutoff.excluded 179730 h 25 a 25 shape box nodes moment := by
  interval_cases a
  · exact case25_13_25 lo hi
  · exact case25_14_25 lo hi
  · exact case25_15_25 lo hi
  · exact case25_16_25 lo hi

theorem partial28 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 4 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179730 h 28 a (28-9+a) shape box nodes moment := by
  interval_cases a
  · exact case28_5_24 lo hi
  · exact case28_6_25 lo hi
  · exact case28_7_26 lo hi
  · exact case28_8_27 lo hi
  · exact case28_9_28 lo hi

theorem full28 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 15 ≤ a) (aHi : a ≤ 19) :
    PadeCutoff.excluded 179730 h 28 a 28 shape box nodes moment := by
  interval_cases a
  · exact case28_15_28 lo hi
  · exact case28_16_28 lo hi
  · exact case28_17_28 lo hi
  · exact case28_18_28 lo hi
  · exact case28_19_28 lo hi

theorem partial33 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 4 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179730 h 33 a (33-9+a) shape box nodes moment := by
  interval_cases a
  · exact case33_5_29 lo hi
  · exact case33_6_30 lo hi
  · exact case33_7_31 lo hi
  · exact case33_8_32 lo hi
  · exact case33_9_33 lo hi

theorem full33 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 17 ≤ a) (aHi : a ≤ 24) :
    PadeCutoff.excluded 179730 h 33 a 33 shape box nodes moment := by
  interval_cases a
  · exact case33_17_33 lo hi
  · exact case33_18_33 lo hi
  · exact case33_19_33 lo hi
  · exact case33_20_33 lo hi
  · exact case33_21_33 lo hi
  · exact case33_22_33 lo hi
  · exact case33_23_33 lo hi
  · exact case33_24_33 lo hi

theorem partial41 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 3 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179730 h 41 a (41-9+a) shape box nodes moment := by
  interval_cases a
  · exact case41_4_36 lo hi
  · exact case41_5_37 lo hi
  · exact case41_6_38 lo hi
  · exact case41_7_39 lo hi
  · exact case41_8_40 lo hi
  · exact case41_9_41 lo hi

theorem full41 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 21 ≤ a) (aHi : a ≤ 32) :
    PadeCutoff.excluded 179730 h 41 a 41 shape box nodes moment := by
  interval_cases a
  · exact case41_21_41 lo hi
  · exact case41_22_41 lo hi
  · exact case41_23_41 lo hi
  · exact case41_24_41 lo hi
  · exact case41_25_41 lo hi
  · exact case41_26_41 lo hi
  · exact case41_27_41 lo hi
  · exact case41_28_41 lo hi
  · exact case41_29_41 lo hi
  · exact case41_30_41 lo hi
  · exact case41_31_41 lo hi
  · exact case41_32_41 lo hi

theorem partial50 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 3 < a) (aHi : a ≤ 10) :
    PadeCutoff.excluded 179730 h 50 a (50-10+a) shape box nodes moment := by
  interval_cases a
  · exact case50_4_44 lo hi
  · exact case50_5_45 lo hi
  · exact case50_6_46 lo hi
  · exact case50_7_47 lo hi
  · exact case50_8_48 lo hi
  · exact case50_9_49 lo hi
  · exact case50_10_50 lo hi

theorem full50 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 26 ≤ a) (aHi : a ≤ 40) :
    PadeCutoff.excluded 179730 h 50 a 50 shape box nodes moment := by
  interval_cases a
  · exact case50_26_50 lo hi
  · exact case50_27_50 lo hi
  · exact case50_28_50 lo hi
  · exact case50_29_50 lo hi
  · exact case50_30_50 lo hi
  · exact case50_31_50 lo hi
  · exact case50_32_50 lo hi
  · exact case50_33_50 lo hi
  · exact case50_34_50 lo hi
  · exact case50_35_50 lo hi
  · exact case50_36_50 lo hi
  · exact case50_37_50 lo hi
  · exact case50_38_50 lo hi
  · exact case50_39_50 lo hi
  · exact case50_40_50 lo hi

theorem partial64 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 2 < a) (aHi : a ≤ 12) :
    PadeCutoff.excluded 179730 h 64 a (64-12+a) shape box nodes moment := by
  interval_cases a
  · exact case64_3_55 lo hi
  · exact case64_4_56 lo hi
  · exact case64_5_57 lo hi
  · exact case64_6_58 lo hi
  · exact case64_7_59 lo hi
  · exact case64_8_60 lo hi
  · exact case64_9_61 lo hi
  · exact case64_10_62 lo hi
  · exact case64_11_63 lo hi
  · exact case64_12_64 lo hi

theorem full64 {h a : ℕ} (lo : 2314 ≤ h) (hi : h ≤ 2557)
    (aLo : 33 ≤ a) (aHi : a ≤ 52) :
    PadeCutoff.excluded 179730 h 64 a 64 shape box nodes moment := by
  interval_cases a
  · exact case64_33_64 lo hi
  · exact case64_34_64 lo hi
  · exact case64_35_64 lo hi
  · exact case64_36_64 lo hi
  · exact case64_37_64 lo hi
  · exact case64_38_64 lo hi
  · exact case64_39_64 lo hi
  · exact case64_40_64 lo hi
  · exact case64_41_64 lo hi
  · exact case64_42_64 lo hi
  · exact case64_43_64 lo hi
  · exact case64_44_64 lo hi
  · exact case64_45_64 lo hi
  · exact case64_46_64 lo hi
  · exact case64_47_64 lo hi
  · exact case64_48_64 lo hi
  · exact case64_49_64 lo hi
  · exact case64_50_64 lo hi
  · exact case64_51_64 lo hi
  · exact case64_52_64 lo hi

end Research6969.SpreadCatalogue
end Z6969Source0675

-- Source: Research6969.PrefixEarlyPacket
section Z6969Source0676
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace Lower6960.Prefix6969Early
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet Equation jetAt)
open K1_14_1 (PoleData CRTLift evaluated MarkResidues nodeL)
open K1_14_2 (Ambient toJet UsesSeed)
open K1_14_2_2 (Active RowCaps mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open Far6969RescueGeometry (Model Family OnSurface word)
open Prefix6969Main (Pricing Band)
open Prefix6969Rescue (EarlyPrice graphShape)
open Research6969 Research6966
open scoped Classical BigOperators

/-- Terminal input for an early event's own invoice. The main book keeps
the whole projected degree and both available seed-credit columns. -/
structure Packet {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (fee ord seed e v : ℕ) where
  paid : Finset K
  parents : Finset Surface
  projected : Equation
  project : JointProjection.Product parents projected
  geo : ∀ q∈parents,Parent q
  terminal : ∀ q∈parents,TerminalBanks.Pass Crt (word M) 179730 Research6969.SpreadCatalogue.shape q
  degree_cap : projected.natDegree ≤ e
  seed_cap : K1_14_4.seedDegree projected ≤ v
  bill : paid.card+ord*projected.natDegree+seed*K1_14_4.seedDegree projected≤fee
  cover : ∀ z∈Γ,z∈paid ∨ ∃q∈parents,OnSurface F q z

private theorem cap_nat {n k : ℕ} {q : ℚ}
    (cap : (n : ℚ) ≤ q) (rounded : q < (k : ℚ)+1) : n ≤ k := by
  apply Nat.le_of_lt_succ
  exact_mod_cast cap.trans_lt rounded

structure Exit where
  mDegree : ℕ
  mWidth : ℕ
  rDegree : ℕ
  rWidth : ℕ
  marked : Bool

def Exit.extra (x : Exit) (band : Band) (rp : EarlyPrice) : ℕ :=
  let d := 131071+band.last
  if x.marked then
    (JointLedger.coefficient x.rDegree-rp.credit 1)*x.rWidth+2*x.rDegree^2
  else
    (JointRouted.seedWeight d rp.seed^2-rp.credit 0)*x.rDegree+
    (2*JointRouted.seedWeight d rp.seed*JointRouted.ordWeight d (rp.degree-1)-rp.credit 1)*x.rWidth

structure Exit.Valid (x : Exit) (main : Prefix6969Main.Plan)
    (rescue : Prefix6969Rescue.Plan) (rp : EarlyPrice) : Prop where
  mDegree : main.history main.last 0 < (x.mDegree : ℚ)+1
  mWidth : main.history main.last 1 < (x.mWidth : ℚ)+1
  rDegree : rescue.history rp.stop 0 < (x.rDegree : ℚ)+1
  rWidth : rescue.history rp.stop 1 < (x.rWidth : ℚ)+1
  tame : x.marked=true → x.rDegree<64 ∧ (2*x.rDegree-1)*x.rWidth<p

theorem settle {u del} {M : Model u del} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    {main : Prefix6969Main.Plan} {mp : Pricing} {band : Band}
    (mainValid : main.Valid) (mainPrice : mp.Valid main band)
    {first extra a low floor : ℕ} {outer : P1_7.Bank}
    (mainSource : main.Sources first band.last outer extra a low floor)
    {rescue : Prefix6969Rescue.Plan} {rp : EarlyPrice}
    (rescueSource : rescue.Sources first band.last) (rescuePrice : rp.Valid rescue band)
    (x : Exit) (checks : x.Valid main rescue rp) (firstPositive : 0<first)
    (lo : first ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ band.last)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    {G : Jet} (phys : HelperPhysicalModel.Model Crt G) (prime : Prime G)
    (slope : G.natDegree = 1) (seeded : UsesSeed G) (caps : RowCaps G rescue.primeShape)
    (known : PrefixRows.Common (evaluated Crt (word M) outer.shape
      (HelperSource.cutoffCount outer.shape 179730 M.overhead.toNat 10-1)) G)
    (nonlinear : 2 ≤ jetDegree G)
    (mainDegree : a ≤ jetDegree G) (mainSeed : low ≤ seedDegree G)
    (mainFloor : floor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw)
    (rescueDegree : rescue.degree ≤ jetDegree G) (rescueSeed : rescue.seedFloor ≤ seedDegree G)
    (rescueFloor : rescue.physicalFloor ≤ RawPhysicalDegree.weight (131071-M.overhead.toNat)
      (131071-M.overhead.toNat-1) phys.raw) :
    Nonempty (Packet F Crt (mp.fee+rp.fee+x.extra band rp) (mp.retainedCredit 0)
      (mp.retainedCredit 1+mp.retainedCredit 2) x.mDegree x.mWidth) := by
  obtain ⟨R,J,Q,B,paid,A,S,_,pay,ms,rs,mg,mo,rg,covered⟩ :=
    Prefix6969Pair.produce F Crt mainValid mainPrice mainSource rescueSource rescuePrice firstPositive
      lo hi noPole residues phys prime slope seeded caps known mainDegree mainSeed mainFloor
      rescueDegree rescueSeed rescueFloor
  have ma (P) (mem : P∈J.final) : Active P := (J.kept_geom (mem_filter.mp mem).1).1
  have ra (P) (mem : P∈B.final) : Active P :=
    (Q.parent_geom (Prefix6969Rescue.Invoice.Book.final_initial B mem)).1
  let T := Γ.filter (fun γ => jetAt G (M.label γ) (F.scalar γ)=0 ∧
    Prefix6969Rescue.regular G (M.label γ) (F.scalar γ) ∧ ∃q∈S,OnSurface F q γ)
  have tr : T⊆Γ := filter_subset _ _
  have rgeo : ∀ q∈S,Parent q := fun q h => (rg q h).1
  have rorigin : ∀ q∈S,∃P∈B.final,q.asIdeal=P.comap toJet := fun q h => (rg q h).2.2
  have ton : ∀γ∈T,∃q∈S,OnSurface F q γ := fun _ h => (mem_filter.mp h).2.2.2
  have rd := cap_nat (rs 0) checks.rDegree
  have rw := cap_nat (rs 1) checks.rWidth
  have hiAll : M.overhead.toNat≤2557 := hi.trans (by cases band <;> decide)
  have exit : T.card ≤ Prefix6969Rescue.Invoice.charge B rp.credit+x.extra band rp := by
    cases hm : x.marked
    · have cc : RowCaps G (graphShape rp.degree rp.seed) := rescuePrice.graph_shape ▸ caps
      have ph : 131071+M.overhead≤((131071+band.last:ℕ):ℤ) := by
        push_cast
        omega
      simpa only [Exit.extra,hm,Bool.false_eq_true,ite_false,Prefix6969Rescue.Invoice.charge,add_assoc] using
        graph_exit F tr prime slope nonlinear rescuePrice.seed_pos cc ph
          (by cases band <;> decide) (by cases band <;> decide) (by cases band <;> decide)
          rgeo B.final ra rorigin ton
          (fun _ h => (mem_filter.mp h).2.1) (fun _ h => (mem_filter.mp h).2.2.1) rp.credit rd rw
    · obtain ⟨small,char⟩ := checks.tame hm
      simpa only [Exit.extra,hm,ite_true,Prefix6969Rescue.Invoice.charge,add_assoc] using
        marked_exit F tr hiAll rgeo B.final ra rorigin ton rp.credit rd rw small char
  obtain ⟨f,project⟩ := JointProjection.exists_product A (fun q h => (mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have credit := JointProjection.credit project J.final ma mo mp.retainedCredit
    (e:=f.natDegree) (v:=K1_14_4.seedDegree f) le_rfl le_rfl
  change _ ≤ mp.charge J.final at credit
  refine ⟨⟨paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    measures.1.trans (cap_nat (ms 0) checks.mDegree),
    measures.2.trans (cap_nat (ms 1) checks.mWidth),?_,?_⟩⟩
  · have union := card_union_le paid T
    omega
  · intro γ mem
    rcases covered γ mem with taken|⟨_,q,hq,on⟩|resc
    · exact Or.inl (mem_union_left _ taken)
    · exact Or.inr ⟨q,hq,on⟩
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem,resc⟩))

end
end Lower6960.Prefix6969Early
end Z6969Source0676

-- Source: Research6969.PrefixNearOuter
section Z6969Source0677
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000

namespace Lower6960.Prefix6969NearOuter
noncomputable section

open Finset Polynomial
open K1_14 (Jet)
open K1_14_1 (PoleData CRTLift MarkResidues evaluated nodeL)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open Far6969RescueGeometry (Model Family word)
open Research6966

/-- Split using the actual outer prefix, and derive the native physical
baseline of every nontrivial exception at the near endpoint. -/
theorem split {u deleted} {M : Model u deleted} {Γ} (F : Family M Γ)
    {D : PoleData M.overhead.toNat} (Crt : CRTLift D)
    (lo : 2314 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ)) :
    ∃ R : Prefix6969Wide.Rows F Crt, R.out.exception = 1 ∨
      ∃ phys : HelperPhysicalModel.Model Crt R.out.exception,
        PrefixRows.Common (evaluated Crt (word M) Prefix6969Helper.helperBank.shape
          (Prefix6969Helper.helperCutoff M.overhead.toNat)) R.out.exception ∧
        R.out.exception.natDegree = 1 ∧
        1 ≤ jetDegree R.out.exception ∧ jetDegree R.out.exception ≤ 7 ∧
        1 ≤ seedDegree R.out.exception ∧ seedDegree R.out.exception ≤ 61 ∧
        (2 ≤ jetDegree R.out.exception → seedDegree R.out.exception ≤ 56) ∧
        jetDegree R.out.exception * 128660 - 1 ≤ RawPhysicalDegree.weight
          (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw := by
  obtain ⟨R⟩ := Prefix6969Wide.rows F Crt lo hi noPole residues
  refine ⟨R, ?_⟩
  rcases R.out.kind with unit | common
  · exact Or.inl unit
  have hiAll : M.overhead.toNat ≤ 33755 := hi.trans (by decide)
  obtain ⟨line, jd, jmax, sd, smax, nonlinear⟩ :=
    Prefix6969Helper.helper_common_caps Crt (word M) lo hiAll
      common.1 common.2.2.1 common.2.1 common.2.2.2
  obtain ⟨phys⟩ := HelperPhysicalModel.exists_model Crt common.1 common.2.1
  have hraw : 0 < 131071-M.overhead.toNat := by omega
  have lower := HelperWeightCap.weight_lower phys common.1.ne_zero _ hraw
  have endpoint : 128660 ≤ 131071-M.overhead.toNat := by omega
  have m := Nat.mul_le_mul_left (jetDegree R.out.exception) endpoint
  rw [Nat.mul_comm (jetDegree R.out.exception) (131071-M.overhead.toNat)] at m
  rw [line] at lower
  exact Or.inr ⟨phys, common, line, jd, jmax, sd, smax, nonlinear, by omega⟩

end
end Lower6960.Prefix6969NearOuter
end Z6969Source0677

-- Source: Research6969.PrefixNearOrdinary
section Z6969Source0678
set_option autoImplicit true
set_option Elab.async false
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace Lower6960.Prefix6969NearOuter
noncomputable section

open Finset Polynomial
open K1 (K p)
open K1_14 (Jet jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues nodeL)
open K1_14_2 (toJet)
open K1_14_2_2 (Active mass)
open K1_14_2_2_2_1 (jetDegree seedDegree)
open K1_14_3 (Surface Parent)
open Far6969RescueGeometry (Model Family OnSurface word)
open Research6969 Research6966
open scoped Classical BigOperators Differential

abbrev affineFee : ℕ :=
  p*61+(3*(133482*61)^2*(262144-133482)^3)/(179730-133482)^3

private theorem affine_roots {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ) (hi : M.overhead.toNat≤2411)
    {G : Jet} (prime : Prime G) (slope : G.natDegree=1) (affine : jetDegree G=1)
    (width : seedDegree G≤61) (roots : ∀γ∈T,jetAt G (M.label γ) (F.scalar γ)=0) :
    T.card≤affineFee := by
  obtain ⟨graph,N,gp,eq,deg⟩ := HelperGraph.of_prime prime slope
  let ev (γ : K) := eval₂RingHom (eval₂RingHom (graphEval (M.label γ)) (atX (F.scalar γ)))
    (atX (F.scalar γ).derivative)
  let q (γ : K) : Surface := ⟨RingHom.ker (ev γ), RingHom.ker_isPrime _⟩
  have own : NativeAffineRows.Owned F T (T.image q) N := by
    intro z hz
    refine ⟨q z,mem_image.mpr ⟨z,hz,rfl⟩,?_,fun _ h=>h⟩
    rw [eq]
    exact roots z hz
  have cap j i : (N.poly.coeff j).coeff i ∈ MvPolynomial.restrictWeightAtMost (fun _=>1) 61 := by
    rw [eq]
    apply MvPolynomial.mem_restrictWeightAtMost.mpr
    intro m hm
    rw [←Finsupp.degree_eq_weight_one]
    exact (MvPolynomial.le_totalDegree hm).trans ((K1_14_2_2_2_1.seedDegree_le G 61).mp width j i)
  exact NativeAffineTariff.price_floor F sub N gp (deg.trans affine) 61 (by decide) cap
    (by decide) 133482 (by omega) (by decide) (by decide) (by decide) (by decide) own

/-- The refitted actual main packet transfers when the outer exception is
a unit or its affine zero marks have been paid. -/
theorem ordinary {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    (R : Prefix6969Wide.Rows F Crt)
    (hi : M.overhead.toNat≤2411)
    (noPole : ∀ j i, (D.block j).eval (nodeL i) ≠ 0)
    (residues : ∀ γ∈Γ, MarkResidues D (M.label γ) (F.scalar γ))
    (mode : R.out.exception=1 ∨ Prime R.out.exception ∧ R.out.exception.natDegree=1 ∧
      jetDegree R.out.exception=1 ∧ seedDegree R.out.exception≤61) :
    Nonempty (Prefix6969Early.Packet F Crt 234329630343844473 133994566145700 1590006772040 351 6143) := by
  obtain ⟨J,C,A,pay,ms,mg,mo,covered⟩:=R.main_prefix hi noPole residues
  let T := Γ.filter (fun γ=>jetAt R.out.exception (M.label γ) (F.scalar γ)=0)
  have affinePay : T.card≤affineFee := by
    rcases mode with unit | ⟨prime,slope,affine,width⟩
    · have empty : T=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro γ mem
        have root := (mem_filter.mp mem).2
        simpa [unit,jetAt] using root
      simp [empty]
    · exact affine_roots F (filter_subset _ _) hi prime slope affine width
        (fun _ h=>(mem_filter.mp h).2)
  have ma (P) (mem : P∈J.final) : Active P := (J.kept_geom (mem_filter.mp mem).1).1
  obtain ⟨f,project⟩ := JointProjection.exists_product A (fun q h => (mg q h).1)
  have measures := JointProjection.measures project J.final ma mo
  have md : mass J.final 0≤335 := by
    apply Nat.le_of_lt_succ
    have q := ms 0
    change (mass J.final 0:ℚ)≤459151/1369 at q
    exact_mod_cast q.trans_lt (by decide +kernel : (459151:ℚ)/1369<336)
  have mv : mass J.final 1≤5964 := by
    apply Nat.le_of_lt_succ
    have q := ms 1
    change (mass J.final 1:ℚ)≤16330489/2738 at q
    exact_mod_cast q.trans_lt (by decide +kernel : (16330489:ℚ)/2738<5965)
  let ordCredit : ℕ := 133994566145700
  let seedCredit : ℕ := 1590006772040
  let w := Prefix6969Wide.retainedCredit
  let adjust := (ordCredit-w 0)*335+(seedCredit-w 1)*5964
  have adj : ordCredit*f.natDegree+seedCredit*K1_14_4.seedDegree f ≤
      Prefix6969Wide.retainedCharge J.final+adjust := by
    have cov0 := Prefix6969Early.compensate ordCredit (w 0) (mass J.final 0) 335 md
    have cov1 := Prefix6969Early.compensate seedCredit (w 1) (mass J.final 1) 5964 mv
    have pr0 := Nat.mul_le_mul_left ordCredit measures.1
    have pr1 := Nat.mul_le_mul_left seedCredit measures.2
    unfold Prefix6969Wide.retainedCharge adjust
    change _ ≤ (∑k,w k*mass J.final k)+_
    simp only [Fin.sum_univ_four]
    omega
  have total : Prefix6969Wide.prefixCap+adjust+affineFee≤234329630343844473 := by decide +kernel
  refine ⟨⟨C.paid∪T,A,f,project,fun q h=>(mg q h).1,fun q h=>(mg q h).2,
    (measures.1.trans md).trans (by decide),(measures.2.trans mv).trans (by decide),?_,?_⟩⟩
  · have union := card_union_le C.paid T
    change (C.paid∪T).card+ordCredit*f.natDegree+seedCredit*K1_14_4.seedDegree f≤234329630343844473
    omega
  · intro γ mem
    by_cases root : jetAt R.out.exception (M.label γ) (F.scalar γ)=0
    · exact Or.inl (mem_union_right _ (mem_filter.mpr ⟨mem,root⟩))
    · rcases covered γ (mem_filter.mpr ⟨mem,root⟩) with paid | surface
      · exact Or.inl (mem_union_left _ paid)
      · exact Or.inr surface

end
end Lower6960.Prefix6969NearOuter
end Z6969Source0678

-- Source: Research6969.PrefixMiddleHelper
section Z6969Source0679
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
namespace Lower6960.Prefix6969MiddleHelper
open Research6969.TransitionArithmetic (value value_eq)
open Research6966.FarSourceArithmetic (Request)
open Research6969.TransitionBanks (bank154 rank154)
open HelperSource
open Finset Polynomial
open K1_14 (FX L Jet)
open K1_14_1 (PoleData CRTLift evaluated evaluated_mono evaluated_shape)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree jetDegree jetDegree_le)
open P1_7 (Bank debit)
abbrev bankAt (u : ℕ) : Bank := bank154 u
abbrev helperBank := bankAt 7384

theorem checked (u : ℕ) : P3_7_1.BankOK (bankAt u) := rank154 u

theorem helper_bank_checked : P3_7_1.BankOK helperBank := checked 7384

inductive HelperTest where
  | twoSlopes | seedBoundary | mixedBoundary | jetBoundary
def HelperTest.slope : HelperTest → ℕ
  | .twoSlopes => 2
  | _ => 1
def HelperTest.excess : HelperTest → ℕ
  | .mixedBoundary => 1
  | .jetBoundary => 7
  | _ => 0
def HelperTest.seed : HelperTest → ℕ
  | .seedBoundary => 62
  | .mixedBoundary => 57
  | _ => 1
abbrev HelperTest.cap (_ : HelperTest) : ℕ := 7384

private def helperRequest (test : HelperTest) : Request :=
  ⟨bankAt test.cap, 10, test.slope, test.excess, test.seed⟩

private abbrev compressedSurplus (h : ℕ) (test : HelperTest) : ℤ :=
  value (helperRequest test) h

private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) (hi : h ≤ 2413) :
    compressedSurplus h test = surplus (bankAt test.cap) 179730 h 10 test.slope test.excess test.seed :=
  value_eq (helperRequest test) h (by cases test <;> decide)
    (by change 170 < 131071 - h; omega)

private theorem twoSlopes_first : compressedSurplus 2412 .twoSlopes = 1986924652913403 := by decide +kernel
private theorem twoSlopes_next : compressedSurplus 2413 .twoSlopes = 2886931873436702 := by decide +kernel
private theorem seedBoundary_first : compressedSurplus 2412 .seedBoundary = 133523645759465726 := by decide +kernel
private theorem seedBoundary_next : compressedSurplus 2413 .seedBoundary = 134478186739129769 := by decide +kernel
private theorem mixedBoundary_first : compressedSurplus 2412 .mixedBoundary = 122520781449920547 := by decide +kernel
private theorem mixedBoundary_next : compressedSurplus 2413 .mixedBoundary = 123470761247888708 := by decide +kernel
private theorem jetBoundary_first : compressedSurplus 2412 .jetBoundary = 52443720744349203 := by decide +kernel
private theorem jetBoundary_next : compressedSurplus 2413 .jetBoundary = 53364647034562152 := by decide +kernel

theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2412≤h) (hi : h≤33755) :
    debit h (bankAt test.cap) < gain (bankAt test.cap).shape 179730 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2412 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq _ _ (by decide)]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus (bankAt test.cap) 179730 2412 10 test.slope test.excess test.seed ≤
      surplus (bankAt test.cap) 179730 2413 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq 2412 test (by decide), ← compressedSurplus_eq 2413 test (by decide)]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2412≤h) (hi : h≤33755) :
    WidthGuard helperBank 179730 h 10 :=
  width_at_height _ _ 2412 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179730 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2412≤h) (hi : h≤33755) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q := by
  obtain ⟨Q,inside,avoids⟩ := crt_avoiding_row Crt word (bankAt test.cap) 179730 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    (checked test.cap).nodes (checked test.cap).moment.1 (checked test.cap).moment.2
    (by cases test <;> decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
  exact ⟨Q, K1_14_1.evaluated_mono Crt word (s:=(bankAt test.cap).shape) (s':=helperBank.shape)
    rfl rfl rfl (by cases test <;> decide) le_rfl inside, avoids⟩
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2412≤h) (hi : h≤33755) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179730 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  exact nonzero_of_supply Crt word helperBank.shape _ (lt_of_le_of_lt (Nat.zero_le _) sup)
private theorem shape_lower_bound {G : Jet} (nz : G≠0) : G.natDegree≤jetDegree G := by
  have coeff : ((G.coeff G.natDegree).coeff G.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_natDegree,coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)
  have cap := (jetDegree_le G _).1 le_rfl _ _ coeff
  omega
theorem helper_common_caps {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2412≤h) (hi : h≤33755) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : 0<G.natDegree)
    (common : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q) :
    G.natDegree=1 ∧ 1≤jetDegree G ∧ jetDegree G≤7 ∧
      1≤seedDegree G ∧ seedDegree G≤61 ∧ (2≤jetDegree G → seedDegree G≤56) := by
  have sb : 1≤seedDegree G := by
    obtain ⟨j,i,hs⟩ := seeded
    have ge := (K1_14_2_2_2_1.seedDegree_le G _).1 le_rfl j i
    omega
  have jb := shape_lower_bound irr.ne_zero
  have not_test (test : HelperTest) (a : test.slope≤G.natDegree)
      (b : test.seed≤seedDegree G) (c : G.natDegree+test.excess≤jetDegree G) : False := by
    obtain ⟨Q,hQ,avoid⟩ := helper_avoids Crt word lo hi test irr seeded a b c
    exact avoid (common Q hQ)
  have linear : G.natDegree=1 := by
    by_contra! bad
    exact not_test .twoSlopes (by change 2≤G.natDegree; omega) sb (by simpa [HelperTest.excess] using jb)
  refine ⟨linear, by omega, ?_, sb, ?_, ?_⟩
  · by_contra! bad
    exact not_test .jetBoundary (by change 1≤G.natDegree; omega) sb
      (by change G.natDegree+7≤jetDegree G; omega)
  · by_contra! bad
    exact not_test .seedBoundary (by change 1≤G.natDegree; omega) (by change 62≤seedDegree G; omega)
      (by simpa [HelperTest.excess] using jb)
  · intro j
    by_contra! bad
    exact not_test .mixedBoundary (by change 1≤G.natDegree; omega) (by change 57≤seedDegree G; omega)
      (by change G.natDegree+1≤jetDegree G; omega)
theorem helper_not_two {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2412≤h) (hi : h≤33755) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179730 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179730 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
end Lower6960.Prefix6969MiddleHelper
end Z6969Source0679

end Merged_Z6969Pack0589
