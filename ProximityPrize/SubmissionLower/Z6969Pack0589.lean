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

theorem bounded {u del} {M:P1.ModelAt 33735 u del} {Γ:Finset K} (F:P1.FamilyAt 179740 M Γ)
    (hi:M.overhead.toNat≤2534) (paid:Finset K) (A B:Finset Surface) (mainGeo:∀q∈A,Parent q) (rescueGeo:∀q∈B,Parent q)
    (mainSources rescueSources:Finset (Ideal Ambient)) (ma:∀Q∈mainSources,Active Q) (ra:∀Q∈rescueSources,Active Q)
    (mo:∀q∈A,∃Q∈mainSources,q.asIdeal=Q.comap toJet) (ro:∀q∈B,∃Q∈rescueSources,q.asIdeal=Q.comap toJet)
    (m r:Book) (wm wr:Fin 4→ℕ) (m0:m.ordinateCredit=wm 0) (m12:m.seedCredit=wm 1+wm 2)
    (r0:r.ordinateCredit=wr 0) (r12:r.seedCredit=wr 1+wr 2)
    (paidCap:paid.card+(∑k,wm k*mass mainSources k)+(∑k,wr k*mass rescueSources k)≤m.fee+r.fee)
    (sizeM:mass mainSources 1≤m.seedMass) (sizeR:mass rescueSources 1≤r.seedMass)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {degree U limit:ℕ} (pos:0<U) (dp:0<degree) (phys:131071+M.overhead≤(degree:ℤ))
    (gap:degree<179740) (tame:degree<p) (width:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
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

theorem small {u del} {M:P1.ModelAt 33735 u del} {Γ:Finset K} (F:P1.FamilyAt 179740 M Γ)
    (hi:M.overhead.toNat≤2534) (paid:Finset K) (A B:Finset Surface) (mainGeo:∀q∈A,Parent q) (rescueGeo:∀q∈B,Parent q)
    (mainSources rescueSources:Finset (Ideal Ambient)) (ma:∀Q∈mainSources,Active Q) (ra:∀Q∈rescueSources,Active Q)
    (mo:∀q∈A,∃Q∈mainSources,q.asIdeal=Q.comap toJet) (ro:∀q∈B,∃Q∈rescueSources,q.asIdeal=Q.comap toJet)
    (m r:Book) (wm wr:Fin 4→ℕ) (m0:m.ordinateCredit=wm 0) (m12:m.seedCredit=wm 1+wm 2)
    (r0:r.ordinateCredit=wr 0) (r12:r.seedCredit=wr 1+wr 2)
    (paidCap:paid.card+(∑k,wm k*mass mainSources k)+(∑k,wr k*mass rescueSources k)≤m.fee+r.fee)
    (sizeM:mass mainSources 1≤m.seedMass) (sizeR:mass rescueSources 1≤r.seedMass)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {degree U limit:ℕ} (pos:0<U) (dp:0<degree) (phys:131071+M.overhead≤(degree:ℤ))
    (gap:degree<179740) (tame:degree<p) (width:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
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
    (physical : 131071+M.overhead≤(d:ℤ)) (dp : 0<d) (gap : d<179740) (tame : d<p)
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
  have fit : 179740≤Fintype.card I := by
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
    (a:=179740) (d:=d) (by simpa using counted)
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
    (F : Family M Γ) (sub : T⊆Γ) (hi : M.overhead.toNat≤2534)
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

private def pole4184_900_0 : Block := ⟨96, 2250047560033997436032195238535454120879536631126813521395085482936459913955224301335931097471387275621058858851450331266460756995580219124707312541103272501253776115968225213750463410494248895705006508799701754687548922174507730281933077032504480022179794189195731552326654748999604392133973070961470512299448130249489645989349447742114666887782916920498976085667886950768730793069750398378168956256257, 625532824⟩
private theorem pole4184_900_0_checked :
    packedBlock 4184 900 pole4184_900_0.length 900 pole4184_900_0.packed = pole4184_900_0.total := by decide +kernel

private def pole4184_900_1 : Block := ⟨96, 4500096550697935628703763017437814805448495077142056878114488805124050438140644146718946941717787933000048562550776318272348438933479927137609204894290942184844478969193854714483813510792779350120804701940764181173116678384140927023761537127520465247914865275601405324786076987814768876515807480552929421780749834135843652363705695187839431211910116104624363775200863687810285703590333036846827081072737, 4215867544⟩
private theorem pole4184_900_1_checked :
    packedBlock 4184 900 pole4184_900_1.length 996 pole4184_900_1.packed = pole4184_900_1.total := by decide +kernel

private def pole4184_900_2 : Block := ⟨96, 6750145541361873821375330796340175490017453523157300234833892127311640962326063992101962785964188590379038266250102305278236120871379635150511097247478611868435181822419484215217163611091309804536602895081826607658684434593774123765589997222536450473649936362007079097245499226629933360897641890144388331262051538022197658738061942633564195536037315288749751464733840424851840614110915675315485205889217, 11124404632⟩
private theorem pole4184_900_2_checked :
    packedBlock 4184 900 pole4184_900_2.length 1092 pole4184_900_2.packed = pole4184_900_2.total := by decide +kernel

private def pole4184_900_3 : Block := ⟨96, 9000194532025812014046898575242536174586411969172543591553295449499231486511483837484978630210589247758027969949428292284123802809279343163412989600666281552025884675645113715950513711389840258952401088222889034144252190803407320507418457317552435699385007448412752869704921465445097845279476299735847240743353241908551665112418190079288959860164514472875139154266817161893395524631498313784143330705697, 21096340120⟩
private theorem pole4184_900_3_checked :
    packedBlock 4184 900 pole4184_900_3.length 1188 pole4184_900_3.packed = pole4184_900_3.total := by decide +kernel

private def pole4184_900_4 : Block := ⟨96, 11250243522689750206718466354144896859155370415187786948272698771686822010696903682867994474456989905137017673648754279290011484747179051176314881953853951235616587528870743216683863811688370713368199281363951460629819947013040517249246917412568420925120078534818426642164343704260262329661310709327306150224654945794905671486774437525013724184291713657000526843799793898934950435152080952252801455522177, 33876870040⟩
private theorem pole4184_900_4_checked :
    packedBlock 4184 900 pole4184_900_4.length 1284 pole4184_900_4.packed = pole4184_900_4.total := by decide +kernel

private def pole4184_900_5 : Block := ⟨96, 13500292513353688399390034133047257543724328861203030304992102093874412534882323528251010318703390562516007377348080266295899166685078759189216774307041620919207290382096372717417213911986901167783997474505013887115387703222673713991075377507584406150855149621224100414623765943075426814043145118918765059705956649681259677861130684970738488508418912841125914533332770635976505345672663590721459580338657, 49211190424⟩
private theorem pole4184_900_5_checked :
    packedBlock 4184 900 pole4184_900_5.length 1380 pole4184_900_5.packed = pole4184_900_5.total := by decide +kernel

private def pole4184_900_6 : Block := ⟨96, 15750341504017626592061601911949618228293287307218273661711505416062003059067743373634026162949791219894997081047406253301786848622978467202118666660229290602797993235322002218150564012285431622199795667646076313600955459432306910732903837602600391376590220707629774187083188181890591298424979528510223969187258353567613684235486932416463252832546112025251302222865747373018060256193246229190117705155137, 66844497304⟩
private theorem pole4184_900_6_checked :
    packedBlock 4184 900 pole4184_900_6.length 1476 pole4184_900_6.packed = pole4184_900_6.total := by decide +kernel

private def pole4184_900_7 : Block := ⟨96, 18000390494681564784733169690851978912862245753233517018430908738249593583253163219017042007196191877273986784746732240307674530560878175215020559013416960286388696088547631718883914112583962076615593860787138740086523215641940107474732297697616376602325291794035447959542610420705755782806813938101682878668560057453967690609843179862188017156673311209376689912398724110059615166713828867658775829971617, 86521986712⟩
private theorem pole4184_900_7_checked :
    packedBlock 4184 900 pole4184_900_7.length 1572 pole4184_900_7.packed = pole4184_900_7.total := by decide +kernel

private def pole4184_900_8 : Block := ⟨96, 20250439485345502977404737469754339597431204199248760375150312060437184107438583064400057851442592534652976488446058227313562212498777883227922451366604629969979398941773261219617264212882492531031392053928201166572090971851573304216560757792632361828060362880441121732002032659520920267188648347693141788149861761340321696984199427307912781480800510393502077601931700847101170077234411506127433954788097, 107988854680⟩
private theorem pole4184_900_8_checked :
    packedBlock 4184 900 pole4184_900_8.length 1668 pole4184_900_8.packed = pole4184_900_8.total := by decide +kernel

private def pole4184_900_9 : Block := ⟨96, 22500488476009441170076305248656700282000162645264003731869715382624774631624002909783073695688993192031966192145384214319449894436677591240824343719792299653570101794998890720350614313181022985447190247069263593057658728061206500958389217887648347053795433966846795504461454898336084751570482757284600697631163465226675703358555674753637545804927709577627465291464677584142724987754994144596092079604577, 130873707635⟩
private theorem pole4184_900_9_checked :
    packedBlock 4184 900 pole4184_900_9.length 1764 pole4184_900_9.packed = pole4184_900_9.total := by decide +kernel

private def pole4184_900_10 : Block := ⟨96, 24750537466673379362747873027559060966569121091279247088589118704812365155809422755166089539935393849410955895844710201325337576374577299253726236072979969337160804648224520221083964413479553439862988440210326019543226484270839697700217677982664332279530505053252469276920877137151249235952317166876059607112465169113029709732911922199362310129054908761752852980997654321184279898275576783064750204421057, 153383991104⟩
private theorem pole4184_900_10_checked :
    packedBlock 4184 900 pole4184_900_10.length 1860 pole4184_900_10.packed = pole4184_900_10.total := by decide +kernel

private def pole4184_900_11 : Block := ⟨96, 27000586457337317555419440806461421651138079537294490445308522026999955679994842600549105384181794506789945599544036188331225258312477007266628128426167639020751507501450149721817314513778083894278786633351388446028794240480472894442046138077680317505265576139658143049380299375966413720334151576467518516593766872999383716107268169645087074453182107945878240670530631058225834808796159421533408329237537, 174325710656⟩
private theorem pole4184_900_11_checked :
    packedBlock 4184 900 pole4184_900_11.length 1956 pole4184_900_11.packed = pole4184_900_11.total := by decide +kernel

private def pole4184_900_12 : Block := ⟨96, 29250635448001255748091008585363782335707037983309733802027925349187546204180262445932121228428195164168935303243362175337112940250376715279530020779355308704342210354675779222550664614076614348694584826492450872514361996690106091183874598172696302731000647226063816821839721614781578204715985986058977426075068576885737722481624417090811838777309307130003628360063607795267389719316742060002066454054017, 193673135936⟩
private theorem pole4184_900_12_checked :
    packedBlock 4184 900 pole4184_900_12.length 2052 pole4184_900_12.packed = pole4184_900_12.total := by decide +kernel

private def pole4184_900_13 : Block := ⟨96, 31500684438665193940762576364266143020275996429324977158747328671375136728365682291315137072674595821547925006942688162343000622188276423292431913132542978387932913207901408723284014714375144803110383019633513298999929752899739287925703058267712287956735718312469490594299143853596742689097820395650436335556370280772091728855980664536536603101436506314129016049596584532308944629837324698470724578870497, 211426266944⟩
private theorem pole4184_900_13_checked :
    packedBlock 4184 900 pole4184_900_13.length 2148 pole4184_900_13.packed = pole4184_900_13.total := by decide +kernel

private def pole4184_900_14 : Block := ⟨96, 33750733429329132133434144143168503704844954875340220515466731993562727252551102136698152916920996478926914710642014149348888304126176131305333805485730648071523616061127038224017364814673675257526181212774575725485497509109372484667531518362728273182470789398875164366758566092411907173479654805241895245037671984658445735230336911982261367425563705498254403739129561269350499540357907336939382703686977, 227585103680⟩
private theorem pole4184_900_14_checked :
    packedBlock 4184 900 pole4184_900_14.length 2244 pole4184_900_14.packed = pole4184_900_14.total := by decide +kernel

private def pole4184_900_15 : Block := ⟨96, 36000782419993070326105711922070864389413913321355463872186135315750317776736521982081168761167397136305904414341340136354775986064075839318235697838918317755114318914352667724750714914972205711941979405915638151971065265319005681409359978457744258408205860485280838139217988331227071657861489214833354154518973688544799741604693159427986131749690904682379791428662538006392054450878489975408040828503457, 242149646144⟩
private theorem pole4184_900_15_checked :
    packedBlock 4184 900 pole4184_900_15.length 2340 pole4184_900_15.packed = pole4184_900_15.total := by decide +kernel

private def pole4184_900_16 : Block := ⟨96, 38250831410657008518777279700973225073982871767370707228905538637937908300921941827464184605413797793684894118040666123360663668001975547331137590192105987438705021767578297225484065015270736166357777599056700578456633021528638878151188438552760243633940931571686511911677410570042236142243323624424813064000275392431153747979049406873710896073818103866505179118195514743433609361399072613876698953319937, 255119894336⟩
private theorem pole4184_900_16_checked :
    packedBlock 4184 900 pole4184_900_16.length 2436 pole4184_900_16.packed = pole4184_900_16.total := by decide +kernel

private def pole4184_900_17 : Block := ⟨96, 40500880401320946711448847479875585758551830213385950585624941960125498825107361672847200449660198451063883821739992110366551349939875255344039482545293657122295724620803926726217415115569266620773575792197763004942200777738272074893016898647776228859676002658092185684136832808857400626625158034016271973481577096317507754353405654319435660397945303050630566807728491480475164271919655252345357078136417, 266495848256⟩
private theorem pole4184_900_17_checked :
    packedBlock 4184 900 pole4184_900_17.length 2532 pole4184_900_17.packed = pole4184_900_17.total := by decide +kernel

private def pole4184_900_18 : Block := ⟨96, 42750929391984884904120415258777946443120788659401193942344345282313089349292781518230216293906599108442873525439318097372439031877774963356941374898481326805886427474029556226950765215867797075189373985338825431427768533947905271634845358742792214085411073744497859456596255047672565111006992443607730882962878800203861760727761901765160424722072502234755954497261468217516719182440237890814015202952897, 276277507904⟩
private theorem pole4184_900_18_checked :
    packedBlock 4184 900 pole4184_900_18.length 2628 pole4184_900_18.packed = pole4184_900_18.total := by decide +kernel

private def pole4184_900_19 : Block := ⟨96, 45000978382648823096791983037680307127689747105416437299063748604500679873478201363613232138152999765821863229138644084378326713815674671369843267251668996489477130327255185727684115316166327529605172178479887857913336290157538468376673818837808199311146144830903533229055677286487729595388826853199189792444180504090215767102118149210885189046199701418881342186794444954558274092960820529282673327769377, 284464873280⟩
private theorem pole4184_900_19_checked :
    packedBlock 4184 900 pole4184_900_19.length 2724 pole4184_900_19.packed = pole4184_900_19.total := by decide +kernel

private def pole4184_900_20 : Block := ⟨96, 47251027373312761289463550816582667812258705551431680655783151926688270397663621208996247982399400423200852932837970071384214395753574379382745159604856666173067833180480815228417465416464857984020970371620950284398904046367171665118502278932824184536881215917309207001515099525302894079770661262790648701925482207976569773476474396656609953370326900603006729876327421691599829003481403167751331452585857, 291057944384⟩
private theorem pole4184_900_20_checked :
    packedBlock 4184 900 pole4184_900_20.length 2820 pole4184_900_20.packed = pole4184_900_20.total := by decide +kernel

private def pole4184_900_21 : Block := ⟨96, 49501076363976699482135118595485028496827663997446924012502555248875860921849041054379263826645801080579842636537296058390102077691474087395647051958044335856658536033706444729150815516763388438436768564762012710884471802576804861860330739027840169762616287003714880773974521764118058564152495672382107611406783911862923779850830644102334717694454099787132117565860398428641383914001985806219989577402337, 296056721216⟩
private theorem pole4184_900_21_checked :
    packedBlock 4184 900 pole4184_900_21.length 2916 pole4184_900_21.packed = pole4184_900_21.total := by decide +kernel

private def pole4184_900_22 : Block := ⟨96, 51751125354640637674806686374387389181396622443462167369221958571063451446034460899762279670892201737958832340236622045395989759629373795408548944311232005540249238886932074229884165617061918892852566757903075137370039558786438058602159199122856154988351358090120554546433944002933223048534330081973566520888085615749277786225186891548059482018581298971257505255393375165682938824522568444688647702218817, 299461203776⟩
private theorem pole4184_900_22_checked :
    packedBlock 4184 900 pole4184_900_22.length 3012 pole4184_900_22.packed = pole4184_900_22.total := by decide +kernel

private def pole4184_900_23 : Block := ⟨96, 54001174345304575867478254153289749865965580889477410725941361893251041970219880745145295515138602395337822043935948032401877441567273503421450836664419675223839941740157703730617515717360449347268364951044137563855607314996071255343987659217872140214086429176526228318893366241748387532916164491565025430369387319635631792599543138993784246342708498155382892944926351902724493735043151083157305827035297, 301271392064⟩
private theorem pole4184_900_23_checked :
    packedBlock 4184 900 pole4184_900_23.length 3108 pole4184_900_23.packed = pole4184_900_23.total := by decide +kernel

private def pole4184_900_24 : Block := ⟨96, 56251223335968514060149821932192110550534539335492654082660765215438632494405300590528311359385003052716811747635274019407765123505173211434352729017607344907430644593383333231350865817658979801684163144185199990341175071205704452085816119312888125439821500262931902091352788480563552017297998901156484339850689023521985798973899386439509010666835697339508280634459328639766048645563733721625963951851777, 301487286080⟩
private theorem pole4184_900_24_checked :
    packedBlock 4184 900 pole4184_900_24.length 3204 pole4184_900_24.packed = pole4184_900_24.total := by decide +kernel

private def pole4184_900_25 : Block := ⟨96, 58501272326632452252821389711094471235103497781507897439380168537626223018590720435911327203631403710095801451334600006413652805443072919447254621370795014591021347446608962732084215917957510256099961337326262416826742827415337648827644579407904110665556571349337575863812210719378716501679833310747943249331990727408339805348255633885233774990962896523633668323992305376807603556084316360094622076668257, 300108885824⟩
private theorem pole4184_900_25_checked :
    packedBlock 4184 900 pole4184_900_25.length 3300 pole4184_900_25.packed = pole4184_900_25.total := by decide +kernel

private def pole4184_900_26 : Block := ⟨96, 60751321317296390445492957489996831919672456227523140796099571859813813542776140281294343047877804367474791155033925993419540487380972627460156513723982684274612050299834592232817566018256040710515759530467324843312310583624970845569473039502920095891291642435743249636271632958193880986061667720339402158813292431294693811722611881330958539315090095707759056013525282113849158466604898998563280201484737, 297136191296⟩
private theorem pole4184_900_26_checked :
    packedBlock 4184 900 pole4184_900_26.length 3396 pole4184_900_26.packed = pole4184_900_26.total := by decide +kernel

private def pole4184_900_27 : Block := ⟨96, 63001370307960328638164525268899192604241414673538384152818975182001404066961560126677358892124205024853780858733251980425428169318872335473058406077170353958202753153060221733550916118554571164931557723608387269797878339834604042311301499597936081117026713522148923408731055197009045470443502129930861068294594135181047818096968128776683303639217294891884443703058258850890713377125481637031938326301217, 292569202496⟩
private theorem pole4184_900_27_checked :
    packedBlock 4184 900 pole4184_900_27.length 3492 pole4184_900_27.packed = pole4184_900_27.total := by decide +kernel

private def pole4184_900_28 : Block := ⟨96, 65251419298624266830836093047801553288810373119553627509538378504188994591146979972060374736370605682232770562432577967431315851256772043485960298430358023641793456006285851234284266218853101619347355916749449696283446096044237239053129959692952066342761784608554597181190477435824209954825336539522319977775895839067401824471324376222408067963344494076009831392591235587932268287646064275500596451117697, 286407919424⟩
private theorem pole4184_900_28_checked :
    packedBlock 4184 900 pole4184_900_28.length 3588 pole4184_900_28.packed = pole4184_900_28.total := by decide +kernel

private def pole4184_900_29 : Block := ⟨96, 67501468289288205023507660826703913973379331565568870866257781826376585115332399817443390580617006339611760266131903954437203533194671751498862190783545693325384158859511480735017616319151632073763154109890512122769013852253870435794958419787968051568496855694960270953649899674639374439207170949113778887257197542953755830845680623668132832287471693260135219082124212324973823198166646913969254575934177, 278652342080⟩
private theorem pole4184_900_29_checked :
    packedBlock 4184 900 pole4184_900_29.length 3684 pole4184_900_29.packed = pole4184_900_29.total := by decide +kernel

private def pole4184_900_30 : Block := ⟨96, 69751517279952143216179228605606274657948290011584114222977185148564175639517819662826406424863406996990749969831229941443091215132571459511764083136733363008974861712737110235750966419450162528178952303031574549254581608463503632536786879882984036794231926781365944726109321913454538923589005358705237796738499246840109837220036871113857596611598892444260606771657189062015378108687229552437912700750657, 269302470464⟩
private theorem pole4184_900_30_checked :
    packedBlock 4184 900 pole4184_900_30.length 3780 pole4184_900_30.packed = pole4184_900_30.total := by decide +kernel

private def pole4184_900_31 : Block := ⟨96, 72001566270616081408850796384508635342517248457599357579696588470751766163703239508209422269109807654369739673530555928448978897070471167524665975489921032692565564565962739736484316519748692982594750496172636975740149364673136829278615339978000022019966997867771618498568744152269703407970839768296696706219800950726463843594393118559582360935726091628385994461190165799056933019207812190906570825567137, 258358304576⟩
private theorem pole4184_900_31_checked :
    packedBlock 4184 900 pole4184_900_31.length 3876 pole4184_900_31.packed = pole4184_900_31.total := by decide +kernel

private def pole4184_900_32 : Block := ⟨96, 74251615261280019601522364163410996027086206903614600936415991792939356687888659353592438113356208311748729377229881915454866579008370875537567867843108702376156267419188369237217666620047223437010548689313699402225717120882770026020443800073016007245702068954177292271028166391084867892352674177888155615701102654612817849968749366005307125259853290812511382150723142536098487929728394829375228950383617, 245819844416⟩
private theorem pole4184_900_32_checked :
    packedBlock 4184 900 pole4184_900_32.length 3972 pole4184_900_32.packed = pole4184_900_32.total := by decide +kernel

private def pole4184_900_33 : Block := ⟨96, 76501664251943957794193931942313356711655165349629844293135395115126947212074079198975453957602608969127719080929207902460754260946270583550469760196296372059746970272413998737951016720345753891426346882454761828711284877092403222762272260168031992471437140040582966043487588629900032376734508587479614525182404358499171856343105613451031889583980489996636769840256119273140042840248977467843887075200097, 231687089984⟩
private theorem pole4184_900_33_checked :
    packedBlock 4184 900 pole4184_900_33.length 4068 pole4184_900_33.packed = pole4184_900_33.total := by decide +kernel

private def pole4184_900_34 : Block := ⟨96, 78704837221969063941184842059155251548628937161353103413256477534768963803036423164111315576318957975898978209405910694817907457844567206110296019367845164454216540835061837687810387911858703716316654207153748357312484920167736367598064086390678350406150672347405114700740997280978392506361842193800465980108988960241201500830720716846445355958622990568770612140746182047637897278625272123221481446476993, 216052125607⟩
private theorem pole4184_900_34_checked :
    packedBlock 4184 900 pole4184_900_34.length 4164 pole4184_900_34.packed = pole4184_900_34.total := by decide +kernel

private def pole4184_900_35 : Block := ⟨96, 80790820140397095303160659422868532815307070535364888294338439218081744196644216637231969563067786225359893633245410579546053740855726234992558829283591819509366659493601464353508281373548098513327436682497002382969327766683553380066295399328343692213744976438000286522835717191088900919335975740114160589487575806314024011510769099568290886874369508344579247870106550458857467116860827594660418618395935, 199648020936⟩
private theorem pole4184_900_35_checked :
    packedBlock 4184 900 pole4184_900_35.length 4260 pole4184_900_35.packed = pole4184_900_35.total := by decide +kernel

private def pole4184_900_36 : Block := ⟨96, 82783051017547451915402058658415854246730322960515033098639435730504759329246098204087933995453977408328195353409667764881321911015473445483439153212804866324521368558489221134619163589629107820946009317068275899013589273355347200542302836843931414273855112623836224567612671682892074690913828113202114706395301343689694879831013268479632675822396202190091990678719507786184201384746708163846870413495672, 182943836319⟩
private theorem pole4184_900_36_checked :
    packedBlock 4184 900 pole4184_900_36.length 4356 pole4184_900_36.packed = pole4184_900_36.total := by decide +kernel

private def pole4184_900_37 : Block := ⟨96, 84634653832781317720113304043654402372389602449383049804518938382516933514138334851528944870628866927390093711580335682759421489603979513946015656717084549947107443218803721960786677425942576931624878914790463533129692156905275995831912388866526494785753917045059211810279733565492843579281072516715515662562169759960635306495142119137541528615814933968508907895599085401506937628224263597670127654620620, 166119929756⟩
private theorem pole4184_900_37_checked :
    packedBlock 4184 900 pole4184_900_37.length 4452 pole4184_900_37.packed = pole4184_900_37.total := by decide +kernel

private def pole4184_900_38 : Block := ⟨96, 86369066596418108739158921208064042636454428631871339914863522918805225230759161630504771404925628739349297546220893369274137120920564718417095718943987395312002543058593422717297815974062349639727947604932283516220003830772467508382797758162592873366559911879455465662003235115564608311945946887859019962876559199538210216078603818203660419038550995530293772555798865156966865132444014093449108732186140, 149348420809⟩
private theorem pole4184_900_38_checked :
    packedBlock 4184 900 pole4184_900_38.length 4548 pole4184_900_38.packed = pole4184_900_38.total := by decide +kernel

private def pole4184_900_39 : Block := ⟨96, 87986289308457814315141610550361757154483139516389660495289287456267041039912171812218391770350533570424038087589501218201073275375873172434042646137093552522941413206121644343942391543218990342049584674451553948120725923911919155341705874322358572086025142960797653811209820924991218386120169759606584599530427894849625348726922350679528227234795579949134659798886869070694512548510384667507632480292454, 132794642194⟩
private theorem pole4184_900_39_checked :
    packedBlock 4184 900 pole4184_900_39.length 4644 pole4184_900_39.packed = pole4184_900_39.total := by decide +kernel

private def pole4184_900_40 : Block := ⟨96, 89486321968900439776922655736296664277529387309404458301085909001812123915549114480747012044419731797773619594678564009429507050738915289047532703338089504390856027374157086894270909661370341600595816514893458127209262184923935027610512892489254842293980739143401856563433090849345289536661128948441302107352173118051795928838252930797606076180848571258579396355479510328169526032375889411647826062659242, 116617139448⟩
private theorem pole4184_900_40_checked :
    packedBlock 4184 900 pole4184_900_40.length 4740 pole4184_900_40.packed = pole4184_900_40.total := by decide +kernel

private def pole4184_900_41 : Block := ⟨96, 90845727997969185807469807080916847226695451052527503864233994395785145303071757022044963840220456387068159823901601865704178838451825178197283670785689700103123317065128804310839350650750176780285605322366789602146775549974514022956578559343236288596587292553505701073286348959095303360955414855456605935912454599299028511946084613881245818484778698464170526688434380226210728981712446207258026418294506, 100967670642⟩
private theorem pole4184_900_41_checked :
    packedBlock 4184 900 pole4184_900_41.length 4836 pole4184_900_41.packed = pole4184_900_41.total := by decide +kernel

private def pole4184_900_42 : Block := ⟨96, 92111379124762342398636371880986803576754889449654912285348567439474030857202432414786845626037101992135690130372605814909167522632897858157431402485770647972511988160717478405917456743475144331848025752341331978945186442756200847812093435626450962182783763528228442385355551197127175075668640805305569420012908736930229717385218050964232788675379924779786480758091649325629437638688384700784939280977701, 85991207049⟩
private theorem pole4184_900_42_checked :
    packedBlock 4184 900 pole4184_900_42.length 4932 pole4184_900_42.packed = pole4184_900_42.total := by decide +kernel

private def pole4184_900_43 : Block := ⟨96, 93025462957674881260806959620306376044228578000357126995996863696623694003106564222827424036924378320167234155715413835747033790721091069963987243008649883157542237911861550793150898922562251685296464571969987283896060854517624940478640989703223774855848163204410494917630807739297473738016176243233942906114362384118052312020300849644345839677779430061651313445777422513163404616435779416331262272917338, 71806851002⟩
private theorem pole4184_900_43_checked :
    packedBlock 4184 900 pole4184_900_43.length 5028 pole4184_900_43.packed = pole4184_900_43.total := by decide +kernel

private def pole4184_900_44 : Block := ⟨96, 93587975205340865808974851565031966215370817611860937835176714527170591634152919184173177997985978484511981581640245332498505711205565996967212716096946800578439913625167958168713269186427080238212083053213618602109781480774574374322106001401512823257618692144234305466973197456157544951994824382801181693808650166172674202894404721095556395142045945468420603534977227406148627610062551877291532093509505, 58448940840⟩
private theorem pole4184_900_44_checked :
    packedBlock 4184 900 pole4184_900_44.length 5124 pole4184_900_44.packed = pole4184_900_44.total := by decide +kernel

private def pole4184_900_45 : Block := ⟨96, 94150487453006850357142743509757556386513057223364748674356565357717489265199274145518931959047578648856729007565076829249977631690040923970438189185243717999337589338474365543896606711501712851816032601498884208731173419826982673507563116425266819564052459915835723910088053015861336073090282985199046421178975592144262704487993782956987586223077745264451950457360471590409016337692697536908696624713625, 46223461800⟩
private theorem pole4184_900_45_checked :
    packedBlock 4184 900 pole4184_900_45.length 5220 pole4184_900_45.packed = pole4184_900_45.total := by decide +kernel

private def pole4184_900_46 : Block := ⟨96, 94712999700672834905310635454483146557655296834868559513536416188264386896245629106864685920109178813201476433489908326001449552174515850973663662273540635420235265051780772919079944236576345465419982149784149815352565358879390972693020231449020815870486227687437142353202908575565127194185741587596911148549301018115851206081582844818418777304109545060483297379743715774669405065322843196525861155917745, 35254335528⟩
private theorem pole4184_900_46_checked :
    packedBlock 4184 900 pole4184_900_46.length 5316 pole4184_900_46.packed = pole4184_900_46.total := by decide +kernel

private def pole4184_900_47 : Block := ⟨96, 95275511948338819453478527399208736728797536446372370352716267018811284527291984068210439881170778977546223859414739822752921472658990777976889135361837552841132940765087180294263281761650978079023931698069415421973957297931799271878477346472774812176919995459038560796317764135268918315281200189994775875919626444087439707675171906679849968385141344856514644302126959958929793792952988856143025687121865, 25621188264⟩
private theorem pole4184_900_47_checked :
    packedBlock 4184 900 pole4184_900_47.length 5412 pole4184_900_47.packed = pole4184_900_47.total := by decide +kernel

private def pole4184_900_48 : Block := ⟨96, 95838024196004804001646419343934326899939776057876181191896117849358182158338339029556193842232379141890971285339571319504393393143465704980114608450134470262030616478393587669446619286725610692627881246354681028595349236984207571063934461496528808483353763230639979239432619694972709436376658792392640603289951870059028209268760968541281159466173144652545991224510204143190182520583134515760190218325985, 17403646248⟩
private theorem pole4184_900_48_checked :
    packedBlock 4184 900 pole4184_900_48.length 5508 pole4184_900_48.packed = pole4184_900_48.total := by decide +kernel

private def pole4184_900_49 : Block := ⟨96, 96400536443670788549814311288659917071082015669379992031075968679905079789384693990901947803293979306235718711264402816255865313627940631983340081538431387682928292191699995044629956811800243306231830794639946635216741176036615870249391576520282804789787531002241397682547475254676500557472117394790505330660277296030616710862350030402712350547204944448577338146893448327450571248213280175377354749530105, 10681335720⟩
private theorem pole4184_900_49_checked :
    packedBlock 4184 900 pole4184_900_49.length 5604 pole4184_900_49.packed = pole4184_900_49.total := by decide +kernel

private def pole4184_900_50 : Block := ⟨96, 96963048691336773097982203233385507242224255280883802870255819510451977420431048952247701764355579470580466137189234313007337234112415558986565554626728305103825967905006402419813294336874875919835780342925212241838133115089024169434848691544036801096221298773842816125662330814380291678567575997188370058030602722002205212455939092264143541628236744244608685069276692511710959975843425834994519280734225, 5533882920⟩
private theorem pole4184_900_50_checked :
    packedBlock 4184 900 pole4184_900_50.length 5700 pole4184_900_50.packed = pole4184_900_50.total := by decide +kernel

private def pole4184_900_51 : Block := ⟨96, 97525560939002757646150095178111097413366494892387613709435670340998875051477403913593455725417179634925213563114065809758809154596890485989791027715025222524723643618312809794996631861949508533439729891210477848459525054141432468620305806567790797402655066545444234568777186374084082799663034599586234785400928147973793714049528154125574732709268544040640031991659936695971348703473571494611683811938345, 2040914088⟩
private theorem pole4184_900_51_checked :
    packedBlock 4184 900 pole4184_900_51.length 5796 pole4184_900_51.packed = pole4184_900_51.total := by decide +kernel

private def pole4184_900_52 : Block := ⟨92, 1360920198428113378090154848729188200871941544039331778858053511042549916804508269179555025477559116729566327606726757297169873931768898613087418461917764446741243895049944028351853330164869037956825099585975965945349716531194758031005107141519425759987152837007271807500705888625365283851139964017620660497789273918286618137950506498317910011346454619079599967949551103282210557295349825, 282051277⟩
private theorem pole4184_900_52_checked :
    packedBlock 4184 900 pole4184_900_52.length 5892 pole4184_900_52.packed = pole4184_900_52.total := by decide +kernel

private def poleBlocks4184_900 : List Block := [pole4184_900_0, pole4184_900_1, pole4184_900_2, pole4184_900_3, pole4184_900_4, pole4184_900_5, pole4184_900_6, pole4184_900_7, pole4184_900_8, pole4184_900_9, pole4184_900_10, pole4184_900_11, pole4184_900_12, pole4184_900_13, pole4184_900_14, pole4184_900_15, pole4184_900_16, pole4184_900_17, pole4184_900_18, pole4184_900_19, pole4184_900_20, pole4184_900_21, pole4184_900_22, pole4184_900_23, pole4184_900_24, pole4184_900_25, pole4184_900_26, pole4184_900_27, pole4184_900_28, pole4184_900_29, pole4184_900_30, pole4184_900_31, pole4184_900_32, pole4184_900_33, pole4184_900_34, pole4184_900_35, pole4184_900_36, pole4184_900_37, pole4184_900_38, pole4184_900_39, pole4184_900_40, pole4184_900_41, pole4184_900_42, pole4184_900_43, pole4184_900_44, pole4184_900_45, pole4184_900_46, pole4184_900_47, pole4184_900_48, pole4184_900_49, pole4184_900_50, pole4184_900_51, pole4184_900_52]
theorem moment4184_900 : P1_7_1.groupedPoleMoment 4184 900 ≤ 8370437628682 := by
  refine grouped_from_blocks 4184 900 _ poleBlocks4184_900 ?_ (by decide) (by decide)
  exact ⟨pole4184_900_0_checked, pole4184_900_1_checked, pole4184_900_2_checked, pole4184_900_3_checked, pole4184_900_4_checked, pole4184_900_5_checked, pole4184_900_6_checked, pole4184_900_7_checked, pole4184_900_8_checked, pole4184_900_9_checked, pole4184_900_10_checked, pole4184_900_11_checked, pole4184_900_12_checked, pole4184_900_13_checked, pole4184_900_14_checked, pole4184_900_15_checked, pole4184_900_16_checked, pole4184_900_17_checked, pole4184_900_18_checked, pole4184_900_19_checked, pole4184_900_20_checked, pole4184_900_21_checked, pole4184_900_22_checked, pole4184_900_23_checked, pole4184_900_24_checked, pole4184_900_25_checked, pole4184_900_26_checked, pole4184_900_27_checked, pole4184_900_28_checked, pole4184_900_29_checked, pole4184_900_30_checked, pole4184_900_31_checked, pole4184_900_32_checked, pole4184_900_33_checked, pole4184_900_34_checked, pole4184_900_35_checked, pole4184_900_36_checked, pole4184_900_37_checked, pole4184_900_38_checked, pole4184_900_39_checked, pole4184_900_40_checked, pole4184_900_41_checked, pole4184_900_42_checked, pole4184_900_43_checked, pole4184_900_44_checked, pole4184_900_45_checked, pole4184_900_46_checked, pole4184_900_47_checked, pole4184_900_48_checked, pole4184_900_49_checked, pole4184_900_50_checked, pole4184_900_51_checked, pole4184_900_52_checked, True.intro⟩

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

-- Source: Research6969.SpreadEdges00
section Z6969Source0662
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge64_3_55_2293_2293_cost : SpreadInterval.costSum shape 179740 64 3 55 2293 2293 ≤ 1330973011 := by
  decide +kernel

theorem edge64_3_55_2293_2293 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2293 2293 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2293_2293_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_32_41_2293_2353_cost : SpreadInterval.costSum shape 179740 41 32 41 2293 2353 ≤ 1330405721 := by
  decide +kernel

theorem edge41_32_41_2293_2353 : SpreadInterval.Positive shape 179740 41 32 41 nodes moment 2293 2353 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_32_41_2293_2353_cost) _).trans_lt <;>
    decide +kernel

private theorem edge22_7_20_2293_2534_cost : SpreadInterval.costSum shape 179740 22 7 20 2293 2534 ≤ 1312043315 := by
  decide +kernel

theorem edge22_7_20_2293_2534 : SpreadInterval.Positive shape 179740 22 7 20 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge22_7_20_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge22_8_21_2293_2534_cost : SpreadInterval.costSum shape 179740 22 8 21 2293 2534 ≤ 1273709598 := by
  decide +kernel

theorem edge22_8_21_2293_2534 : SpreadInterval.Positive shape 179740 22 8 21 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge22_8_21_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge22_9_22_2293_2534_cost : SpreadInterval.costSum shape 179740 22 9 22 2293 2534 ≤ 1245995938 := by
  decide +kernel

theorem edge22_9_22_2293_2534 : SpreadInterval.Positive shape 179740 22 9 22 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge22_9_22_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge22_12_22_2293_2534_cost : SpreadInterval.costSum shape 179740 22 12 22 2293 2534 ≤ 1297534412 := by
  decide +kernel

theorem edge22_12_22_2293_2534 : SpreadInterval.Positive shape 179740 22 12 22 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge22_12_22_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge22_13_22_2293_2534_cost : SpreadInterval.costSum shape 179740 22 13 22 2293 2534 ≤ 1328102736 := by
  decide +kernel

theorem edge22_13_22_2293_2534 : SpreadInterval.Positive shape 179740 22 13 22 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge22_13_22_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge23_7_21_2293_2534_cost : SpreadInterval.costSum shape 179740 23 7 21 2293 2534 ≤ 1286222237 := by
  decide +kernel

theorem edge23_7_21_2293_2534 : SpreadInterval.Positive shape 179740 23 7 21 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge23_7_21_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge23_8_22_2293_2534_cost : SpreadInterval.costSum shape 179740 23 8 22 2293 2534 ≤ 1247054810 := by
  decide +kernel

theorem edge23_8_22_2293_2534 : SpreadInterval.Positive shape 179740 23 8 22 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge23_8_22_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge23_9_23_2293_2534_cost : SpreadInterval.costSum shape 179740 23 9 23 2293 2534 ≤ 1218771349 := by
  decide +kernel

theorem edge23_9_23_2293_2534 : SpreadInterval.Positive shape 179740 23 9 23 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge23_9_23_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0662

-- Source: Research6969.SpreadEdges01
section Z6969Source0663
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge23_12_23_2293_2534_cost : SpreadInterval.costSum shape 179740 23 12 23 2293 2534 ≤ 1262114890 := by
  decide +kernel

theorem edge23_12_23_2293_2534 : SpreadInterval.Positive shape 179740 23 12 23 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge23_12_23_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge23_13_23_2293_2534_cost : SpreadInterval.costSum shape 179740 23 13 23 2293 2534 ≤ 1289907679 := by
  decide +kernel

theorem edge23_13_23_2293_2534 : SpreadInterval.Positive shape 179740 23 13 23 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge23_13_23_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge23_14_23_2293_2534_cost : SpreadInterval.costSum shape 179740 23 14 23 2293 2534 ≤ 1322290202 := by
  decide +kernel

theorem edge23_14_23_2293_2534 : SpreadInterval.Positive shape 179740 23 14 23 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge23_14_23_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_6_22_2293_2534_cost : SpreadInterval.costSum shape 179740 25 6 22 2293 2534 ≤ 1297172794 := by
  decide +kernel

theorem edge25_6_22_2293_2534 : SpreadInterval.Positive shape 179740 25 6 22 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_6_22_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_7_23_2293_2534_cost : SpreadInterval.costSum shape 179740 25 7 23 2293 2534 ≤ 1241154819 := by
  decide +kernel

theorem edge25_7_23_2293_2534 : SpreadInterval.Positive shape 179740 25 7 23 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_7_23_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_8_24_2293_2534_cost : SpreadInterval.costSum shape 179740 25 8 24 2293 2534 ≤ 1200341949 := by
  decide +kernel

theorem edge25_8_24_2293_2534 : SpreadInterval.Positive shape 179740 25 8 24 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_8_24_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_9_25_2293_2534_cost : SpreadInterval.costSum shape 179740 25 9 25 2293 2534 ≤ 1170845241 := by
  decide +kernel

theorem edge25_9_25_2293_2534 : SpreadInterval.Positive shape 179740 25 9 25 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_9_25_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_13_25_2293_2534_cost : SpreadInterval.costSum shape 179740 25 13 25 2293 2534 ≤ 1222667479 := by
  decide +kernel

theorem edge25_13_25_2293_2534 : SpreadInterval.Positive shape 179740 25 13 25 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_13_25_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_14_25_2293_2534_cost : SpreadInterval.costSum shape 179740 25 14 25 2293 2534 ≤ 1250141601 := by
  decide +kernel

theorem edge25_14_25_2293_2534 : SpreadInterval.Positive shape 179740 25 14 25 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_14_25_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge25_15_25_2293_2534_cost : SpreadInterval.costSum shape 179740 25 15 25 2293 2534 ≤ 1281366334 := by
  decide +kernel

theorem edge25_15_25_2293_2534 : SpreadInterval.Positive shape 179740 25 15 25 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_15_25_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0663

-- Source: Research6969.SpreadEdges02
section Z6969Source0664
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge25_16_25_2293_2534_cost : SpreadInterval.costSum shape 179740 25 16 25 2293 2534 ≤ 1315692321 := by
  decide +kernel

theorem edge25_16_25_2293_2534 : SpreadInterval.Positive shape 179740 25 16 25 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge25_16_25_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_5_24_2293_2534_cost : SpreadInterval.costSum shape 179740 28 5 24 2293 2534 ≤ 1322770135 := by
  decide +kernel

theorem edge28_5_24_2293_2534 : SpreadInterval.Positive shape 179740 28 5 24 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_5_24_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_6_25_2293_2534_cost : SpreadInterval.costSum shape 179740 28 6 25 2293 2534 ≤ 1245107776 := by
  decide +kernel

theorem edge28_6_25_2293_2534 : SpreadInterval.Positive shape 179740 28 6 25 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_6_25_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_7_26_2293_2534_cost : SpreadInterval.costSum shape 179740 28 7 26 2293 2534 ≤ 1186302214 := by
  decide +kernel

theorem edge28_7_26_2293_2534 : SpreadInterval.Positive shape 179740 28 7 26 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_7_26_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_8_27_2293_2534_cost : SpreadInterval.costSum shape 179740 28 8 27 2293 2534 ≤ 1143142873 := by
  decide +kernel

theorem edge28_8_27_2293_2534 : SpreadInterval.Positive shape 179740 28 8 27 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_8_27_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_9_28_2293_2534_cost : SpreadInterval.costSum shape 179740 28 9 28 2293 2534 ≤ 1111776317 := by
  decide +kernel

theorem edge28_9_28_2293_2534 : SpreadInterval.Positive shape 179740 28 9 28 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_9_28_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_15_28_2293_2534_cost : SpreadInterval.costSum shape 179740 28 15 28 2293 2534 ≤ 1186361170 := by
  decide +kernel

theorem edge28_15_28_2293_2534 : SpreadInterval.Positive shape 179740 28 15 28 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_15_28_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_16_28_2293_2534_cost : SpreadInterval.costSum shape 179740 28 16 28 2293 2534 ≤ 1214593837 := by
  decide +kernel

theorem edge28_16_28_2293_2534 : SpreadInterval.Positive shape 179740 28 16 28 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_16_28_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_17_28_2293_2534_cost : SpreadInterval.costSum shape 179740 28 17 28 2293 2534 ≤ 1245436994 := by
  decide +kernel

theorem edge28_17_28_2293_2534 : SpreadInterval.Positive shape 179740 28 17 28 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_17_28_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge28_18_28_2293_2534_cost : SpreadInterval.costSum shape 179740 28 18 28 2293 2534 ≤ 1278471951 := by
  decide +kernel

theorem edge28_18_28_2293_2534 : SpreadInterval.Positive shape 179740 28 18 28 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_18_28_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0664

-- Source: Research6969.SpreadEdges03
section Z6969Source0665
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge28_19_28_2293_2534_cost : SpreadInterval.costSum shape 179740 28 19 28 2293 2534 ≤ 1313364687 := by
  decide +kernel

theorem edge28_19_28_2293_2534 : SpreadInterval.Positive shape 179740 28 19 28 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge28_19_28_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_5_29_2293_2534_cost : SpreadInterval.costSum shape 179740 33 5 29 2293 2534 ≤ 1262669369 := by
  decide +kernel

theorem edge33_5_29_2293_2534 : SpreadInterval.Positive shape 179740 33 5 29 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_5_29_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_6_30_2293_2534_cost : SpreadInterval.costSum shape 179740 33 6 30 2293 2534 ≤ 1180864094 := by
  decide +kernel

theorem edge33_6_30_2293_2534 : SpreadInterval.Positive shape 179740 33 6 30 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_6_30_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_7_31_2293_2534_cost : SpreadInterval.costSum shape 179740 33 7 31 2293 2534 ≤ 1118133007 := by
  decide +kernel

theorem edge33_7_31_2293_2534 : SpreadInterval.Positive shape 179740 33 7 31 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_7_31_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_8_32_2293_2534_cost : SpreadInterval.costSum shape 179740 33 8 32 2293 2534 ≤ 1071493289 := by
  decide +kernel

theorem edge33_8_32_2293_2534 : SpreadInterval.Positive shape 179740 33 8 32 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_8_32_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_9_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 9 33 2293 2534 ≤ 1037163693 := by
  decide +kernel

theorem edge33_9_33_2293_2534 : SpreadInterval.Positive shape 179740 33 9 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_9_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_17_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 17 33 2293 2534 ≤ 1109998685 := by
  decide +kernel

theorem edge33_17_33_2293_2534 : SpreadInterval.Positive shape 179740 33 17 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_17_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_18_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 18 33 2293 2534 ≤ 1135300882 := by
  decide +kernel

theorem edge33_18_33_2293_2534 : SpreadInterval.Positive shape 179740 33 18 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_18_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_19_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 19 33 2293 2534 ≤ 1162449220 := by
  decide +kernel

theorem edge33_19_33_2293_2534 : SpreadInterval.Positive shape 179740 33 19 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_19_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_20_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 20 33 2293 2534 ≤ 1191214746 := by
  decide +kernel

theorem edge33_20_33_2293_2534 : SpreadInterval.Positive shape 179740 33 20 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_20_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0665

-- Source: Research6969.SpreadEdges04
section Z6969Source0666
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge33_21_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 21 33 2293 2534 ≤ 1221383311 := by
  decide +kernel

theorem edge33_21_33_2293_2534 : SpreadInterval.Positive shape 179740 33 21 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_21_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_22_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 22 33 2293 2534 ≤ 1252733474 := by
  decide +kernel

theorem edge33_22_33_2293_2534 : SpreadInterval.Positive shape 179740 33 22 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_22_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_23_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 23 33 2293 2534 ≤ 1285169059 := by
  decide +kernel

theorem edge33_23_33_2293_2534 : SpreadInterval.Positive shape 179740 33 23 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_23_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge33_24_33_2293_2534_cost : SpreadInterval.costSum shape 179740 33 24 33 2293 2534 ≤ 1318573693 := by
  decide +kernel

theorem edge33_24_33_2293_2534 : SpreadInterval.Positive shape 179740 33 24 33 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge33_24_33_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_4_36_2293_2534_cost : SpreadInterval.costSum shape 179740 41 4 36 2293 2534 ≤ 1299728002 := by
  decide +kernel

theorem edge41_4_36_2293_2534 : SpreadInterval.Positive shape 179740 41 4 36 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_4_36_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_5_37_2293_2534_cost : SpreadInterval.costSum shape 179740 41 5 37 2293 2534 ≤ 1199351753 := by
  decide +kernel

theorem edge41_5_37_2293_2534 : SpreadInterval.Positive shape 179740 41 5 37 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_5_37_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_6_38_2293_2534_cost : SpreadInterval.costSum shape 179740 41 6 38 2293 2534 ≤ 1112633283 := by
  decide +kernel

theorem edge41_6_38_2293_2534 : SpreadInterval.Positive shape 179740 41 6 38 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_6_38_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_7_39_2293_2534_cost : SpreadInterval.costSum shape 179740 41 7 39 2293 2534 ≤ 1045072020 := by
  decide +kernel

theorem edge41_7_39_2293_2534 : SpreadInterval.Positive shape 179740 41 7 39 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_7_39_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_8_40_2293_2534_cost : SpreadInterval.costSum shape 179740 41 8 40 2293 2534 ≤ 993954252 := by
  decide +kernel

theorem edge41_8_40_2293_2534 : SpreadInterval.Positive shape 179740 41 8 40 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_8_40_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_9_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 9 41 2293 2534 ≤ 955602617 := by
  decide +kernel

theorem edge41_9_41_2293_2534 : SpreadInterval.Positive shape 179740 41 9 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_9_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0666

-- Source: Research6969.SpreadEdges05
section Z6969Source0667
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge41_21_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 21 41 2293 2534 ≤ 1039386362 := by
  decide +kernel

theorem edge41_21_41_2293_2534 : SpreadInterval.Positive shape 179740 41 21 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_21_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_22_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 22 41 2293 2534 ≤ 1062232600 := by
  decide +kernel

theorem edge41_22_41_2293_2534 : SpreadInterval.Positive shape 179740 41 22 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_22_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_23_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 23 41 2293 2534 ≤ 1086156444 := by
  decide +kernel

theorem edge41_23_41_2293_2534 : SpreadInterval.Positive shape 179740 41 23 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_23_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_24_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 24 41 2293 2534 ≤ 1111037571 := by
  decide +kernel

theorem edge41_24_41_2293_2534 : SpreadInterval.Positive shape 179740 41 24 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_24_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_25_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 25 41 2293 2534 ≤ 1136710402 := by
  decide +kernel

theorem edge41_25_41_2293_2534 : SpreadInterval.Positive shape 179740 41 25 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_25_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_26_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 26 41 2293 2534 ≤ 1163095418 := by
  decide +kernel

theorem edge41_26_41_2293_2534 : SpreadInterval.Positive shape 179740 41 26 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_26_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_27_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 27 41 2293 2534 ≤ 1190167332 := by
  decide +kernel

theorem edge41_27_41_2293_2534 : SpreadInterval.Positive shape 179740 41 27 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_27_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_28_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 28 41 2293 2534 ≤ 1217848123 := by
  decide +kernel

theorem edge41_28_41_2293_2534 : SpreadInterval.Positive shape 179740 41 28 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_28_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_29_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 29 41 2293 2534 ≤ 1246035045 := by
  decide +kernel

theorem edge41_29_41_2293_2534 : SpreadInterval.Positive shape 179740 41 29 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_29_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_30_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 30 41 2293 2534 ≤ 1274712301 := by
  decide +kernel

theorem edge41_30_41_2293_2534 : SpreadInterval.Positive shape 179740 41 30 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_30_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0667

end Merged_Z6969Pack0588

-- merged module Z6969Pack0589
section Merged_Z6969Pack0589

-- Source: Research6969.SpreadEdges06
section Z6969Source0668
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge41_31_41_2293_2534_cost : SpreadInterval.costSum shape 179740 41 31 41 2293 2534 ≤ 1303839373 := by
  decide +kernel

theorem edge41_31_41_2293_2534 : SpreadInterval.Positive shape 179740 41 31 41 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_31_41_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_4_44_2293_2534_cost : SpreadInterval.costSum shape 179740 50 4 44 2293 2534 ≤ 1261319469 := by
  decide +kernel

theorem edge50_4_44_2293_2534 : SpreadInterval.Positive shape 179740 50 4 44 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_4_44_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_5_45_2293_2534_cost : SpreadInterval.costSum shape 179740 50 5 45 2293 2534 ≤ 1157891607 := by
  decide +kernel

theorem edge50_5_45_2293_2534 : SpreadInterval.Positive shape 179740 50 5 45 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_5_45_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_6_46_2293_2534_cost : SpreadInterval.costSum shape 179740 50 6 46 2293 2534 ≤ 1067642443 := by
  decide +kernel

theorem edge50_6_46_2293_2534 : SpreadInterval.Positive shape 179740 50 6 46 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_6_46_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_7_47_2293_2534_cost : SpreadInterval.costSum shape 179740 50 7 47 2293 2534 ≤ 996524342 := by
  decide +kernel

theorem edge50_7_47_2293_2534 : SpreadInterval.Positive shape 179740 50 7 47 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_7_47_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_8_48_2293_2534_cost : SpreadInterval.costSum shape 179740 50 8 48 2293 2534 ≤ 942010933 := by
  decide +kernel

theorem edge50_8_48_2293_2534 : SpreadInterval.Positive shape 179740 50 8 48 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_8_48_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_9_49_2293_2534_cost : SpreadInterval.costSum shape 179740 50 9 49 2293 2534 ≤ 900511225 := by
  decide +kernel

theorem edge50_9_49_2293_2534 : SpreadInterval.Positive shape 179740 50 9 49 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_9_49_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_10_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 10 50 2293 2534 ≤ 868987982 := by
  decide +kernel

theorem edge50_10_50_2293_2534 : SpreadInterval.Positive shape 179740 50 10 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_10_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_26_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 26 50 2293 2534 ≤ 996203623 := by
  decide +kernel

theorem edge50_26_50_2293_2534 : SpreadInterval.Positive shape 179740 50 26 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_26_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_27_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 27 50 2293 2534 ≤ 1016931885 := by
  decide +kernel

theorem edge50_27_50_2293_2534 : SpreadInterval.Positive shape 179740 50 27 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_27_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0668

-- Source: Research6969.SpreadEdges07
section Z6969Source0669
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge50_28_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 28 50 2293 2534 ≤ 1038255789 := by
  decide +kernel

theorem edge50_28_50_2293_2534 : SpreadInterval.Positive shape 179740 50 28 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_28_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_29_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 29 50 2293 2534 ≤ 1060099624 := by
  decide +kernel

theorem edge50_29_50_2293_2534 : SpreadInterval.Positive shape 179740 50 29 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_29_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_30_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 30 50 2293 2534 ≤ 1082426476 := by
  decide +kernel

theorem edge50_30_50_2293_2534 : SpreadInterval.Positive shape 179740 50 30 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_30_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_31_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 31 50 2293 2534 ≤ 1105195622 := by
  decide +kernel

theorem edge50_31_50_2293_2534 : SpreadInterval.Positive shape 179740 50 31 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_31_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_32_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 32 50 2293 2534 ≤ 1128331655 := by
  decide +kernel

theorem edge50_32_50_2293_2534 : SpreadInterval.Positive shape 179740 50 32 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_32_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_33_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 33 50 2293 2534 ≤ 1151859647 := by
  decide +kernel

theorem edge50_33_50_2293_2534 : SpreadInterval.Positive shape 179740 50 33 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_33_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_34_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 34 50 2293 2534 ≤ 1175669309 := by
  decide +kernel

theorem edge50_34_50_2293_2534 : SpreadInterval.Positive shape 179740 50 34 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_34_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_35_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 35 50 2293 2534 ≤ 1199857443 := by
  decide +kernel

theorem edge50_35_50_2293_2534 : SpreadInterval.Positive shape 179740 50 35 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_35_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_36_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 36 50 2293 2534 ≤ 1224225443 := by
  decide +kernel

theorem edge50_36_50_2293_2534 : SpreadInterval.Positive shape 179740 50 36 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_36_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_37_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 37 50 2293 2534 ≤ 1248962585 := by
  decide +kernel

theorem edge50_37_50_2293_2534 : SpreadInterval.Positive shape 179740 50 37 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_37_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0669

-- Source: Research6969.SpreadEdges08
section Z6969Source0670
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge50_38_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 38 50 2293 2534 ≤ 1273802531 := by
  decide +kernel

theorem edge50_38_50_2293_2534 : SpreadInterval.Positive shape 179740 50 38 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_38_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_39_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 39 50 2293 2534 ≤ 1299058669 := by
  decide +kernel

theorem edge50_39_50_2293_2534 : SpreadInterval.Positive shape 179740 50 39 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_39_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge50_40_50_2293_2534_cost : SpreadInterval.costSum shape 179740 50 40 50 2293 2534 ≤ 1324518537 := by
  decide +kernel

theorem edge50_40_50_2293_2534 : SpreadInterval.Positive shape 179740 50 40 50 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge50_40_50_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_4_56_2293_2534_cost : SpreadInterval.costSum shape 179740 64 4 56 2293 2534 ≤ 1224064279 := by
  decide +kernel

theorem edge64_4_56_2293_2534 : SpreadInterval.Positive shape 179740 64 4 56 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_4_56_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_5_57_2293_2534_cost : SpreadInterval.costSum shape 179740 64 5 57 2293 2534 ≤ 1117389973 := by
  decide +kernel

theorem edge64_5_57_2293_2534 : SpreadInterval.Positive shape 179740 64 5 57 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_5_57_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_6_58_2293_2534_cost : SpreadInterval.costSum shape 179740 64 6 58 2293 2534 ≤ 1023362350 := by
  decide +kernel

theorem edge64_6_58_2293_2534 : SpreadInterval.Positive shape 179740 64 6 58 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_6_58_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_7_59_2293_2534_cost : SpreadInterval.costSum shape 179740 64 7 59 2293 2534 ≤ 948372622 := by
  decide +kernel

theorem edge64_7_59_2293_2534 : SpreadInterval.Positive shape 179740 64 7 59 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_7_59_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_8_60_2293_2534_cost : SpreadInterval.costSum shape 179740 64 8 60 2293 2534 ≤ 890086338 := by
  decide +kernel

theorem edge64_8_60_2293_2534 : SpreadInterval.Positive shape 179740 64 8 60 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_8_60_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_9_61_2293_2534_cost : SpreadInterval.costSum shape 179740 64 9 61 2293 2534 ≤ 844994971 := by
  decide +kernel

theorem edge64_9_61_2293_2534 : SpreadInterval.Positive shape 179740 64 9 61 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_9_61_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_10_62_2293_2534_cost : SpreadInterval.costSum shape 179740 64 10 62 2293 2534 ≤ 810100321 := by
  decide +kernel

theorem edge64_10_62_2293_2534 : SpreadInterval.Positive shape 179740 64 10 62 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_10_62_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0670

-- Source: Research6969.SpreadEdges09
section Z6969Source0671
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge64_11_63_2293_2534_cost : SpreadInterval.costSum shape 179740 64 11 63 2293 2534 ≤ 783095962 := by
  decide +kernel

theorem edge64_11_63_2293_2534 : SpreadInterval.Positive shape 179740 64 11 63 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_11_63_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_12_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 12 64 2293 2534 ≤ 762240060 := by
  decide +kernel

theorem edge64_12_64_2293_2534 : SpreadInterval.Positive shape 179740 64 12 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_12_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_33_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 33 64 2293 2534 ≤ 941041852 := by
  decide +kernel

theorem edge64_33_64_2293_2534 : SpreadInterval.Positive shape 179740 64 33 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_33_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_34_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 34 64 2293 2534 ≤ 958495553 := by
  decide +kernel

theorem edge64_34_64_2293_2534 : SpreadInterval.Positive shape 179740 64 34 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_34_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_35_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 35 64 2293 2534 ≤ 976337428 := by
  decide +kernel

theorem edge64_35_64_2293_2534 : SpreadInterval.Positive shape 179740 64 35 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_35_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_36_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 36 64 2293 2534 ≤ 994361725 := by
  decide +kernel

theorem edge64_36_64_2293_2534 : SpreadInterval.Positive shape 179740 64 36 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_36_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_37_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 37 64 2293 2534 ≤ 1012749160 := by
  decide +kernel

theorem edge64_37_64_2293_2534 : SpreadInterval.Positive shape 179740 64 37 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_37_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_38_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 38 64 2293 2534 ≤ 1031227210 := by
  decide +kernel

theorem edge64_38_64_2293_2534 : SpreadInterval.Positive shape 179740 64 38 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_38_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_39_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 39 64 2293 2534 ≤ 1050121884 := by
  decide +kernel

theorem edge64_39_64_2293_2534 : SpreadInterval.Positive shape 179740 64 39 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_39_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_40_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 40 64 2293 2534 ≤ 1069241566 := by
  decide +kernel

theorem edge64_40_64_2293_2534 : SpreadInterval.Positive shape 179740 64 40 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_40_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0671

-- Source: Research6969.SpreadEdges10
section Z6969Source0672
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge64_41_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 41 64 2293 2534 ≤ 1088315141 := by
  decide +kernel

theorem edge64_41_64_2293_2534 : SpreadInterval.Positive shape 179740 64 41 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_41_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_42_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 42 64 2293 2534 ≤ 1107859191 := by
  decide +kernel

theorem edge64_42_64_2293_2534 : SpreadInterval.Positive shape 179740 64 42 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_42_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_43_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 43 64 2293 2534 ≤ 1127304257 := by
  decide +kernel

theorem edge64_43_64_2293_2534 : SpreadInterval.Positive shape 179740 64 43 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_43_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_44_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 44 64 2293 2534 ≤ 1146823257 := by
  decide +kernel

theorem edge64_44_64_2293_2534 : SpreadInterval.Positive shape 179740 64 44 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_44_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_45_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 45 64 2293 2534 ≤ 1166489344 := by
  decide +kernel

theorem edge64_45_64_2293_2534 : SpreadInterval.Positive shape 179740 64 45 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_45_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_46_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 46 64 2293 2534 ≤ 1186741522 := by
  decide +kernel

theorem edge64_46_64_2293_2534 : SpreadInterval.Positive shape 179740 64 46 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_46_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_47_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 47 64 2293 2534 ≤ 1206632400 := by
  decide +kernel

theorem edge64_47_64_2293_2534 : SpreadInterval.Positive shape 179740 64 47 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_47_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_48_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 48 64 2293 2534 ≤ 1227063813 := by
  decide +kernel

theorem edge64_48_64_2293_2534 : SpreadInterval.Positive shape 179740 64 48 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_48_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_49_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 49 64 2293 2534 ≤ 1247403515 := by
  decide +kernel

theorem edge64_49_64_2293_2534 : SpreadInterval.Positive shape 179740 64 49 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_49_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_50_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 50 64 2293 2534 ≤ 1268103484 := by
  decide +kernel

theorem edge64_50_64_2293_2534 : SpreadInterval.Positive shape 179740 64 50 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_50_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0672

-- Source: Research6969.SpreadEdges11
section Z6969Source0673
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge64_51_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 51 64 2293 2534 ≤ 1288039344 := by
  decide +kernel

theorem edge64_51_64_2293_2534 : SpreadInterval.Positive shape 179740 64 51 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_51_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_52_64_2293_2534_cost : SpreadInterval.costSum shape 179740 64 52 64 2293 2534 ≤ 1309054119 := by
  decide +kernel

theorem edge64_52_64_2293_2534 : SpreadInterval.Positive shape 179740 64 52 64 nodes moment 2293 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_52_64_2293_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2294_2294_cost : SpreadInterval.costSum shape 179740 64 3 55 2294 2294 ≤ 1330984696 := by
  decide +kernel

theorem edge64_3_55_2294_2294 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2294 2294 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2294_2294_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2295_2296_cost : SpreadInterval.costSum shape 179740 64 3 55 2295 2296 ≤ 1331010815 := by
  decide +kernel

theorem edge64_3_55_2295_2296 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2295 2296 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2295_2296_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2297_2300_cost : SpreadInterval.costSum shape 179740 64 3 55 2297 2300 ≤ 1331078951 := by
  decide +kernel

theorem edge64_3_55_2297_2300 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2297 2300 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2297_2300_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2301_2308_cost : SpreadInterval.costSum shape 179740 64 3 55 2301 2308 ≤ 1331191165 := by
  decide +kernel

theorem edge64_3_55_2301_2308 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2301 2308 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2301_2308_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2309_2323_cost : SpreadInterval.costSum shape 179740 64 3 55 2309 2323 ≤ 1331401835 := by
  decide +kernel

theorem edge64_3_55_2309_2323 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2309 2323 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2309_2323_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2324_2353_cost : SpreadInterval.costSum shape 179740 64 3 55 2324 2353 ≤ 1331811970 := by
  decide +kernel

theorem edge64_3_55_2324_2353 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2324 2353 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2324_2353_cost) _).trans_lt <;>
    decide +kernel

private theorem edge41_32_41_2354_2413_cost : SpreadInterval.costSum shape 179740 41 32 41 2354 2413 ≤ 1330851541 := by
  decide +kernel

theorem edge41_32_41_2354_2413 : SpreadInterval.Positive shape 179740 41 32 41 nodes moment 2354 2413 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_32_41_2354_2413_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2354_2413_cost : SpreadInterval.costSum shape 179740 64 3 55 2354 2413 ≤ 1332583780 := by
  decide +kernel

theorem edge64_3_55_2354_2413 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2354 2413 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2354_2413_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0673

-- Source: Research6969.SpreadEdges12
section Z6969Source0674
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxRecDepth 24000
set_option maxHeartbeats 0

private theorem edge41_32_41_2414_2534_cost : SpreadInterval.costSum shape 179740 41 32 41 2414 2534 ≤ 1332149821 := by
  decide +kernel

theorem edge41_32_41_2414_2534 : SpreadInterval.Positive shape 179740 41 32 41 nodes moment 2414 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge41_32_41_2414_2534_cost) _).trans_lt <;>
    decide +kernel

private theorem edge64_3_55_2414_2534_cost : SpreadInterval.costSum shape 179740 64 3 55 2414 2534 ≤ 1333916106 := by
  decide +kernel

theorem edge64_3_55_2414_2534 : SpreadInterval.Positive shape 179740 64 3 55 nodes moment 2414 2534 box := by
  unfold SpreadInterval.Positive
  dsimp only
  constructor <;>
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ edge64_3_55_2414_2534_cost) _).trans_lt <;>
    decide +kernel

end Research6969.SpreadCatalogue
end Z6969Source0674

-- Source: Research6969.SpreadCatalogue
section Z6969Source0675
set_option autoImplicit true
namespace Research6969.SpreadCatalogue
open Research6966
set_option maxHeartbeats 1200000

theorem case22_7_20 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 22 7 20 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge22_7_20_2293_2534

theorem case22_8_21 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 22 8 21 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge22_8_21_2293_2534

theorem case22_9_22 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 22 9 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge22_9_22_2293_2534

theorem case22_12_22 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 22 12 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge22_12_22_2293_2534

theorem case22_13_22 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 22 13 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge22_13_22_2293_2534

theorem case23_7_21 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 23 7 21 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge23_7_21_2293_2534

theorem case23_8_22 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 23 8 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge23_8_22_2293_2534

theorem case23_9_23 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 23 9 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge23_9_23_2293_2534

theorem case23_12_23 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 23 12 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge23_12_23_2293_2534

theorem case23_13_23 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 23 13 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge23_13_23_2293_2534

theorem case23_14_23 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 23 14 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge23_14_23_2293_2534

theorem case25_6_22 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 6 22 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_6_22_2293_2534

theorem case25_7_23 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 7 23 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_7_23_2293_2534

theorem case25_8_24 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 8 24 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_8_24_2293_2534

theorem case25_9_25 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 9 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_9_25_2293_2534

theorem case25_13_25 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 13 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_13_25_2293_2534

theorem case25_14_25 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 14 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_14_25_2293_2534

theorem case25_15_25 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 15 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_15_25_2293_2534

theorem case25_16_25 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 25 16 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge25_16_25_2293_2534

theorem case28_5_24 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 5 24 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_5_24_2293_2534

theorem case28_6_25 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 6 25 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_6_25_2293_2534

theorem case28_7_26 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 7 26 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_7_26_2293_2534

theorem case28_8_27 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 8 27 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_8_27_2293_2534

theorem case28_9_28 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 9 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_9_28_2293_2534

theorem case28_15_28 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 15 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_15_28_2293_2534

theorem case28_16_28 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 16 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_16_28_2293_2534

theorem case28_17_28 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 17 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_17_28_2293_2534

theorem case28_18_28 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 18 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_18_28_2293_2534

theorem case28_19_28 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 28 19 28 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge28_19_28_2293_2534

theorem case33_5_29 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 5 29 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_5_29_2293_2534

theorem case33_6_30 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 6 30 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_6_30_2293_2534

theorem case33_7_31 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 7 31 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_7_31_2293_2534

theorem case33_8_32 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 8 32 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_8_32_2293_2534

theorem case33_9_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 9 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_9_33_2293_2534

theorem case33_17_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 17 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_17_33_2293_2534

theorem case33_18_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 18 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_18_33_2293_2534

theorem case33_19_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 19 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_19_33_2293_2534

theorem case33_20_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 20 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_20_33_2293_2534

theorem case33_21_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 21 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_21_33_2293_2534

theorem case33_22_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 22 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_22_33_2293_2534

theorem case33_23_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 23 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_23_33_2293_2534

theorem case33_24_33 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 33 24 33 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge33_24_33_2293_2534

theorem case41_4_36 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 4 36 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_4_36_2293_2534

theorem case41_5_37 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 5 37 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_5_37_2293_2534

theorem case41_6_38 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 6 38 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_6_38_2293_2534

theorem case41_7_39 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 7 39 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_7_39_2293_2534

theorem case41_8_40 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 8 40 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_8_40_2293_2534

theorem case41_9_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 9 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_9_41_2293_2534

theorem case41_21_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 21 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_21_41_2293_2534

theorem case41_22_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 22 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_22_41_2293_2534

theorem case41_23_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 23 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_23_41_2293_2534

theorem case41_24_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 24 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_24_41_2293_2534

theorem case41_25_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 25 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_25_41_2293_2534

theorem case41_26_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 26 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_26_41_2293_2534

theorem case41_27_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 27 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_27_41_2293_2534

theorem case41_28_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 28 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_28_41_2293_2534

theorem case41_29_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 29 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_29_41_2293_2534

theorem case41_30_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 30 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_30_41_2293_2534

theorem case41_31_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 31 41 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_31_41_2293_2534

theorem case41_32_41 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 41 32 41 shape box nodes moment := by
  by_cases bound0 : h ≤ 2353
  · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge41_32_41_2293_2353
  ·
    by_cases bound1 : h ≤ 2413
    · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) edge41_32_41_2354_2413
    ·
      exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) edge41_32_41_2414_2534

theorem case50_4_44 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 4 44 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_4_44_2293_2534

theorem case50_5_45 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 5 45 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_5_45_2293_2534

theorem case50_6_46 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 6 46 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_6_46_2293_2534

theorem case50_7_47 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 7 47 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_7_47_2293_2534

theorem case50_8_48 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 8 48 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_8_48_2293_2534

theorem case50_9_49 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 9 49 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_9_49_2293_2534

theorem case50_10_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 10 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_10_50_2293_2534

theorem case50_26_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 26 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_26_50_2293_2534

theorem case50_27_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 27 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_27_50_2293_2534

theorem case50_28_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 28 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_28_50_2293_2534

theorem case50_29_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 29 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_29_50_2293_2534

theorem case50_30_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 30 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_30_50_2293_2534

theorem case50_31_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 31 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_31_50_2293_2534

theorem case50_32_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 32 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_32_50_2293_2534

theorem case50_33_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 33 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_33_50_2293_2534

theorem case50_34_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 34 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_34_50_2293_2534

theorem case50_35_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 35 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_35_50_2293_2534

theorem case50_36_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 36 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_36_50_2293_2534

theorem case50_37_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 37 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_37_50_2293_2534

theorem case50_38_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 38 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_38_50_2293_2534

theorem case50_39_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 39 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_39_50_2293_2534

theorem case50_40_50 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 50 40 50 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge50_40_50_2293_2534

theorem case64_3_55 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 3 55 shape box nodes moment := by
  by_cases bound0 : h ≤ 2293
  · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_3_55_2293_2293
  ·
    by_cases bound1 : h ≤ 2294
    · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) edge64_3_55_2294_2294
    ·
      by_cases bound2 : h ≤ 2296
      · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) edge64_3_55_2295_2296
      ·
        by_cases bound3 : h ≤ 2300
        · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) edge64_3_55_2297_2300
        ·
          by_cases bound4 : h ≤ 2308
          · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) edge64_3_55_2301_2308
          ·
            by_cases bound5 : h ≤ 2323
            · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) edge64_3_55_2309_2323
            ·
              by_cases bound6 : h ≤ 2353
              · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) edge64_3_55_2324_2353
              ·
                by_cases bound7 : h ≤ 2413
                · exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
                    (by decide) (by decide) (by decide) (by decide) edge64_3_55_2354_2413
                ·
                  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
                      (by decide) (by decide) (by decide) (by decide) edge64_3_55_2414_2534

theorem case64_4_56 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 4 56 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_4_56_2293_2534

theorem case64_5_57 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 5 57 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_5_57_2293_2534

theorem case64_6_58 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 6 58 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_6_58_2293_2534

theorem case64_7_59 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 7 59 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_7_59_2293_2534

theorem case64_8_60 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 8 60 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_8_60_2293_2534

theorem case64_9_61 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 9 61 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_9_61_2293_2534

theorem case64_10_62 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 10 62 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_10_62_2293_2534

theorem case64_11_63 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 11 63 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_11_63_2293_2534

theorem case64_12_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 12 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_12_64_2293_2534

theorem case64_33_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 33 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_33_64_2293_2534

theorem case64_34_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 34 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_34_64_2293_2534

theorem case64_35_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 35 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_35_64_2293_2534

theorem case64_36_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 36 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_36_64_2293_2534

theorem case64_37_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 37 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_37_64_2293_2534

theorem case64_38_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 38 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_38_64_2293_2534

theorem case64_39_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 39 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_39_64_2293_2534

theorem case64_40_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 40 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_40_64_2293_2534

theorem case64_41_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 41 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_41_64_2293_2534

theorem case64_42_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 42 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_42_64_2293_2534

theorem case64_43_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 43 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_43_64_2293_2534

theorem case64_44_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 44 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_44_64_2293_2534

theorem case64_45_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 45 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_45_64_2293_2534

theorem case64_46_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 46 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_46_64_2293_2534

theorem case64_47_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 47 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_47_64_2293_2534

theorem case64_48_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 48 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_48_64_2293_2534

theorem case64_49_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 49 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_49_64_2293_2534

theorem case64_50_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 50 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_50_64_2293_2534

theorem case64_51_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 51 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_51_64_2293_2534

theorem case64_52_64 {h : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534) :
    PadeCutoff.excluded 179740 h 64 52 64 shape box nodes moment := by
  exact SpreadInterval.excluded (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) edge64_52_64_2293_2534

theorem partial22 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 6 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179740 h 22 a (22-9+a) shape box nodes moment := by
  interval_cases a
  · exact case22_7_20 lo hi
  · exact case22_8_21 lo hi
  · exact case22_9_22 lo hi

theorem full22 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 12 ≤ a) (aHi : a ≤ 13) :
    PadeCutoff.excluded 179740 h 22 a 22 shape box nodes moment := by
  interval_cases a
  · exact case22_12_22 lo hi
  · exact case22_13_22 lo hi

theorem partial23 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 6 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179740 h 23 a (23-9+a) shape box nodes moment := by
  interval_cases a
  · exact case23_7_21 lo hi
  · exact case23_8_22 lo hi
  · exact case23_9_23 lo hi

theorem full23 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 12 ≤ a) (aHi : a ≤ 14) :
    PadeCutoff.excluded 179740 h 23 a 23 shape box nodes moment := by
  interval_cases a
  · exact case23_12_23 lo hi
  · exact case23_13_23 lo hi
  · exact case23_14_23 lo hi

theorem partial25 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 5 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179740 h 25 a (25-9+a) shape box nodes moment := by
  interval_cases a
  · exact case25_6_22 lo hi
  · exact case25_7_23 lo hi
  · exact case25_8_24 lo hi
  · exact case25_9_25 lo hi

theorem full25 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 13 ≤ a) (aHi : a ≤ 16) :
    PadeCutoff.excluded 179740 h 25 a 25 shape box nodes moment := by
  interval_cases a
  · exact case25_13_25 lo hi
  · exact case25_14_25 lo hi
  · exact case25_15_25 lo hi
  · exact case25_16_25 lo hi

theorem partial28 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 4 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179740 h 28 a (28-9+a) shape box nodes moment := by
  interval_cases a
  · exact case28_5_24 lo hi
  · exact case28_6_25 lo hi
  · exact case28_7_26 lo hi
  · exact case28_8_27 lo hi
  · exact case28_9_28 lo hi

theorem full28 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 15 ≤ a) (aHi : a ≤ 19) :
    PadeCutoff.excluded 179740 h 28 a 28 shape box nodes moment := by
  interval_cases a
  · exact case28_15_28 lo hi
  · exact case28_16_28 lo hi
  · exact case28_17_28 lo hi
  · exact case28_18_28 lo hi
  · exact case28_19_28 lo hi

theorem partial33 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 4 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179740 h 33 a (33-9+a) shape box nodes moment := by
  interval_cases a
  · exact case33_5_29 lo hi
  · exact case33_6_30 lo hi
  · exact case33_7_31 lo hi
  · exact case33_8_32 lo hi
  · exact case33_9_33 lo hi

theorem full33 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 17 ≤ a) (aHi : a ≤ 24) :
    PadeCutoff.excluded 179740 h 33 a 33 shape box nodes moment := by
  interval_cases a
  · exact case33_17_33 lo hi
  · exact case33_18_33 lo hi
  · exact case33_19_33 lo hi
  · exact case33_20_33 lo hi
  · exact case33_21_33 lo hi
  · exact case33_22_33 lo hi
  · exact case33_23_33 lo hi
  · exact case33_24_33 lo hi

theorem partial41 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 3 < a) (aHi : a ≤ 9) :
    PadeCutoff.excluded 179740 h 41 a (41-9+a) shape box nodes moment := by
  interval_cases a
  · exact case41_4_36 lo hi
  · exact case41_5_37 lo hi
  · exact case41_6_38 lo hi
  · exact case41_7_39 lo hi
  · exact case41_8_40 lo hi
  · exact case41_9_41 lo hi

theorem full41 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 21 ≤ a) (aHi : a ≤ 32) :
    PadeCutoff.excluded 179740 h 41 a 41 shape box nodes moment := by
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

theorem partial50 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 3 < a) (aHi : a ≤ 10) :
    PadeCutoff.excluded 179740 h 50 a (50-10+a) shape box nodes moment := by
  interval_cases a
  · exact case50_4_44 lo hi
  · exact case50_5_45 lo hi
  · exact case50_6_46 lo hi
  · exact case50_7_47 lo hi
  · exact case50_8_48 lo hi
  · exact case50_9_49 lo hi
  · exact case50_10_50 lo hi

theorem full50 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 26 ≤ a) (aHi : a ≤ 40) :
    PadeCutoff.excluded 179740 h 50 a 50 shape box nodes moment := by
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

theorem partial64 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 2 < a) (aHi : a ≤ 12) :
    PadeCutoff.excluded 179740 h 64 a (64-12+a) shape box nodes moment := by
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

theorem full64 {h a : ℕ} (lo : 2293 ≤ h) (hi : h ≤ 2534)
    (aLo : 33 ≤ a) (aHi : a ≤ 52) :
    PadeCutoff.excluded 179740 h 64 a 64 shape box nodes moment := by
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
  terminal : ∀ q∈parents,TerminalBanks.Pass Crt (word M) 179740 Research6969.SpreadCatalogue.shape q
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
      (HelperSource.cutoffCount outer.shape 179740 M.overhead.toNat 10-1)) G)
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
  have hiAll : M.overhead.toNat≤2534 := hi.trans (by cases band <;> decide)
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
    (lo : 2293 ≤ M.overhead.toNat) (hi : M.overhead.toNat ≤ 2389)
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
        jetDegree R.out.exception * 128682 - 1 ≤ RawPhysicalDegree.weight
          (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw := by
  obtain ⟨R⟩ := Prefix6969Wide.rows F Crt lo hi noPole residues
  refine ⟨R, ?_⟩
  rcases R.out.kind with unit | common
  · exact Or.inl unit
  have hiAll : M.overhead.toNat ≤ 33735 := hi.trans (by decide)
  obtain ⟨line, jd, jmax, sd, smax, nonlinear⟩ :=
    Prefix6969Helper.helper_common_caps Crt (word M) lo hiAll
      common.1 common.2.2.1 common.2.1 common.2.2.2
  obtain ⟨phys⟩ := HelperPhysicalModel.exists_model Crt common.1 common.2.1
  have hraw : 0 < 131071-M.overhead.toNat := by omega
  have lower := HelperWeightCap.weight_lower phys common.1.ne_zero _ hraw
  have endpoint : 128682 ≤ 131071-M.overhead.toNat := by omega
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
  p*61+(3*(133460*61)^2*(262144-133460)^3)/(179740-133460)^3

private theorem affine_roots {u deleted} {M : Model u deleted} {Γ T : Finset K}
    (F : Family M Γ) (sub : T⊆Γ) (hi : M.overhead.toNat≤2389)
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
    (by decide) 133460 (by omega) (by decide) (by decide) (by decide) (by decide) own

/-- The refitted actual main packet transfers when the outer exception is
a unit or its affine zero marks have been paid. -/
theorem ordinary {u del} {M : Model u del} {Γ} {F : Family M Γ}
    {D : PoleData M.overhead.toNat} {Crt : CRTLift D}
    (R : Prefix6969Wide.Rows F Crt)
    (hi : M.overhead.toNat≤2389)
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
open Research6969.FarProfileArithmetic (value value_eq)
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

private theorem compressedSurplus_eq (h : ℕ) (test : HelperTest) (hi : h ≤ 2391) :
    compressedSurplus h test = surplus (bankAt test.cap) 179740 h 10 test.slope test.excess test.seed :=
  value_eq (helperRequest test) h (by cases test <;> decide)
    (by change 170 < 131071 - h; omega)

private theorem twoSlopes_first : compressedSurplus 2390 .twoSlopes = 26531553679225 := by decide +kernel
private theorem twoSlopes_next : compressedSurplus 2391 .twoSlopes = 926538774202524 := by decide +kernel
private theorem seedBoundary_first : compressedSurplus 2390 .seedBoundary = 130363507147744365 := by decide +kernel
private theorem seedBoundary_next : compressedSurplus 2391 .seedBoundary = 131318047710755838 := by decide +kernel
private theorem mixedBoundary_first : compressedSurplus 2390 .mixedBoundary = 119460991646899405 := by decide +kernel
private theorem mixedBoundary_next : compressedSurplus 2391 .mixedBoundary = 120410971444867566 := by decide +kernel
private theorem jetBoundary_first : compressedSurplus 2390 .jetBoundary = 50023108111942725 := by decide +kernel
private theorem jetBoundary_next : compressedSurplus 2391 .jetBoundary = 50944034402155674 := by decide +kernel

theorem helper_surplus (test : HelperTest) {h : ℕ} (lo : 2390≤h) (hi : h≤33735) :
    debit h (bankAt test.cap) < gain (bankAt test.cap).shape 179740 h 10 test.slope test.excess test.seed := by
  apply surplus_positive _ _ 2390 _ _ _ _ _ lo (by omega)
  · rw [← compressedSurplus_eq _ _ (by decide)]
    cases test
    · rw [twoSlopes_first]; decide
    · rw [seedBoundary_first]; decide
    · rw [mixedBoundary_first]; decide
    · rw [jetBoundary_first]; decide
  · change surplus (bankAt test.cap) 179740 2390 10 test.slope test.excess test.seed ≤
      surplus (bankAt test.cap) 179740 2391 10 test.slope test.excess test.seed
    rw [← compressedSurplus_eq 2390 test (by decide), ← compressedSurplus_eq 2391 test (by decide)]
    cases test
    · rw [twoSlopes_first, twoSlopes_next]; decide
    · rw [seedBoundary_first, seedBoundary_next]; decide
    · rw [mixedBoundary_first, mixedBoundary_next]; decide
    · rw [jetBoundary_first, jetBoundary_next]; decide
theorem helper_width {h : ℕ} (lo : 2390≤h) (hi : h≤33735) :
    WidthGuard helperBank 179740 h 10 :=
  width_at_height _ _ 2390 _ _ lo (by omega) (by decide) (by unfold WidthGuard; decide +kernel)
def helperCutoff (h : ℕ) : ℕ := cutoffCount helperBank.shape 179740 h 10-1
theorem helper_avoids {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2390≤h) (hi : h≤33735) (test : HelperTest) {G : Jet} (irr : Irreducible G)
    (seeded : UsesSeed G) (slope : test.slope≤G.natDegree) (seed : test.seed≤seedDegree G)
    (excess : G.natDegree+test.excess≤jetDegree G) :
    ∃ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), ¬ G∣Q := by
  obtain ⟨Q,inside,avoids⟩ := crt_avoiding_row Crt word (bankAt test.cap) 179740 10 test.slope test.excess test.seed
    (by omega) (by omega) (by cases test <;> decide)
    (checked test.cap).nodes (checked test.cap).moment.1 (checked test.cap).moment.2
    (by cases test <;> decide) (helper_width lo hi) (helper_surplus test lo hi) irr seeded slope seed excess
  exact ⟨Q, K1_14_1.evaluated_mono Crt word (s:=(bankAt test.cap).shape) (s':=helperBank.shape)
    rfl rfl rfl (by cases test <;> decide) le_rfl inside, avoids⟩
theorem helper_nonzero {h : ℕ} {D : PoleData h} (Crt : CRTLift D) (word : K1.I → L)
    (lo : 2390≤h) (hi : h≤33735) :
    ∃ P ∈ evaluated Crt word helperBank.shape (helperCutoff h), P≠0 := by
  have sup := crt_supply Crt word helperBank 179740 10 2 0 1 (by omega) (by omega) (by decide)
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
    (lo : 2390≤h) (hi : h≤33735) {G : Jet} (irr : Irreducible G)
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
    (lo : 2390≤h) (hi : h≤33735) {G H : Jet} (g : Irreducible G) (i : Irreducible H)
    (cop : IsRelPrime G H) (gs : 0<G.natDegree) (hs : 0<H.natDegree)
    (gu : UsesSeed G) (hu : UsesSeed H)
    (allG : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), G∣Q)
    (allH : ∀ Q ∈ evaluated Crt word helperBank.shape (helperCutoff h), H∣Q) : False := by
  have supply := crt_supply Crt word helperBank 179740 10 2 0 1 (by omega) (by omega) (by decide)
    helper_bank_checked.nodes helper_bank_checked.moment.1 helper_bank_checked.moment.2
    (helper_width lo hi) (helper_surplus .twoSlopes lo hi)
  obtain ⟨P,hP,np⟩ := helper_nonzero Crt word lo hi
  have hpc (j i : ℕ) : ((P.coeff j).coeff i).totalDegree ≤ helperBank.shape.U := by
    by_cases zero : ((P.coeff j).coeff i)=0
    · simp [zero]
    · exact (evaluated_shape Crt word hP j i zero).2.2
  exact HelperPrefix.not_two_common helperBank.shape h (cutoffCount helperBank.shape 179740 h 10)
    (by omega) (evaluated Crt word helperBank.shape) G H P g i cop gs hs gu hu np hP
    (by decide) hpc (fun _ _ _ hR => evaluated_shape Crt word hR)
    (fun W _ R hR hnR => P0_10_1.leading_bound (by omega) (by omega) Crt word helperBank.shape W R hR hnR)
    (fun _ _ _ hR j a hshift => evaluated_mono Crt word rfl rfl rfl le_rfl hshift
      (P0_10_1.evaluated_shift Crt word hR j a))
    supply allG allH
end Lower6960.Prefix6969MiddleHelper
end Z6969Source0679

end Merged_Z6969Pack0589
