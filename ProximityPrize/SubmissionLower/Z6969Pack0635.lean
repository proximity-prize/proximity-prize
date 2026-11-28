import ProximityPrize.SubmissionLower.Z6969Pack0634
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.R6966ProofNativeAffineTariff
import ProximityPrize.SubmissionLower.Z6969Pack0520
import ProximityPrize.SubmissionLower.R6966ProofNearTerminalFacts
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import Mathlib.Tactic
import ProximityPrize.SubmissionLower.Z6969Pack0528
import ProximityPrize.SubmissionLower.R6966ProofWordSurfaceMarks
import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
import ProximityPrize.SubmissionLower.R6966ProofOdeSurfaceBridge

set_option Elab.async false

-- Source: Research6969.OwnedTariffs
section Z6969Source0833
set_option autoImplicit true
namespace Research6969.OwnedTariffs
noncomputable section
open K1 (K p)
open K1_14 (Equation atX jetAt)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open GraphPartition (Split)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 8500

variable {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ) (sub:T⊆Γ)
variable {parents:Finset Surface} {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
variable (S:Split F T parents N.poly)

theorem owners:NativeAffineRows.Owned F S.onLabels (NearBook.owning N.poly parents) N:=by
  intro z hz
  obtain ⟨q,hq,on⟩:=S.onMarks z hz
  exact ⟨q,hq,(mem_filter.mp hq).2,on⟩

include sub in
theorem marked {v w:ℕ} (high:M.overhead.toNat≤2557)
    (onGrade:S.onEq.natDegree<64) (offGrade:S.offEq.natDegree<64)
    (onSeed:K1_14_4.seedDegree S.onEq≤v) (offSeed:K1_14_4.seedDegree S.offEq≤w)
    (onChar:(2*S.onEq.natDegree-1)*v<p) (offChar:(2*S.offEq.natDegree-1)*w<p) :
    S.onLabels.card≤JointMarked.price S.onEq.natDegree v ∧
    S.offLabels.card≤JointMarked.price S.offEq.natDegree w :=
  ⟨JointMarked.owned_count F (S.onSub.trans sub) high _ S.onProduct.primitive S.onProduct.separable onGrade
     onSeed onChar (GraphPartition.labels_root S).1,
   JointMarked.owned_count F (S.offSub.trans sub) high _ S.offProduct.primitive S.offProduct.separable offGrade
     offSeed offChar (GraphPartition.labels_root S).2⟩

include sub gp
theorem nonlinear {d u v:ℕ} (large:2≤G.graphDegree) (up:0<u)
    (seed:∀j i,((N.poly.coeff j).coeff i).totalDegree≤u) (bound:K1_14_4.seedDegree S.onEq≤v)
    (small:(2*G.graphDegree-1)*u<p) (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p) :
    S.onLabels.card≤(2*G.graphDegree-1)*((p+1)*u)+S.onEq.natDegree*JointRouted.seedWeight d u^2+
      2*v*JointRouted.seedWeight d u*JointRouted.ordWeight d (G.graphDegree-1) := by
  have fit:179730≤Fintype.card K1.I:=by rw [show Fintype.card K1.I=262144 from Fintype.card_fin (2^18)];decide
  have a:=NativeSurfaceCount.price_equation F (S.onSub.trans sub) S.onProduct.primitive.ne_zero N gp large up
    seed ((K1_14_4.seedDegree_le_iff ..).mp bound) small phys dp gap fit tame (by
      intro z hz;obtain ⟨q,_,owned,atQ⟩:=owners F N S z hz
      exact NativeGraphMarks.mark_law N gp owned atQ) (fun z hz=>by
        have root:=(GraphPartition.labels_root S).1 z hz
        simpa [evaluate,NativeSurfaceCount.label,K1_14.graphEval,Polynomial.eval_map] using root)
  exact NativeSurfaceCount.round_price a

theorem affine {d width:ℕ} (linear:G.graphDegree=1) (up:0<width)
    (seed:∀j i,((N.poly.coeff j).coeff i).totalDegree≤width) (small:width<p)
    (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p) :
    S.onLabels.card≤p*width+(3*(d*width)^2*(262144-d)^3)/(179730-d)^3 := by
  apply NativeAffineTariff.price_floor F (S.onSub.trans sub) N gp linear width up _ small d phys tame dp gap
    (by decide) (owners F N S)
  intro j i
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro m hm
  rw [←Finsupp.degree_eq_weight_one]
  exact (MvPolynomial.le_totalDegree hm).trans (seed j i)

end
end Research6969.OwnedTariffs
end Z6969Source0833

-- Source: Research6969.GraphLedger
section Z6969Source0834
set_option autoImplicit true
namespace Research6969.GraphLedger
noncomputable section
open Finset Polynomial
open K1 (K p)
open K1_14 (Equation)
open K1_14_3 (Surface)
open JointLedger (Book coefficient)
open GraphPartition (Split)
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 9000

theorem coefficient_mono : Monotone coefficient := by
  intro i j ij
  unfold coefficient
  apply Nat.mul_le_mul_right
  exact Nat.sub_le_sub_right (Nat.add_le_add (Near6969FactorPrice.rate_mono (max_le_max_left 3 ij))
    (Nat.mul_le_mul_left 2 ij)) _

theorem marked_fee {e n v grade:ℕ} (le:e≤n) (bound:e≤grade) (ge:3≤grade) :
    JointMarked.price e v≤(if n=0 then 0 else coefficient n)*v+grade^2 := by
  by_cases zero:e=0
  · simp [zero,JointMarked.price]
  · have npos:n≠0:=by omega
    rw [JointMarked.price,ite_eq_right zero,ite_eq_right npos,←Nat.mul_assoc]
    have tail:max 3 e-1≤grade:=(Nat.sub_le ..).trans (max_le ge bound)
    change coefficient e*v+(max 3 e-1)*e≤coefficient n*v+grade^2
    rw [pow_two]
    exact Nat.add_le_add (Nat.mul_le_mul_right v (coefficient_mono le)) (Nat.mul_le_mul tail bound)

structure Inputs (b:Book) (gradeCap offCap:ℕ) where
  onDegree:ℕ
  offDegree:ℕ
  onSeed:ℕ
  offSeed:ℕ
  axis:ℕ
  onMarks:ℕ
  offMarks:ℕ
  degreeCap:onDegree≤gradeCap
  offSmall:offDegree≤offCap
  offRoom:offDegree≤gradeCap
  seedCap:onSeed+offSeed≤b.seedMass
  axisCap:axis≤onSeed
  offCost:offMarks≤(if offCap=0 then 0 else coefficient offCap)*offSeed+gradeCap^2

/-- Construct the input to the price ledger from actual projected parents.
The filtered on-graph and off-graph sources partition their seed mass. -/
theorem inputs {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} {F:P1.FamilyAt 179730 M Γ}
    {A G} (S:Split F T A G) (sub:T⊆Γ) (hi:M.overhead.toNat≤2557)
    (book:Book) (gradeCap offCap:ℕ) (ge:3≤gradeCap)
    (J:Finset (Ideal K1_14_2.Ambient)) (active:∀q∈J,K1_14_2_2.Active q)
    (origins:∀q∈A,∃j∈J,q.asIdeal=j.comap K1_14_2.toJet)
    (deg:K1_14_2_2.mass J 0≤gradeCap) (seed:K1_14_2_2.mass J 1≤book.seedMass)
    (off:S.offEq.natDegree≤offCap) (small:offCap<64) (guard:(2*offCap-1)*book.seedMass<p)
    (j:Fin 2) :
    ∃ t:Inputs book gradeCap offCap,
      t.onDegree=S.onEq.natDegree ∧ t.offDegree=S.offEq.natDegree ∧
      t.onSeed=K1_14_4.seedDegree S.onEq ∧ t.offSeed=K1_14_4.seedDegree S.offEq ∧
      t.axis=KoalaRect.axisDegree S.onEq j ∧ t.onMarks=S.onLabels.card ∧ t.offMarks=S.offLabels.card := by
  obtain ⟨ds,ss⟩:=GraphPartition.measured S J active origins
  have mass:=ss.trans seed
  have g:=ds.trans deg
  have val:K1_14_4.seedDegree S.offEq≤book.seedMass:=by omega
  have actual:=JointMarked.owned_count F (S.offSub.trans sub) hi S.offEq S.offProduct.primitive S.offProduct.separable
    (off.trans_lt small) le_rfl ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 off) _) val).trans_lt guard)
    (GraphPartition.labels_root S).2
  have axis:=Research6966.NearBook.axis_total ((K1_14_4.seedDegree_le_iff S.onEq _).mp le_rfl) j
  exact ⟨⟨S.onEq.natDegree,S.offEq.natDegree,K1_14_4.seedDegree S.onEq,K1_14_4.seedDegree S.offEq,
    KoalaRect.axisDegree S.onEq j,S.onLabels.card,S.offLabels.card,by omega,off,by omega,mass,axis,
    actual.trans (marked_fee off (by omega) ge)⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def excess (b:Book) (gradeCap offCap:ℕ) (lo hi seedMax narrowMax:ℕ)
    (constant ordinate seed axisRate:ℤ) : ℤ :=
  let raw:ℤ:=((if offCap=0 then 0 else coefficient offCap):ℕ)
  let offNet:=max 0 (raw-b.seedCredit)
  let c:=seed-b.seedCredit-offNet
  offNet*b.seedMass+(gradeCap:ℤ)^2+constant+
    (ordinate-b.ordinateCredit)*(if 0≤ordinate-b.ordinateCredit then (hi:ℤ) else lo)+
    max 0 c*seedMax+(max 0 (c+axisRate)-max 0 c)*min (narrowMax:ℤ) seedMax

/-- The integer upper bound used by each terminal decision. The same
statement handles the two-axis case, including a negative net grade coefficient. -/
theorem bound {b:Book} {G off:ℕ} (t:Inputs b G off) (lo hi seedMax axisMax:ℕ)
    (constant ordinate seed axisRate:ℤ)
    (onFee:(t.onMarks:ℤ)≤constant+ordinate*t.onDegree+seed*t.onSeed+axisRate*t.axis)
    (lower:lo≤t.onDegree) (upper:t.onDegree≤hi) (seedLimit:t.onSeed≤seedMax) (axisLimit:t.axis≤axisMax)
    (nonneg:0≤axisRate) :
    (t.onMarks:ℤ)+t.offMarks-b.ordinateCredit*((t.onDegree:ℤ)+t.offDegree)-b.seedCredit*((t.onSeed:ℤ)+t.offSeed) ≤
      excess b G off lo hi seedMax axisMax constant ordinate seed axisRate := by
  let raw:ℕ:=if off=0 then 0 else coefficient off
  have oc:(t.offMarks:ℤ)≤(raw:ℤ)*t.offSeed+(G:ℤ)^2:=by exact_mod_cast t.offCost
  have value:=TerminalLedger.split_cost ((t.onMarks:ℤ)+t.offMarks) t.onMarks t.offMarks t.onDegree t.offDegree
    t.onSeed t.offSeed t.axis lo hi seedMax axisMax b.seedMass b.ordinateCredit b.seedCredit raw ((G:ℤ)^2)
    constant ordinate seed axisRate rfl onFee oc
    ⟨by exact_mod_cast lower,by exact_mod_cast upper,by exact_mod_cast seedLimit,by exact_mod_cast axisLimit,by exact_mod_cast t.axisCap⟩
    (by exact_mod_cast t.seedCap) (by positivity) (by positivity) (by positivity) (by positivity) nonneg
  simpa [excess,raw] using value

end
end Research6969.GraphLedger
end Z6969Source0834

-- Source: Research6969.OrdinaryLedger
section Z6969Source0835
set_option autoImplicit true
namespace Research6969.OrdinaryLedger
open JointLedger (Book)
open K1 (p)

def raw (off:ℕ):ℕ:=if off=0 then 0 else JointLedger.coefficient off
def due (m:Book) (gradeCap off minDegree maxOn maxSeed:ℕ) (whole:Bool) (fixed y seed:ℤ):ℤ:=
  let offNet:=max 0 ((raw off:ℤ)-m.seedCredit)
  let ord:ℤ:=if whole then 0 else m.ordinateCredit
  let full:ℤ:=if whole then (m.ordinateCredit:ℤ)*minDegree else 0
  (m.fee:ℤ)+2*(gradeCap:ℤ)^2+offNet*m.seedMass+fixed-full+
    (y-ord)*(if 0≤y-ord then (maxOn:ℤ) else ((minDegree-off:ℕ):ℤ))+
    max 0 (seed-m.seedCredit-offNet)*maxSeed

theorem counts (m:Book) (gradeCap off minDegree maxOn maxSeed:ℕ) (whole:Bool) (fixed y seed:ℤ)
    {total paid onMarks offMarks onDegree offDegree onSeed offSeed:ℕ}
    (coverage:total≤paid+(onMarks+offMarks)) (prefixBill:paid+m.ordinateCredit*(onDegree+offDegree)+
      m.seedCredit*(onSeed+offSeed)≤m.fee) (small:offDegree≤off) (large:minDegree≤onDegree+offDegree)
    (yCap:onDegree≤maxOn) (vCap:onSeed≤maxSeed) (seedBound:onSeed+offSeed≤m.seedMass)
    (onFee:(onMarks:ℤ)≤(gradeCap:ℤ)^2+fixed+y*onDegree+seed*onSeed)
    (offFee:(offMarks:ℤ)≤(raw off:ℤ)*offSeed+(gradeCap:ℤ)^2):
    (total:ℤ)≤due m gradeCap off minDegree maxOn maxSeed whole fixed y seed := by
  let ord:ℤ:=if whole then 0 else m.ordinateCredit
  let extra:ℤ:=if whole then (m.ordinateCredit:ℤ)*minDegree else 0
  have paid':(paid:ℤ)+ord*((onDegree:ℤ)+offDegree)+m.seedCredit*((onSeed:ℤ)+offSeed)+extra ≤m.fee:=by
    have p:(paid:ℤ)+m.ordinateCredit*((onDegree:ℤ)+offDegree)+m.seedCredit*((onSeed:ℤ)+offSeed)≤m.fee:=by exact_mod_cast prefixBill
    cases whole with
    | false=>simpa [ord,extra] using p
    | true=>
      have h:(m.ordinateCredit:ℤ)*minDegree≤m.ordinateCredit*((onDegree:ℤ)+offDegree):=by exact_mod_cast Nat.mul_le_mul_left m.ordinateCredit large
      simp only [ord,extra,ite_true,zero_mul,add_zero]
      linarith
  have ordN:0≤ord:=by cases whole <;> simp [ord]
  have low:minDegree-off≤onDegree:=by omega
  have z:=TerminalLedger.split_cost ((onMarks:ℤ)+offMarks) onMarks offMarks onDegree offDegree
    onSeed offSeed 0 (minDegree-off:ℕ) maxOn maxSeed 0 m.seedMass ord m.seedCredit (raw off) ((gradeCap:ℤ)^2)
    ((gradeCap:ℤ)^2+fixed) y seed 0 rfl (by simpa using onFee) offFee
    ⟨by exact_mod_cast low,by exact_mod_cast yCap,by exact_mod_cast vCap,le_rfl,by positivity⟩
    (by exact_mod_cast seedBound) (by positivity) (by decide) (by positivity) ordN (by decide)
  simp only [add_zero,sub_self,zero_mul,add_zero] at z
  have total':(total:ℤ)≤paid+((onMarks:ℤ)+offMarks):=by exact_mod_cast coverage
  unfold due
  change (total:ℤ)≤_+_+_+fixed-extra+(y-ord)*(if 0≤y-ord then (maxOn:ℤ) else ((minDegree-off:ℕ):ℤ))+_
  linarith only [paid',z,total']

end Research6969.OrdinaryLedger
end Z6969Source0835

-- Source: Research6969.OffFirst
section Z6969Source0836
set_option autoImplicit true
namespace Research6969.OffFirst
noncomputable section
open K1 (K p)
open K1_14 (Jet Equation Seeds SeedBound FX graphEval atX jetAt)
open K1_14_3 (Surface Parent SeedField ProjectedProduct)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open Finset Polynomial
open scoped Classical
set_option maxRecDepth 10000
set_option maxHeartbeats 1300000

/-- The non-native word tariffs are valid on the exclusive quotient because
a label that is not a root of the global off-graph polynomial has an actual
on-graph parent. Counting the entire specialized off factor first also gives
the exact seed credit of the original full projection. -/
structure Parts {u del} {M:P1.ModelAt 33755 u del} {Γ} (F:P1.FamilyAt 179730 M Γ) (T:Finset K)
    (parents:Finset Surface) (G:Jet) (f H J:Equation) where
  onEq:Equation
  offLabels:Finset K
  onLabels:Finset K
  full_eq:f=J*onEq
  divides:onEq∣H
  nz:onEq≠0
  primitive:onEq.IsPrimitive
  separable:(onEq.map (algebraMap Seeds SeedField)).Separable
  degree:J.natDegree+onEq.natDegree=f.natDegree
  seed:K1_14_4.seedDegree J+K1_14_4.seedDegree onEq=K1_14_4.seedDegree f
  onSub:onLabels⊆T
  offSub:offLabels⊆T
  partition:onLabels.card+offLabels.card=T.card
  onRoots:∀z∈onLabels,(onEq.map (graphEval (M.label z))).eval (atX (F.scalar z))=0
  offRoots:∀z∈offLabels,(J.map (graphEval (M.label z))).eval (atX (F.scalar z))=0
  onSurface:∀z∈onLabels,∃q∈NearBook.owning G parents,GraphPartition.On F q z

theorem parts {u del} {M:P1.ModelAt 33755 u del} {Γ} (F:P1.FamilyAt 179730 M Γ) {T:Finset K}
    (parents:Finset Surface) (G:Jet) {f H J:Equation} (full:JointProjection.Product parents f)
    (on:JointProjection.Product (NearBook.owning G parents) H) (off:JointProjection.Product (NearBook.outside G parents) J)
    (marks:∀z∈T,∃q∈parents,GraphPartition.On F q z) : Nonempty (Parts F T parents G f H J) := by
  classical
  have union:NearBook.outside G parents∪NearBook.owning G parents=parents:=by
    ext q;simp only [NearBook.outside,NearBook.owning,mem_union,mem_filter];tauto
  obtain ⟨Q,eq,dvd,nz,deg,sep⟩:=JointProjection.exclusive off on (union ▸ full)
  let val (z:K):Equation→+*FX:=eval₂RingHom (graphEval (M.label z)) (atX (F.scalar z))
  let B:=T.filter (fun z=>val z J=0)
  let A:=T\B
  have cap:B⊆T:=filter_subset _ _
  have aSub:A⊆T:=sdiff_subset
  have miss z (hz:z∈A):val z J≠0:=fun hit=>(mem_sdiff.mp hz).2 (mem_filter.mpr ⟨aSub hz,hit⟩)
  have from_mark z (q:Surface) (atQ:GraphPartition.On F q z) (s:Equation) (mem:C s∈q.asIdeal): val z s=0:=by
    simpa only [jetAt,Polynomial.eval₂_C,Polynomial.coe_eval₂RingHom,val] using atQ _ mem
  have root z (hz:z∈A): val z Q=0:=by
    obtain ⟨q,hq,atQ⟩:=marks z (aSub hz)
    have h:=from_mark z q atQ f (full.vanishes hq)
    rw [eq,map_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (miss z hz)
  have read (z) (q:Equation):val z q=(q.map (graphEval (M.label z))).eval (atX (F.scalar z)):=by simp [val,Polynomial.eval_map]
  refine ⟨⟨Q,B,A,eq,dvd,nz,(JointProjection.remainder on dvd).1,sep,deg,?_,aSub,cap,card_sdiff_add_card_eq_card cap,
    fun z hz=>(read z Q).symm.trans (root z hz),fun z hz=>(read z J).symm.trans (mem_filter.mp hz).2,?_⟩⟩
  · rw [eq,K1_14_4.seedDegree_mul off.primitive.ne_zero nz]
  · intro z hz
    obtain ⟨q,hq,atQ⟩:=marks z (aSub hz)
    by_cases owner:G∈q.asIdeal
    · exact ⟨q,mem_filter.mpr ⟨hq,owner⟩,atQ⟩
    · exact (miss z hz (from_mark z q atQ J (off.vanishes (mem_filter.mpr ⟨hq,owner⟩)))).elim

end
end Research6969.OffFirst
end Z6969Source0836

-- Source: Research6969.EmbeddingDegree
section Z6969Source0837
set_option autoImplicit true
namespace Research6969.EmbeddingDegree
noncomputable section
open MvPolynomial Filter
open scoped BigOperators Topology

/-- The degree of all of one ordinate and two seeds in the fixed bidegree embedding. -/
theorem ambient {F:Type*} [Field F] {a b:ℕ} (ha:0<a) (hb:0<b) :
    affineDegree (RingHom.ker (bidegreeMap (Fin 2) F a b)) ≤ (3*a*b^2 : ℕ) := by
  let I:=RingHom.ker (bidegreeMap (Fin 2) F a b)
  have dim : (affineHilbertPolynomial I).natDegree=3 := by
    simpa [I,Nat.card_eq_fintype_card] using
      (natDegree_affineHilbertPolynomial_ker_bidegreeMap (σ:=Fin 2) (k:=F) ha hb)
  let c₃ : ℚ := (a:ℚ)*b^2/2
  let c₂ : ℚ := (3*(a:ℚ)*b+b^2)/2
  let c₁ : ℚ := (2*(a:ℚ)+3*b)/2
  let P : Polynomial ℚ := Polynomial.monomial 3 c₃ + Polynomial.monomial 2 c₂ +
    Polynomial.monomial 1 c₁ + 1
  have pd : P.natDegree≤3 := by
    dsimp [P]
    compute_degree
  have coeff : P.coeff 3=c₃ := by
    simp [P,Polynomial.coeff_one]
  have size (N:ℕ) : affineHilbertFunction I N≤(a*N+1)*(b*N+2).choose 2 := by
    rw [show I=(⊥:Ideal (MvPolynomial (Option (Fin 2)) F)).comap (bidegreeMap (Fin 2) F a b) from
      RingHom.ker_eq_comap_bot _]
    apply (affineHilbertFunction_comap_bidegreeMap_le _ a b N).trans
    apply (Submodule.finrank_map_le _ _).trans
    simpa only [finrank_restrictBidegree,Nat.card_eq_fintype_card,Fintype.card_fin] using
      (le_rfl : Module.finrank F (restrictBidegree (Fin 2) F (a*N) (b*N))≤_)
  have evaluated (N:ℕ) : P.eval (N:ℚ)=((a*N+1)*(b*N+2).choose 2:ℕ) := by
    have bin:=Nat.choose_succ_right_eq (b*N+2) 1
    rw [Nat.choose_one_right,show b*N+2-1=b*N+1 from by omega] at bin
    have castBin : (2:ℚ)*((b*N+2).choose 2:ℕ)=((b*N:ℕ)+1:ℚ)*((b*N:ℕ)+2:ℚ) := by
      exact_mod_cast (show 2*(b*N+2).choose 2=(b*N+1)*(b*N+2) by nlinarith only [bin])
    simp only [P,Polynomial.eval_add,Polynomial.eval_monomial,Polynomial.eval_one,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    dsimp [c₁,c₂,c₃]
    push_cast at castBin ⊢
    linear_combination -((a:ℚ)*N+1)/2*castBin
  have bound:=affineDegree_le_of_eventually_affineHilbertFunction_le dim pd
    (Filter.Eventually.of_forall (fun N=>by rw [evaluated];exact_mod_cast size N))
  rw [coeff] at bound
  calc _ ≤ (Nat.factorial 3:ℚ)*c₃ := bound
    _ = _ := by dsimp [c₃];norm_num;push_cast;ring

end
end Research6969.EmbeddingDegree
end Z6969Source0837

-- Source: Research6969.AmbientWords
section Z6969Source0838
set_option autoImplicit true
namespace Research6969.AmbientWords
noncomputable section
open K1 (K I p node)
open K1_14 (FX atX)
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open MarkedAdaptive (Coordinates price)
open MvPolynomial Finset
open scoped Classical Differential
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds
set_option maxRecDepth 6000

/-- The unrestricted regular-word price in the same fixed embedding used on individual surfaces. -/
theorem count {r u d a:ℕ} (rp:1≤r) (up:0<u) (dp:0<d) (gap:d<a) (possible:a≤Fintype.card I) (tame:d<p)
    (A B:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) u A) (bz:cap (fun _=>1) u B)
    (W:Finset (Coordinates r u)) (words:Coordinates r u→Polynomial K)
    (params:Coordinates r u→Fin 2→FX) (recv:I→K)
    (original:∀ x∈W,x=monomialPoint (bidegreeExponents (Fin 2) r u)
      (OdeEmbedding.point (params x) (atX (words x))))
    (distinct:Set.InjOn words (W:Set _)) (degree:∀ x∈W,(words x).natDegree≤d)
    (fixed:∀ x∈W,∀ j,Differential.deriv (params x j)=0)
    (law:∀ x∈W,evaluate (params x) (atX (words x)) A * atX (words x).derivative =
      evaluate (params x) (atX (words x)) B)
    (regular:∀ x∈W,evaluate (params x) (atX (words x)) A≠0)
    (enough:∀ x∈W,a≤(univ.filter (fun i=>(words x).eval (node i)=recv i)).card) :
    (W.card:ℚ)≤((3*r*u^2:ℕ):ℚ)*price (Fintype.card I) d a^3 := by
  classical
  let M:=bidegreeMap (Fin 2) FX r u
  let Q:=RingHom.ker M
  have prime:Q.IsPrime:=RingHom.ker_isPrime M
  have dim:(affineHilbertPolynomial Q).natDegree=3:=by
    simpa [Q,M,Nat.card_eq_fintype_card] using
      (natDegree_affineHilbertPolynomial_ker_bidegreeMap (k:=FX) (σ:=Fin 2) rp up)
  have tests:=MarkedAdaptive.supplies_tests rp dp gap tame A B ay byDeg az bz W words params recv original
    distinct degree fixed law regular enough
  have nz:1≤price (Fintype.card I) d a:=by
    rw [price,le_div_iff₀ (by exact_mod_cast dp.trans gap : (0:ℚ)<a),one_mul]
    exact_mod_cast (show a≤2*Fintype.card I*d from possible.trans
      ((Nat.le_mul_of_pos_left _ (by decide:0<2)).trans (Nat.le_mul_of_pos_right _ dp)))
  have on (x) (hx:x∈W):x∈zeroLocus FX Q:=by
    intro f hf
    rw [original x hx,aeval_monomialPoint,←bidegreeMap_eq_monomialMap r u]
    change M f=0 at hf
    rw [hf,map_zero]
  have result:=AdaptiveIncidence.prime_count W nz tests Q W (fun _ h=>h) on
  rw [dim] at result
  exact result.trans (mul_le_mul_of_nonneg_right (EmbeddingDegree.ambient rp up)
    (pow_nonneg (zero_le_one.trans nz) _))

end
end Research6969.AmbientWords
end Z6969Source0838

-- Source: Research6969.NativeAmbient
section Z6969Source0839
set_option autoImplicit true
namespace Research6969.NativeAmbient
noncomputable section
open K1 (K I p)
open K1_14 (FX L Jet Equation atX seedEmbedding)
open K1_14_3 (SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open NonlinearMarkDegrees (cap)
open NativeSurfaceCount (label label_fixed)
open MarkedAdaptive (Coordinates price)
open Finset Polynomial
open scoped Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxHeartbeats 1100000
set_option maxRecDepth 9500

private theorem total_cap {u:ℕ} {Q:Equation} (bound:∀i,(Q.coeff i).totalDegree≤u):cap (fun _=>1) u Q:=by
  intro i
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro m hm
  rw [←Finsupp.degree_eq_weight_one]
  exact (MvPolynomial.le_totalDegree hm).trans (bound i)

theorem regular {a₀ : P1.Words} {deleted : Finset I} {maxHeight agreement d U:ℕ}
    {M:P1.ModelAt maxHeight a₀ deleted} {Γ T:Finset K} (F:P1.FamilyAt agreement M Γ)
    (sub:T⊆Γ)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree) (up:0<U)
    (hU:∀ j i,((N.poly.coeff j).coeff i).totalDegree≤U)
    (physical:(131071:ℤ)+M.overhead≤d) (dp:0<d) (gap:d<agreement)
    (possible:agreement≤Fintype.card I) (tame:d<p)
    (ode:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) (den N)*atX (F.scalar z).derivative=
      evaluate (label (M.label z)) (atX (F.scalar z)) (rhs N))
    (regular:∀ z∈T,evaluate (label (M.label z)) (atX (F.scalar z)) (den N)≠0) :
    (T.card:ℚ) ≤ ((3*(G.graphDegree-1)*U^2:ℕ):ℚ)*price (Fintype.card I) d agreement^3 := by
  classical
  let r:=G.graphDegree-1
  have rp:1≤r:=by dsimp [r];omega
  have li : Function.Injective M.label := fun x y same=>sub_left_injective (b:=M.shift) same
  let encode (z:K):Coordinates r U:=MvPolynomial.monomialPoint
    (MvPolynomial.bidegreeExponents (Fin 2) r U) (OdeEmbedding.point (label (M.label z)) (atX (F.scalar z)))
  have inject : Function.Injective encode := by
    intro z y same
    have eq:=MvPolynomial.monomialPoint_injective (fun i=>MvPolynomial.single_mem_bidegreeExponents rp up i)
      (show encode z=encode y from same)
    exact li (seedEmbedding.injective (congrFun eq (some 0)))
  let W:=T.image encode
  let back:=Function.invFun encode
  have inverse (z:K):back (encode z)=z:=Function.leftInverse_invFun inject z
  have membership {x} (hx:x∈W) : back x∈T ∧ encode (back x)=x := by
    obtain ⟨z,hz,rfl⟩:=mem_image.mp hx
    rw [inverse]
    exact ⟨hz,rfl⟩
  have fam {x} (hx:x∈W):back x∈Γ:=sub ((membership hx).1)
  obtain ⟨dy,ny⟩:=NativeGraphMarks.equation_degrees N gp
  have hdeg {x} (hx:x∈W) : (F.scalar (back x)).natDegree≤d := by
    rcases (F.mark _ (fam hx)).scalar_degree with zero|bnd
    · simp [zero]
    · change ((F.scalar (back x)).natDegree:ℤ)≤131071+M.overhead at bnd
      omega
  have counted:=AmbientWords.count rp up dp gap possible tame (den N) (rhs N) dy
    (ny.trans (by dsimp [r];omega)) (total_cap (hU 1)) (total_cap (fun i=>by
      simpa [rhs,coeff_neg] using hU 0 i))
    W (fun x=>F.scalar (back x)) (fun x=>label (M.label (back x))) M.word
    (fun _ hx=>(membership hx).2.symm) (by
      intro x hx y hy eq
      have same:=F.distinct (fam hx) (fam hy) eq
      exact (membership hx).2.symm.trans ((congrArg encode same).trans (membership hy).2))
    (fun _ hx=>hdeg hx) (fun _ _=>label_fixed _)
    (fun _ hx=>ode _ ((membership hx).1)) (fun _ hx=>regular _ (membership hx).1)
    (by
      intro x hx
      let mark:=F.mark _ (fam hx)
      refine mark.bad.agreement.trans (card_le_card ?_)
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _,mark.scalar_hits i hi⟩)
  rwa [show W.card=T.card from card_image_of_injective _ inject] at counted


theorem round {t r u d:ℕ} (bound:(t:ℚ)≤((3*r*u^2:ℕ):ℚ)*price (Fintype.card I) d 179730^3) :
    t≤3*JointRouted.ordWeight d r*JointRouted.seedWeight d u^2:=by
  let R:=price (Fintype.card I) d 179730
  have z:0≤R:=by unfold R price;positivity
  have xs:R*u≤(JointRouted.seedWeight d u:ℚ):=by
    unfold JointRouted.seedWeight;push_cast
    have cp:=Nat.le_ceil (R*u);linarith
  have ys:R*r≤(JointRouted.ordWeight d r:ℚ):=by
    unfold JointRouted.ordWeight
    let extra:ℚ:=((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ)
    have en:0≤extra:=by dsimp [extra];positivity
    have cp:=Nat.le_ceil (R*r+extra)
    push_cast
    linarith
  have squared: (R*u)^2≤(JointRouted.seedWeight d u:ℚ)^2:=by
    rw [pow_two,pow_two];exact mul_le_mul xs xs (by positivity) (by positivity)
  have prod:=mul_le_mul ys squared (sq_nonneg _) (Nat.cast_nonneg _)
  have cmp:(t:ℚ)≤(3:ℚ)*JointRouted.ordWeight d r*(JointRouted.seedWeight d u:ℚ)^2:=by
    push_cast at bound
    change (t:ℚ)≤3*(r:ℚ)*u^2*R^3 at bound
    linarith only [bound,prod]
  exact_mod_cast cmp

end
end Research6969.NativeAmbient
end Z6969Source0839

-- Source: Research6969.BoxEmbedding
section Z6969Source0840
set_option autoImplicit true
namespace Research6969.BoxEmbedding
noncomputable section
open Finset MvPolynomial Module
open scoped BigOperators Pointwise
open Research6966.WordSurfaceInterpolation (rect in_rect rectangle_dimension)
variable {F σ:Type*} [Field F] [Fintype σ] [DecidableEq σ]

def exps (w:σ→ℕ) : Set (σ→₀ℕ) := {m|∀ i,m i≤w i}
instance (w:σ→ℕ) : Finite (exps w) :=
  Finite.of_injective (fun m:exps w=>fun i:σ=>(⟨m.val i,Nat.lt_succ_of_le (m.property i)⟩:Fin (w i+1)))
  (by intro a b h;apply Subtype.ext;ext i;exact congrArg Fin.val (congrFun h i))

theorem singles {w:σ→ℕ} (positive:∀ i,0<w i) (i:σ) : Finsupp.single i 1∈exps w := by
  intro j
  by_cases eq:i=j
  · subst j;simp only [Finsupp.single_eq_same];exact Nat.succ_le_of_lt (positive i)
  · simp [eq]

private theorem lift_monomial (w:σ→ℕ) (m:σ→₀ℕ) (k:ℕ) (fits:∀ i,m i≤w i*k) :
    ∃ q:MvPolynomial (exps w) F, q.totalDegree≤k ∧ monomialMap F (exps w) q=monomial m 1 := by
  classical
  induction k generalizing m with
  | zero =>
    have zero:m=0:=by ext i;simpa using fits i
    exact ⟨1,by simp,by simp [zero]⟩
  | succ k ih =>
    let first:σ→₀ℕ:=Finsupp.equivFunOnFinite.symm (fun j=>min (m j) (w j))
    have small : ∀ i,(m-first) i≤w i*k := by
      intro i
      have h:=fits i
      rw [Nat.mul_succ] at h
      change m i-min (m i) (w i)≤_
      omega
    obtain ⟨q,hq,img⟩:=ih (m-first) small
    let j:exps w:=⟨first,fun i=>min_le_right (m i) (w i)⟩
    have split : first+(m-first)=m := by
      ext i;change min (m i) (w i)+(m i-min (m i) (w i))=m i;omega
    refine ⟨MvPolynomial.X j*q,(totalDegree_mul _ _).trans ?_,?_⟩
    · rw [totalDegree_X];omega
    · rw [map_mul,img,monomialMap_X,monomial_mul_monomial,one_mul]
      exact congrArg (fun v=>monomial v (1:F)) split

theorem exists_lift (w:σ→ℕ) (k:ℕ) (f:MvPolynomial σ F)
    (bounds:∀ j,f.degreeOf j≤w j*k) :
    ∃ q:MvPolynomial (exps w) F, q.totalDegree≤k ∧ monomialMap F (exps w) q=f := by
  classical
  have get (m:f.support) := lift_monomial (F:=F) w m.val k
    (fun i=> (MvPolynomial.degreeOf_le_iff.mp (bounds i)) _ m.property)
  choose q deg im using get
  refine ⟨∑ m:f.support,C (f.coeff m.val)*q m,?_,?_⟩
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_C,zero_add];exact deg i)
  · simp only [map_sum,map_mul,monomialMap,aeval_C,algebraMap_eq] at im ⊢
    simp_rw [im,C_mul_monomial,mul_one]
    rw [Finset.sum_coe_sort f.support (fun m=>monomial m (f.coeff m))]
    exact f.support_sum_monomial_coeff

private theorem axes_nsmul (w:σ→ℕ) (k:ℕ) {m:σ→₀ℕ} (hm:m∈k • exps w) :
    ∀ j,m j≤w j*k := by
  induction k generalizing m with
  | zero =>
    have eq:m=0:=by simpa using hm
    simp [eq]
  | succ k ih =>
    rw [succ_nsmul] at hm
    obtain ⟨u,hu,v,hv,rfl⟩:=Set.mem_add.mp hm
    intro j
    rw [Finsupp.add_apply,Nat.mul_succ]
    exact Nat.add_le_add (ih hu j) (hv j)

def imageRect (J:Ideal (MvPolynomial σ F)) (w:σ→ℕ) :=
  (rect σ F w).map (Ideal.Quotient.mkₐ F J).toLinearMap

instance (J:Ideal (MvPolynomial σ F)) (w:σ→ℕ) : Module.Finite F (imageRect J w) := by
  unfold imageRect
  infer_instance

theorem hilbert_le (J:Ideal (MvPolynomial σ F)) (w:σ→ℕ) (k:ℕ) :
    affineHilbertFunction (J.comap (monomialMap F (exps w))) k ≤ finrank F (imageRect J (fun j=>w j*k)) := by
  let g:=Ideal.quotientMapₐ J (monomialMap F (exps w)) le_rfl
  let L : quotientDegreeLE (J.comap (monomialMap F (exps w))) k →ₗ[F] imageRect J (fun j=>w j*k) :=
    (g.toLinearMap.domRestrict _).codRestrict _ (fun x=>by
      obtain ⟨q,deg,eq⟩:=mem_quotientDegreeLE.mp x.property
      rw [LinearMap.domRestrict_apply,AlgHom.toLinearMap_apply,←eq]
      refine ⟨monomialMap F (exps w) q,?_,rfl⟩
      apply in_rect.mpr
      intro j
      apply degreeOf_le_iff.mpr
      intro e he
      have h:=monomialMap_mem_restrictSupport_nsmul (R:=F) (S:=exps w)
        (show 0∈exps w from fun _=>Nat.zero_le _) deg
      exact axes_nsmul w k (h he) j)
  exact LinearMap.finrank_le_finrank_of_injective (f:=L)
    (fun x y h=>Subtype.ext (Ideal.quotientMap_injective (congrArg Subtype.val h)))

theorem box_difference (H:MvPolynomial σ F) (hn:H≠0) (v cap:σ→ℕ)
    (bounds:∀ j,H.degreeOf j≤v j) (room:∀ j,v j≤cap j) :
    finrank F (imageRect (Ideal.span {H}) cap) + ∏ j,(cap j-v j+1) ≤ ∏ j,(cap j+1) := by
  let V:=rect σ F cap
  let U:=rect σ F (fun j=>cap j-v j)
  let p:V→ₗ[F](MvPolynomial σ F ⧸ Ideal.span {H}):=(Ideal.Quotient.mkₐ F _).toLinearMap.domRestrict V
  let mul:U→ₗ[F]V:=((LinearMap.mulLeft F H).domRestrict U).codRestrict V (fun x=>by
    apply in_rect.mpr
    intro j
    exact (degreeOf_mul_le j H x.val).trans ((Nat.add_le_add (bounds j)
      (in_rect.mp x.property j)).trans (by have:=room j;omega)))
  have inject:Function.Injective mul:=fun x y eq=>Subtype.ext (mul_left_cancel₀ hn (congrArg Subtype.val eq))
  have subset:mul.range≤p.ker:=by
    rintro x ⟨q,rfl⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have rank:=p.finrank_range_add_finrank_ker
  have lower:finrank F U ≤finrank F p.ker:=(LinearMap.finrank_range_of_inj inject).symm.trans_le (Submodule.finrank_mono subset)
  have equal:p.range=imageRect (Ideal.span {H}) cap:=LinearMap.range_domRestrict ..
  rw [equal] at rank
  simp only [U,V,rectangle_dimension] at lower rank
  omega

end
end Research6969.BoxEmbedding
end Z6969Source0840

-- Source: Research6969.EmbeddedCount
section Z6969Source0841
set_option autoImplicit true
namespace Research6969.EmbeddedCount
noncomputable section
open MvPolynomial Finset
open scoped BigOperators Classical
variable {F σ τ ι:Type*} [Field F] [Finite σ] [Finite τ]

/-- The dimension induction on all components of a projected hypersurface. -/
theorem hypersurface (φ:MvPolynomial σ F →ₐ[F] MvPolynomial τ F) (onto:Function.Surjective φ)
    (h:MvPolynomial τ F) (nz:h≠0) {d:ℕ} (arity:Nat.card τ=d+1)
    {D R:ℚ} (bound:affineDegree ((Ideal.span {h}).comap φ)≤D) (one:1≤R)
    (W:Finset (σ→F)) (tests:AdaptiveIncidence.Tests (ι:=ι) W R)
    (on:∀ x∈W,x∈zeroLocus F ((Ideal.span {h}).comap φ)) :
    (W.card:ℚ)≤D*R^d := by
  classical
  let J:Ideal (MvPolynomial τ F):=Ideal.span {h}
  let K:=J.comap φ
  by_cases ht:J=⊤
  · have empty:W=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hx':x∈zeroLocus F K:=on x hx
      have zero:=hx' (1:MvPolynomial σ F) (by simp [K,ht])
      simpa using zero
    rw [empty,card_empty,Nat.cast_zero]
    exact mul_nonneg ((affineDegree_nonneg _).trans bound) (pow_nonneg (zero_le_one.trans one) d)
  have dim:(affineHilbertPolynomial K).natDegree=d := by
    have t:=natDegree_affineHilbertPolynomial_comap_span_singleton_add_one_of_surjective φ onto nz ht
    change (affineHilbertPolynomial K).natDegree+1=Nat.card τ at t
    omega
  have full:=sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective φ onto h
  apply card_le_mul_pow_of_forall_mem_zeroLocus K.minimalPrimesFinset
    (fun Q hQ => (natDegree_affineHilbertPolynomial_le_of_le (Ideal.mem_minimalPrimesFinset.mp hQ).le).trans_eq dim)
    (full.trans bound) one W
  · intro x hx
    obtain ⟨Q,hQ,yes⟩:=exists_retainedMinimalPrime_of_mem_zeroLocus K 1 x (on x hx) (by simp)
    exact ⟨Q,Ideal.mem_minimalPrimesFinset.mpr (Ideal.mem_retainedMinimalPrimes.mp hQ).1,yes⟩
  · intro Q hQ
    have : Q.IsPrime:=(Ideal.mem_minimalPrimesFinset.mp hQ).isPrime
    rw [K1_11.ncard_inter_filter]
    exact AdaptiveIncidence.prime_count W one tests Q _ (filter_subset _ _) (fun _ hx=>(mem_filter.mp hx).2)

end
end Research6969.EmbeddedCount
end Z6969Source0841

-- Source: Research6969.OneSeed
section Z6969Source0842
set_option autoImplicit true
namespace Research6969.OneSeed
noncomputable section
open K1 (K I p node)
open K1_14 (FX atX)
open Research6966 Research6966.NonlinearMarkRows Research6966.NonlinearMarkDegrees
open MvPolynomial Finset
open scoped BigOperators Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000
set_option maxHeartbeats 1000000

private theorem degree_one (m:Fin 1→₀ℕ) : m.degree=m 0 := by
  change m.sum (fun _ n=>n)=m 0
  rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_one]

def widths (r u:ℕ) (v:Option (Fin 1)):=v.elim r (fun _=>u)

private theorem exponents (r u:ℕ) :
    BoxEmbedding.exps (widths r u)=bidegreeExponents (Fin 1) r u := by
  ext m
  rw [mem_bidegreeExponents,degree_one]
  constructor
  · intro h
    exact ⟨h none,h (some 0)⟩
  · rintro ⟨hy,hs⟩ i
    cases i with
    | none=>exact hy
    | some i=>fin_cases i;exact hs

private theorem lift (r u k:ℕ) (H:MvPolynomial (Option (Fin 1)) FX)
    (fits:H∈restrictBidegree (Fin 1) FX (r*k) (u*k)) :
    ∃ Q:MvPolynomial (bidegreeExponents (Fin 1) r u) FX,
    Q.totalDegree≤k ∧ monomialMap FX (bidegreeExponents (Fin 1) r u) Q=H := by
  rw [←exponents]
  apply BoxEmbedding.exists_lift
  intro i
  apply degreeOf_le_iff.mpr
  intro m hm
  have ⟨a,b⟩:=mem_restrictBidegree.mp fits m hm
  rw [degree_one] at b
  cases i with
  | none=>exact a
  | some i=>fin_cases i;exact b

abbrev Coordinates (r u:ℕ):=bidegreeExponents (Fin 1) r u→FX

theorem tests {r u d a:ℕ} (rp:0<r) (dp:0<d) (gap:d<a) (tame:d<p)
    (A B:Eqn (Fin 1) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:cap (fun _=>1) u A) (bz:cap (fun _=>1) u B)
    (W:Finset (Coordinates r u)) (words:Coordinates r u→Polynomial K)
    (params:Coordinates r u→Fin 1→FX) (received:I→K)
    (original:∀x∈W,x=monomialPoint (bidegreeExponents (Fin 1) r u) (OdeEmbedding.point (params x) (atX (words x))))
    (distinct:Set.InjOn words (W:Set _)) (degree:∀x∈W,(words x).natDegree≤d)
    (fixed:∀x∈W,∀j,Differential.deriv (params x j)=0)
    (law:∀x∈W,evaluate (params x) (atX (words x)) A * atX (words x).derivative=evaluate (params x) (atX (words x)) B)
    (regular:∀x∈W,evaluate (params x) (atX (words x)) A≠0)
    (enough:∀x∈W,a≤(univ.filter fun i=>(words x).eval (node i)=received i).card) :
    AdaptiveIncidence.Tests (ι:=I) W (MarkedAdaptive.price (Fintype.card I) d a) := by
  apply MarkedAdaptive.supplies_from_nodes dp gap W words received distinct degree enough
  intro sites t short td i
  obtain ⟨Q,ord,axes,detect⟩:=ShortenedOdeRows.exists_test sites received d t short (td.trans_lt tame) rp A B ay byDeg i
  have hy:(2*t-1)*r+1≤r*max 1 (2*t):=by
    cases t with
    | zero=>simpa using (show 1≤r by omega)
    | succ t=>
      rw [max_eq_right (by omega:1≤2*(t+1)),Nat.mul_comm r]
      calc _ ≤ (2*(t+1)-1)*r+r := by omega
           _ = _ := by rw [←Nat.succ_mul];exact congrArg (fun n=>n*r) (by omega)
  have hu:(2*t-1)*u≤u*max 1 (2*t):=
    (Nat.mul_le_mul_right _ ((Nat.sub_le ..).trans (le_max_right 1 (2*t)))).trans_eq (Nat.mul_comm ..)
  obtain ⟨cut,fee,eq⟩:=lift r u (max 1 (2*t)) (OdeEmbedding.poly Q)
    (mem_restrictBidegree_mono (OdeEmbedding.poly_bound ord (axes _ _ az bz)) hy hu)
  refine ⟨cut,fee,?_⟩
  intro x hx common
  conv_lhs => rw [original x hx,aeval_monomialPoint,eq,OdeEmbedding.evaluate_poly]
  exact detect _ _ (fixed x hx) (degree x hx) common (law x hx) (regular x hx)

theorem curve {r u g v:ℕ} (rp:0<r) (up:0<u) (H:Eqn (Fin 1) FX) (hn:H≠0)
    (hy:H.natDegree≤g) (hz:cap (fun _=>1) v H)
    (W:Finset (Coordinates r u)) (ys:Coordinates r u→FX) (seeds:Coordinates r u→Fin 1→FX)
    (original:∀x∈W,x=monomialPoint (bidegreeExponents (Fin 1) r u) (OdeEmbedding.point (seeds x) (ys x)))
    (zero:∀x∈W,evaluate (seeds x) (ys x) H=0) {R:ℚ} (one:1≤R) (cuts:AdaptiveIncidence.Tests (ι:=I) W R) :
    (W.card:ℚ)≤((g*u+r*v:ℕ):ℚ)*R := by
  let h:=OdeEmbedding.poly H
  have nz:h≠0:=fun eq=>hn ((optionEquivLeft FX (Fin 1)).symm.injective (by simpa [h,OdeEmbedding.poly] using eq))
  have fee:=affineDegree_comap_bidegreeMap_span_singleton_le rp up nz (OdeEmbedding.poly_bound hy hz)
  have total:=EmbeddedCount.hypersurface (bidegreeMap (Fin 1) FX r u) (bidegreeMap_surjective rp up) h nz
    (by simp [Nat.card_eq_fintype_card]:Nat.card (Option (Fin 1))=1+1) fee one W cuts (by
      intro x hx f hf
      rw [original x hx,aeval_monomialPoint,←bidegreeMap_eq_monomialMap r u]
      have owned : Ideal.span {h}≤RingHom.ker (aeval (R:=FX) (OdeEmbedding.point (seeds x) (ys x))) :=
        (Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr ((OdeEmbedding.evaluate_poly H ..).trans (zero x hx)))
      exact RingHom.mem_ker.mp (owned hf))
  simpa [Nat.card_eq_fintype_card,Nat.mul_comm v r] using total


/-- The complete one-seed plane pays two incidences per unit of the two
Taylor degrees. This also covers a surface depending on the discarded seed. -/
theorem ambient_degree {r u:ℕ} (rp:0<r) (up:0<u) :
    affineDegree (RingHom.ker (bidegreeMap (Fin 1) FX r u))≤((2*r*u:ℕ):ℚ) := by
  let J:=RingHom.ker (bidegreeMap (Fin 1) FX r u)
  have dim:(affineHilbertPolynomial J).natDegree=2:=by
    simpa [J,Nat.card_eq_fintype_card] using (natDegree_affineHilbertPolynomial_ker_bidegreeMap (σ:=Fin 1) (k:=FX) rp up)
  let c:ℚ:=(r:ℚ)*u
  let P:Polynomial ℚ:=Polynomial.monomial 2 c+Polynomial.monomial 1 ((r:ℚ)+u)+1
  have pd:P.natDegree≤2:=by dsimp [P];compute_degree
  have pc:P.coeff 2=c:=by simp [P,Polynomial.coeff_one]
  have size (N:ℕ):affineHilbertFunction J N≤(r*N+1)*(u*N+1):=by
    rw [show J=(⊥:Ideal (MvPolynomial (Option (Fin 1)) FX)).comap (bidegreeMap (Fin 1) FX r u) from rfl]
    apply (affineHilbertFunction_comap_bidegreeMap_le _ _ _ _).trans
    apply (Submodule.finrank_map_le _ _).trans
    simp [finrank_restrictBidegree,Nat.card_eq_fintype_card]
  have evaluated (N:ℕ):P.eval (N:ℚ)=(((r*N+1)*(u*N+1):ℕ):ℚ):=by
    simp only [P,Polynomial.eval_add,Polynomial.eval_monomial,Polynomial.eval_one]
    dsimp [c]
    push_cast
    ring
  have bound:=affineDegree_le_of_eventually_affineHilbertFunction_le dim pd
    (Filter.Eventually.of_forall (fun N=>by rw [evaluated];exact_mod_cast size N))
  rw [pc] at bound
  simpa [c,Nat.factorial,mul_assoc] using bound

theorem plane {r u:ℕ} (rp:0<r) (up:0<u) (W:Finset (Coordinates r u))
    (ys:Coordinates r u→FX) (seeds:Coordinates r u→Fin 1→FX)
    (original:∀x∈W,x=monomialPoint (bidegreeExponents (Fin 1) r u) (OdeEmbedding.point (seeds x) (ys x)))
    {R:ℚ} (one:1≤R) (cuts:AdaptiveIncidence.Tests (ι:=I) W R) :
    (W.card:ℚ)≤((2*r*u:ℕ):ℚ)*R^2 := by
  let J:=RingHom.ker (bidegreeMap (Fin 1) FX r u)
  have on (x) (hx:x∈W):x∈zeroLocus FX J:=by
    intro f hf
    rw [original x hx,aeval_monomialPoint,←bidegreeMap_eq_monomialMap r u,RingHom.mem_ker.mp hf,map_zero]
  have dim:(affineHilbertPolynomial J).natDegree=2:=by
    simpa [J,Nat.card_eq_fintype_card] using (natDegree_affineHilbertPolynomial_ker_bidegreeMap (σ:=Fin 1) (k:=FX) rp up)
  have : J.IsPrime:=RingHom.ker_isPrime _
  have total:=AdaptiveIncidence.prime_count W one cuts J W (fun _ x=>x) on
  rw [dim] at total
  exact total.trans (mul_le_mul_of_nonneg_right (ambient_degree rp up) (sq_nonneg _))

end
end Research6969.OneSeed
end Z6969Source0842

-- Source: Research6969.OneSeedSpecialization
section Z6969Source0843
set_option autoImplicit true
namespace Research6969.OneSeed
noncomputable section
open K1 (K I p)
open K1_14 (FX atX)
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open MvPolynomial Finset
open scoped Differential
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds

def fold (P:Eqn (Fin 2) FX):Eqn (Fin 1) FX :=
  P.map (MvPolynomial.rename (fun _:Fin 2=>(0:Fin 1))).toRingHom

def supportedOn (j:Fin 2) (P:Eqn (Fin 2) FX):Prop :=
  ∀ n k, k≠j → (P.coeff n).degreeOf k=0

theorem restored (j:Fin 2) (P:Eqn (Fin 2) FX) (support:supportedOn j P) :
    (fold P).map (MvPolynomial.rename (fun _:Fin 1=>j)).toRingHom=P := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map,fold,Polynomial.coeff_map]
  let f: MvPolynomial (Fin 2) FX →+* MvPolynomial (Fin 2) FX :=
    (MvPolynomial.rename (fun _:Fin 1=>j)).toRingHom.comp (MvPolynomial.rename (fun _:Fin 2=>(0:Fin 1))).toRingHom
  change f (P.coeff n)=(RingHom.id _) (P.coeff n)
  apply MvPolynomial.hom_congr_vars (p₁:=P.coeff n) (p₂:=P.coeff n) (by ext c;simp [f]) _ rfl
  intro k hk _
  have same:k=j:=by
    by_contra ne
    exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hk) (support n k ne)
  subst k
  simp [f]

theorem eval_fold (j:Fin 2) (P:Eqn (Fin 2) FX) (support:supportedOn j P) (z:Fin 2→FX) (y:FX) :
    evaluate (fun _:Fin 1=>z j) y (fold P)=evaluate z y P := by
  conv_rhs=>rw [←restored j P support]
  change _=Polynomial.eval₂ _ y (Polynomial.map _ _)
  rw [Polynomial.eval₂_map]
  have maps:(MvPolynomial.eval z).comp (MvPolynomial.rename (fun _:Fin 1=>j)).toRingHom =
      MvPolynomial.eval (fun _:Fin 1=>z j):=by ext <;>simp
  rw [maps]
  rfl

theorem fold_cap {j:Fin 2} {P:Eqn (Fin 2) FX} {u:ℕ} (support:supportedOn j P)
    (active:∀n,(P.coeff n).degreeOf j≤u) : cap (fun _=>1) u (fold P) := by
  intro n
  apply MvPolynomial.mem_restrictWeightAtMost.mpr
  intro m hm
  have bd:(P.coeff n).totalDegree≤u:=by
    apply Finset.sup_le
    intro v hv
    have other (k:Fin 2) (ne:k≠j) : v k=0:=
      Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_le_iff.mp (le_of_eq (support n k ne))) _ hv)
    have one: v.degree=v j:=by
      change v.sum (fun _ n=>n)=v j
      rw [Finsupp.sum_fintype _ _ (fun _=>rfl),Fin.sum_univ_two]
      fin_cases j
      · simp [other 1 (by decide)]
      · simp [other 0 (by decide)]
    change v.degree≤u
    rw [one]
    exact MvPolynomial.degreeOf_le_iff.mp (active n) _ hv
  have all:((fold P).coeff n).totalDegree≤u:=by
    rw [fold,Polynomial.coeff_map]
    exact (MvPolynomial.totalDegree_rename_le _ _).trans bd
  have v:= (MvPolynomial.le_totalDegree hm).trans all
  simpa [Finsupp.weight_apply,Finsupp.degree_apply,Finsupp.sum] using v

theorem fold_ne {j:Fin 2} {P:Eqn (Fin 2) FX} (support:supportedOn j P) (hn:P≠0) : fold P≠0 := by
  intro eq
  exact hn ((restored j P support).symm.trans (by rw [eq,Polynomial.map_zero]))

end
end Research6969.OneSeed
end Z6969Source0843

-- Source: Research6969.OneSeedNative
section Z6969Source0844
set_option autoImplicit true
namespace Research6969.OneSeed
noncomputable section
open K1 (K I p)
open K1_14 (FX atX)
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open MvPolynomial Finset
open scoped Differential Classical BigOperators
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds
set_option maxHeartbeats 1200000

/-- A genuine marked word is encoded using only its ordinate and the
single seed coordinate present in its differential equation. -/
theorem native_at {u₀:P1.Words} {del:Finset I} {height a d r U g v:ℕ}
    {M:P1.ModelAt height u₀ del} {Γ T:Finset K} (F:P1.FamilyAt a M Γ) (subset:T⊆Γ)
    (param:K→Fin 2→FX) (fixed:∀ z i,Differential.deriv (param z i)=0)
    (j:Fin 2) (rp:0<r) (up:0<U) (dp:0<d) (gap:d<a) (possible:a≤Fintype.card I) (tame:d<p)
    (A B H:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (sa:supportedOn j A) (sb:supportedOn j B)
    (az:∀i,(A.coeff i).degreeOf j≤U) (bz:∀i,(B.coeff i).degreeOf j≤U)
    (hn:H≠0) (hy:H.natDegree≤g) (hz:∀i,(H.coeff i).degreeOf j≤v)
    (degree:∀ z∈T,(F.scalar z).natDegree≤d)
    (law:∀ z∈T,evaluate (param z) (atX (F.scalar z)) A * atX (F.scalar z).derivative=
      evaluate (param z) (atX (F.scalar z)) B)
    (regular:∀ z∈T,evaluate (param z) (atX (F.scalar z)) A≠0)
    (surface:∀ z∈T,evaluate (param z) (atX (F.scalar z)) H=0) :
    let R:=MarkedAdaptive.price (Fintype.card I) d a
    (T.card:ℚ) ≤ if supportedOn j H then ((g*U+r*v:ℕ):ℚ)*R else ((2*r*U:ℕ):ℚ)*R^2 := by
  classical
  let val (z:K):Fin 1→FX:=fun _=>param z j
  let encode (z:K):Coordinates r U:=monomialPoint (bidegreeExponents (Fin 1) r U) (OdeEmbedding.point (val z) (atX (F.scalar z)))
  have inj:Set.InjOn encode (T:Set K):=by
    intro x hx y hy eq
    have h:=monomialPoint_injective (fun i=>single_mem_bidegreeExponents rp up i) (show encode x=encode y from eq)
    exact F.distinct (subset hx) (subset hy) (K1_14_3.scalar_atX_injective (congrFun h none))
  let W:=T.image encode
  let back (x:Coordinates r U):K:=if h:x∈W then Classical.choose (mem_image.mp h) else 0
  have recover (x) (hx:x∈W):back x∈T ∧ encode (back x)=x:=by
    dsimp [back]
    rw [dif_pos hx]
    exact Classical.choose_spec (mem_image.mp hx)
  let words (x:Coordinates r U) := F.scalar (back x)
  let params (x:Coordinates r U):=val (back x)
  have original x (hx:x∈W):
      x=monomialPoint (bidegreeExponents (Fin 1) r U) (OdeEmbedding.point (params x) (atX (words x))) :=
    (recover x hx).2.symm
  have cuts:=tests rp dp gap tame (fold A) (fold B) (Polynomial.natDegree_map_le.trans ay)
    (Polynomial.natDegree_map_le.trans byDeg) (fold_cap sa az) (fold_cap sb bz) W words params M.word original
    (by intro x hx y hy eq
        have eq':back x=back y:=F.distinct (subset (recover x hx).1) (subset (recover y hy).1) eq
        exact (recover x hx).2.symm.trans ((congrArg encode eq').trans (recover y hy).2))
    (fun x hx=>degree _ (recover x hx).1)
    (fun _ _ _=>fixed _ _) (by
      intro x hx
      have e:=law _ (recover x hx).1
      rw [←eval_fold j A sa,←eval_fold j B sb] at e
      exact e) (by
      intro x hx
      have e:=regular _ (recover x hx).1
      rw [←eval_fold j A sa] at e
      exact e) (by
      intro x hx
      let mark:=F.mark _ (subset (recover x hx).1)
      refine mark.bad.agreement.trans (card_le_card ?_)
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _,mark.scalar_hits i hi⟩)
  have one:1≤MarkedAdaptive.price (Fintype.card I) d a:=by
    rw [MarkedAdaptive.price,le_div_iff₀ (by exact_mod_cast dp.trans gap : (0:ℚ)<a),one_mul]
    exact_mod_cast (show a≤2*Fintype.card I*d from possible.trans
      ((Nat.le_mul_of_pos_left _ (by decide:0<2)).trans (Nat.le_mul_of_pos_right _ dp)))
  rw [←show W.card=T.card from card_image_of_injOn inj]
  split_ifs with sh
  · apply curve rp up (fold H) (fold_ne sh hn) (Polynomial.natDegree_map_le.trans hy) (fold_cap sh hz)
      W (fun x=>atX (words x)) params original _ one cuts
    intro x hx
    have e:=surface _ (recover x hx).1
    rw [←eval_fold j H sh] at e
    exact e
  · exact plane rp up W (fun x=>atX (words x)) params original one cuts

theorem native {u₀:P1.Words} {del:Finset I} {height a d r U g v:ℕ}
    {M:P1.ModelAt height u₀ del} {Γ T:Finset K} (F:P1.FamilyAt a M Γ) (subset:T⊆Γ)
    (j:Fin 2) (rp:0<r) (up:0<U) (dp:0<d) (gap:d<a) (possible:a≤Fintype.card I) (tame:d<p)
    (A B H:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (sa:supportedOn j A) (sb:supportedOn j B)
    (az:∀i,(A.coeff i).degreeOf j≤U) (bz:∀i,(B.coeff i).degreeOf j≤U)
    (hn:H≠0) (hy:H.natDegree≤g) (hz:∀i,(H.coeff i).degreeOf j≤v)
    (degree:∀ z∈T,(F.scalar z).natDegree≤d)
    (law:∀ z∈T,evaluate (NativeSurfaceCount.label (M.label z)) (atX (F.scalar z)) A * atX (F.scalar z).derivative=
      evaluate (NativeSurfaceCount.label (M.label z)) (atX (F.scalar z)) B)
    (regular:∀ z∈T,evaluate (NativeSurfaceCount.label (M.label z)) (atX (F.scalar z)) A≠0)
    (surface:∀ z∈T,evaluate (NativeSurfaceCount.label (M.label z)) (atX (F.scalar z)) H=0) :
    let R:=MarkedAdaptive.price (Fintype.card I) d a
    (T.card:ℚ) ≤ if supportedOn j H then ((g*U+r*v:ℕ):ℚ)*R else ((2*r*U:ℕ):ℚ)*R^2 :=
  native_at F subset (fun z=>NativeSurfaceCount.label (M.label z)) (fun z=>NativeSurfaceCount.label_fixed _) j
    rp up dp gap possible tame A B H ay byDeg sa sb az bz hn hy hz degree law regular surface

end
end Research6969.OneSeed
end Z6969Source0844
