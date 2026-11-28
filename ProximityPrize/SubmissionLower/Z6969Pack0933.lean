import ProximityPrize.SubmissionLower.Z6969Pack0635
import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertBidegree
import ProximityPrize.SubmissionLower.Z6969Pack0528
import ProximityPrize.SubmissionLower.R6966ProofOdeSurfaceBridge
import ProximityPrize.SubmissionLower.Z6969Pack0534
import ProximityPrize.SubmissionLower.Z6969Pack0636
import ProximityPrize.SubmissionLower.Z6969Pack0666
import ProximityPrize.SubmissionLower.Z6969Pack0640
import ProximityPrize.SubmissionLower.Z6969Pack0641

set_option Elab.async false

-- merged module Z6969Pack0932
section Merged_Z6969Pack0932

-- Source: Research6969.RectangularDegree
section Z6969Source2543
set_option autoImplicit true
namespace Research6969.RectangularDegree
noncomputable section
open MvPolynomial Finset Filter Module Research6969.BoxEmbedding
open scoped BigOperators Classical

def mixed (v w:Fin 3→ℕ) := v 0*w 1*w 2+v 1*w 0*w 2+v 2*w 0*w 1

private theorem loss (x y z a b c:ℕ) (ha:a≤x) (hb:b≤y) (hc:c≤z) :
    x*y*z ≤ (x-a)*(y-b)*(z-c) + (a*y*z+b*x*z+c*x*y) := by
  obtain ⟨x,rfl⟩:=Nat.exists_eq_add_of_le ha
  obtain ⟨y,rfl⟩:=Nat.exists_eq_add_of_le hb
  obtain ⟨z,rfl⟩:=Nat.exists_eq_add_of_le hc
  simp only [Nat.add_sub_cancel_left]
  nlinarith only [Nat.zero_le (a*b*c),Nat.zero_le (a*b*z),Nat.zero_le (a*c*y),Nat.zero_le (b*c*x)]

/-- The exact three-axis leading coefficient, also for a reducible
hypersurface and in positive characteristic. -/
theorem hypersurface {F:Type*} [Field F] (H:MvPolynomial (Fin 3) F) (hn:H≠0)
    (v w:Fin 3→ℕ) (hw:∀ i,0<w i) (hv:∀ i,H.degreeOf i≤v i) :
    affineDegree ((Ideal.span {H}).comap (monomialMap F (exps w))) ≤ ((2*mixed v w:ℕ):ℚ) := by
  let J:Ideal (MvPolynomial (Fin 3) F):=Ideal.span {H}
  let K:=J.comap (monomialMap F (exps w))
  by_cases ht:J=⊤
  · change affineDegree (J.comap _)≤_
    rw [ht,Ideal.comap_top,affineDegree_top]
    positivity
  have dims : (affineHilbertPolynomial K).natDegree=2 := by
    have hbase:=natDegree_affineHilbertPolynomial_span_singleton_add_one hn ht
    have dim:=natDegree_affineHilbertPolynomial_comap_of_surjective
      (monomialMap F (exps w)) (monomialMap_surjective (R:=F) (singles hw)) J
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hbase
    exact dim.trans (by change _=2;change (affineHilbertPolynomial J).natDegree+1=3 at hbase;omega)
  let c₁:ℕ:=v 0*(w 1+w 2)+v 1*(w 0+w 2)+v 2*(w 0+w 1)
  let c₀:ℕ:=v 0+v 1+v 2
  let P:Polynomial ℚ:=Polynomial.monomial 2 (mixed v w:ℚ)+Polynomial.monomial 1 (c₁:ℚ)+Polynomial.C (c₀:ℚ)
  have pd:P.natDegree≤2:=by dsimp [P];compute_degree
  have coeff:P.coeff 2=(mixed v w:ℕ):=by simp [P]
  have result:=affineDegree_le_of_eventually_affineHilbertFunction_le dims pd (R:=P) (by
    filter_upwards [eventually_ge_atTop (v 0+v 1+v 2)] with N hN
    let cap:=fun j=>w j*N
    have room (j):v j≤cap j:=by
      apply le_trans _ (Nat.le_mul_of_pos_left N (hw j))
      fin_cases j <;> dsimp <;> omega
    have ranked:=hilbert_le J w N
    have diff:=box_difference H hn v cap hv room
    have budget:=loss (cap 0+1) (cap 1+1) (cap 2+1) (v 0) (v 1) (v 2)
      ((room 0).trans (Nat.le_succ _)) ((room 1).trans (Nat.le_succ _)) ((room 2).trans (Nat.le_succ _))
    have reset (i):cap i+1-v i=cap i-v i+1 := by have:=room i;omega
    simp only [Fin.prod_univ_three] at diff
    simp only [reset] at budget
    change affineHilbertFunction K N≤_ at ranked
    change finrank F (imageRect J cap)+_≤_ at diff
    have size:affineHilbertFunction K N≤
        v 0*(cap 1+1)*(cap 2+1)+v 1*(cap 0+1)*(cap 2+1)+v 2*(cap 0+1)*(cap 1+1) := by
      change _≤finrank F (imageRect J cap) at ranked
      omega
    apply (show (affineHilbertFunction K N:ℚ)≤
      ((v 0*(cap 1+1)*(cap 2+1)+v 1*(cap 0+1)*(cap 2+1)+v 2*(cap 0+1)*(cap 1+1):ℕ):ℚ)
      from Nat.cast_le.mpr size).trans_eq
    simp only [P,Polynomial.eval_add,Polynomial.eval_monomial,Polynomial.eval_C]
    dsimp [cap,c₁,c₀,mixed]
    push_cast <;> ring)
  rw [coeff] at result
  simpa [Nat.factorial] using result

end
end Research6969.RectangularDegree
end Z6969Source2543

-- Source: Research6969.RectangularRows
section Z6969Source2544
set_option autoImplicit true
namespace Research6969.RectangularRows
noncomputable section
open K1 (K I p node)
open K1_14 (FX atX)
open Research6966
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open MvPolynomial Finset
open scoped Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000

def sides (r:ℕ) (u:Fin 2→ℕ) : Fin 3→ℕ:=Fin.cons (α:=fun _:Fin 3=>ℕ) r u
def point (z:Fin 2→FX) (y:FX) : Fin 3→FX:=Fin.cons (α:=fun _:Fin 3=>FX) y z

theorem exists_cut (sites:Finset I) (recv:I→K) (d t:ℕ) (short:d≤sites.card+t)
    (tame:t<p) {r:ℕ} (rp:1≤r) (u:Fin 2→ℕ) (A B:Eqn (Fin 2) FX)
    (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:∀ j,cap (Pi.single j 1) (u j) A) (bz:∀ j,cap (Pi.single j 1) (u j) B) (i:I) :
    ∃ cut:MvPolynomial (BoxEmbedding.exps (sides r u)) FX, cut.totalDegree≤max 1 (2*t) ∧
      ∀ (z:Fin 2→FX) (S:Polynomial K), (∀ j,Differential.deriv (z j)=0) → S.natDegree≤d →
        (∀ k∈sites,S.eval (node k)=recv k) →
        evaluate z (atX S) A * atX S.derivative = evaluate z (atX S) B →
        evaluate z (atX S) A ≠ 0 →
        (aeval (monomialPoint (BoxEmbedding.exps (sides r u)) (point z (atX S))) cut=0 ↔
          S.eval (node i)=recv i) := by
  obtain ⟨Q,degree,axes,detect⟩:=ShortenedOdeRows.exists_test sites recv d t short tame rp A B ay byDeg i
  have sizes:=OdeSurfaceBridge.degrees Q ((2*t-1)*r+1) (fun j=>(2*t-1)*u j) degree
    (fun j=>axes _ _ (az j) (bz j))
  have bounds (k:Fin 3) : (OdeSurfaceBridge.coordinates Q).degreeOf k≤sides r u k*max 1 (2*t) := by
    apply (sizes k).trans
    refine Fin.cases ?_ (fun j=>?_) k
    · change (2*t-1)*r+1≤r*max 1 (2*t)
      cases t with
      | zero=>simpa using rp
      | succ n=>
        rw [max_eq_right (by omega:1≤2*(n+1)),Nat.mul_comm r]
        calc _ ≤ (2*(n+1)-1)*r+r := by omega
          _ = (2*(n+1))*r := by
            rw [←Nat.succ_mul]
            exact congrArg (fun k=>k*r) (by omega)
    · change (2*t-1)*u j≤u j*max 1 (2*t)
      exact (Nat.mul_le_mul_right _ ((Nat.sub_le ..).trans (le_max_right 1 (2*t)))).trans_eq (Nat.mul_comm ..)
  obtain ⟨cut,bound,eq⟩:=BoxEmbedding.exists_lift (sides r u) (max 1 (2*t)) (OdeSurfaceBridge.coordinates Q) bounds
  refine ⟨cut,bound,?_⟩
  intro z S fixed deg common law regular
  rw [aeval_monomialPoint,eq]
  change MvPolynomial.eval (point z (atX S)) (OdeSurfaceBridge.coordinates Q)=0 ↔ _
  rw [show MvPolynomial.eval (point z (atX S)) (OdeSurfaceBridge.coordinates Q)=evaluate z (atX S) Q
    from OdeSurfaceBridge.read Q z (atX S)]
  exact detect z S fixed deg common law regular

end
end Research6969.RectangularRows
end Z6969Source2544

-- Source: Research6969.RectangularSurface
section Z6969Source2545
set_option autoImplicit true
namespace Research6969.RectangularSurface
noncomputable section
open K1 (K I p node)
open K1_14 (FX atX)
open Research6966
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Research6966.NonlinearMarkDegrees (cap)
open Research6969.MarkedAdaptive (price)
open Research6969.RectangularRows (sides point)
open MvPolynomial Finset
open scoped BigOperators Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 6000
set_option maxHeartbeats 900000

abbrev Coord (r:ℕ) (u:Fin 2→ℕ):=BoxEmbedding.exps (sides r u)→FX

/-- Nonlinear marks with a different Taylor degree cap on each seed axis. -/
theorem count {r d agreement g:ℕ} (u v:Fin 2→ℕ) (rp:1≤r) (up:∀ i,0<u i)
    (dp:0<d) (gap:d<agreement) (possible:agreement≤Fintype.card I) (tame:d<p)
    (A B H:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:∀ j,cap (Pi.single j 1) (u j) A) (bz:∀ j,cap (Pi.single j 1) (u j) B)
    (hn:H≠0) (hy:H.natDegree≤g) (hz:∀ j,cap (Pi.single j 1) (v j) H)
    (W:Finset (Coord r u)) (words:Coord r u→Polynomial K)
    (params:Coord r u→Fin 2→FX) (received:I→K)
    (original:∀ x∈W,x=monomialPoint (BoxEmbedding.exps (sides r u))
      (point (params x) (atX (words x))))
    (distinct:Set.InjOn words (W:Set _)) (degree:∀ x∈W,(words x).natDegree≤d)
    (fixed:∀ x∈W,∀ j,Differential.deriv (params x j)=0)
    (law:∀ x∈W,evaluate (params x) (atX (words x)) A * atX (words x).derivative =
      evaluate (params x) (atX (words x)) B)
    (regular:∀ x∈W,evaluate (params x) (atX (words x)) A≠0)
    (surface:∀ x∈W,evaluate (params x) (atX (words x)) H=0)
    (enough:∀ x∈W,agreement≤(univ.filter (fun i=> (words x).eval (node i)=received i)).card) :
    (W.card:ℚ)≤((2*RectangularDegree.mixed (sides g v) (sides r u):ℕ):ℚ)*
      price (Fintype.card I) d agreement^2 := by
  classical
  let w:=sides r u
  have hp:∀ j,0<w j:=Fin.cases rp up
  let topo:=monomialMap FX (BoxEmbedding.exps w)
  let h:=OdeSurfaceBridge.coordinates H
  have hbound:=OdeSurfaceBridge.degrees H g v hy hz
  have nz:h≠0:=(map_ne_zero_iff _ (MvPolynomial.finSuccEquiv FX 2).symm.injective).mpr hn
  have tests:AdaptiveIncidence.Tests (ι:=I) W (price (Fintype.card I) d agreement) := by
    apply MarkedAdaptive.supplies_from_nodes dp gap W words received distinct degree enough
    intro sites t short td i
    obtain ⟨cut,bound,detect⟩:=RectangularRows.exists_cut sites received d t short (td.trans_lt tame)
      rp u A B ay byDeg az bz i
    refine ⟨cut,bound,?_⟩
    intro x hx common
    have eq:=detect (params x) (words x) (fixed x hx) (degree x hx) common (law x hx) (regular x hx)
    rwa [←original x hx] at eq
  have one:1≤price (Fintype.card I) d agreement:=by
    rw [price,le_div_iff₀ (by exact_mod_cast dp.trans gap : (0:ℚ)<agreement),one_mul]
    exact_mod_cast (show agreement≤2*Fintype.card I*d from
      possible.trans ((Nat.le_mul_of_pos_left _ (by decide:0<2)).trans (Nat.le_mul_of_pos_right _ dp)))
  apply EmbeddedCount.hypersurface topo (monomialMap_surjective (BoxEmbedding.singles hp)) h nz
    (by simp : Nat.card (Fin 3)=2+1) (RectangularDegree.hypersurface h nz _ w hp hbound) one W tests
  intro x hx f hf
  rw [original x hx,aeval_monomialPoint]
  have hzero:MvPolynomial.aeval (point (params x) (atX (words x))) h=0:=
    (OdeSurfaceBridge.read H ..).trans (surface x hx)
  have ideal:(Ideal.span {h})≤RingHom.ker (MvPolynomial.aeval (point (params x) (atX (words x)))) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (RingHom.mem_ker.mpr hzero)
  exact RingHom.mem_ker.mp (ideal hf)

end
end Research6969.RectangularSurface
end Z6969Source2545

-- Source: Research6969.RectNative
section Z6969Source2546
set_option autoImplicit true
namespace Research6969.RectNative
noncomputable section
open K1 (I K p)
open K1_14 (FX atX)
open Research6966
open NonlinearMarkRows (evaluate Eqn)
open NonlinearMarkDegrees (cap)
open NativeSurfaceCount (label)
open RectangularRows (sides point)
open MvPolynomial Finset
open scoped Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 7000
set_option maxHeartbeats 1100000

/-- Regular marked words counted with separate positive bounds on the
two seed coordinates, for an arbitrary genuine retained equation. -/
theorem regular {u₀ del} {M:P1.ModelAt 33755 u₀ del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ) (sub:T⊆Γ)
    {r g d:ℕ} (U V:Fin 2→ℕ) (rp:0<r) (up:∀i,0<U i) (dp:0<d) (gap:d<179730) (tame:d<p)
    (A B H:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:∀j i,(A.coeff i).degreeOf j≤U j) (bz:∀j i,(B.coeff i).degreeOf j≤U j)
    (hn:H≠0) (hy:H.natDegree≤g) (hz:∀j i,(H.coeff i).degreeOf j≤V j)
    (degree:∀z∈T,(F.scalar z).natDegree≤d)
    (laws:∀z∈T,let ev:=evaluate (label (M.label z)) (atX (F.scalar z))
      (ev A*atX (F.scalar z).derivative=ev B) ∧ ev A≠0 ∧ ev H=0) :
    (T.card:ℚ)≤((2*RectangularDegree.mixed (sides g V) (sides r U):ℕ):ℚ)*
      MarkedAdaptive.price (Fintype.card I) d 179730^2 := by
  classical
  let encode (z:K):RectangularSurface.Coord r U:=monomialPoint (BoxEmbedding.exps (sides r U))
    (point (label (M.label z)) (atX (F.scalar z)))
  have positive (j):0<sides r U j:=Fin.cases rp up j
  have inj:Set.InjOn encode (T:Set K):=by
    intro x hx y hy same
    have eq:=monomialPoint_injective (BoxEmbedding.singles positive) (show encode x=encode y from same)
    exact F.distinct (sub hx) (sub hy) (K1_14_3.scalar_atX_injective (congrFun eq 0))
  let S:=T.image encode
  let back (x:RectangularSurface.Coord r U):K:=if h:x∈S then Classical.choose (mem_image.mp h) else 0
  have belongs (x) (hx:x∈S):back x∈T ∧ encode (back x)=x:=by
    dsimp [back];rw [dite_eq_left hx];exact Classical.choose_spec (mem_image.mp hx)
  have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
  have count:=RectangularSurface.count U V rp up dp gap fit tame A B H ay byDeg
    (fun j=>(OdeSurfaceBridge.axis_cap ..).mpr (az j)) (fun j=>(OdeSurfaceBridge.axis_cap ..).mpr (bz j))
    hn hy (fun j=>(OdeSurfaceBridge.axis_cap ..).mpr (hz j)) S (fun x=>F.scalar (back x))
    (fun x=>label (M.label (back x))) M.word (fun _ hx=>(belongs _ hx).2.symm) (by
      intro x hx y hy eq
      have same:=F.distinct (sub (belongs _ hx).1) (sub (belongs _ hy).1) eq
      exact (belongs _ hx).2.symm.trans ((congrArg encode same).trans (belongs _ hy).2))
    (fun _ hx=>degree _ (belongs _ hx).1) (fun _ _=>NativeSurfaceCount.label_fixed _)
    (fun _ hx=>(laws _ (belongs _ hx).1).1) (fun _ hx=>(laws _ (belongs _ hx).1).2.1)
    (fun _ hx=>(laws _ (belongs _ hx).1).2.2) (by
      intro x hx
      let m:=F.mark _ (sub (belongs x hx).1)
      refine m.bad.agreement.trans (card_le_card ?_)
      intro i hi
      exact mem_filter.mpr ⟨mem_univ _,m.scalar_hits i hi⟩)
  rwa [show S.card=T.card from card_image_of_injOn inj] at count

/-- Comparison with the integer ledger when the second Taylor seed is
absent. A genuine dependence of the retained equation on that seed pays
the entire plane charge with its positive degree in the missing axis. -/
theorem one_axis_price {t r u g v x y:ℕ} {R:ℚ} (zero:Prop) [Decidable zero] (nn:0≤R)
    (count:(t:ℚ) ≤ (if zero then ((g*u+r*v:ℕ):ℚ)*R else ((2*r*u:ℕ):ℚ)*R^2))
    (absent:¬zero→0<x) (bPrice yPrice:ℕ) (bs:R*u≤(bPrice:ℚ)) (ys:R*r≤(yPrice:ℚ)) (pad:0<y) :
    t≤2*g*bPrice*y+2*yPrice*(v*y+x*bPrice) := by
  have fromQ (h:(t:ℚ)≤((2*g*bPrice*y+2*yPrice*(v*y+x*bPrice):ℕ):ℚ)) :
      t≤2*g*bPrice*y+2*yPrice*(v*y+x*bPrice):=by exact_mod_cast h
  apply fromQ
  push_cast
  by_cases yes:zero
  · rw [ite_eq_left yes] at count
    have gb:=mul_le_mul_of_nonneg_left bs (Nat.cast_nonneg g: (0:ℚ)≤g)
    have vr:=mul_le_mul_of_nonneg_left ys (Nat.cast_nonneg v: (0:ℚ)≤v)
    have gn:g*bPrice≤2*g*bPrice*y:=by
      have b:g*bPrice≤(g*bPrice)*2:=Nat.le_mul_of_pos_right _ (by decide)
      calc _≤(g*bPrice)*2:=b
           _≤((g*bPrice)*2)*y:=Nat.le_mul_of_pos_right _ pad
           _=_:=by ring
    have vn:v*yPrice≤2*yPrice*(v*y+x*bPrice):=by
      have h:v≤v*y+x*bPrice := (Nat.le_mul_of_pos_right _ pad).trans (Nat.le_add_right ..)
      calc _=yPrice*v:=Nat.mul_comm ..
           _≤yPrice*(v*y+x*bPrice):=Nat.mul_le_mul_left _ h
           _≤2*yPrice*(v*y+x*bPrice):=Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide))
    have gnq:(g:ℚ)*bPrice≤2*g*bPrice*y:=by exact_mod_cast gn
    have vnq:(v:ℚ)*yPrice≤2*yPrice*(v*y+x*bPrice):=by exact_mod_cast vn
    push_cast at count
    linarith only [count,gb,vr,gnq,vnq]
  · rw [ite_eq_right yes] at count
    have prod:=mul_le_mul bs ys (mul_nonneg nn (Nat.cast_nonneg _)) (Nat.cast_nonneg bPrice)
    have q:2*yPrice*bPrice≤2*yPrice*(v*y+x*bPrice):=Nat.mul_le_mul_left _ ((Nat.le_mul_of_pos_left _ (absent yes)).trans (Nat.le_add_left ..))
    have qq:(2:ℚ)*yPrice*bPrice≤2*yPrice*(v*y+x*bPrice):=by exact_mod_cast q
    push_cast at count
    nlinarith only [count,prod,qq,show (0:ℚ)≤2*g*bPrice*y by positivity]

end
end Research6969.RectNative
end Z6969Source2546

-- Source: Research6969.RectWordPrice
section Z6969Source2547
set_option autoImplicit true
namespace Research6969.RectWordPrice
noncomputable section
open K1 (K I p)
open K1_14 (Equation FX atX)
open K1_14_3 (SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open NonlinearMarkRows (evaluate)
open JointRouted (seedWeight ordWeight)
open Finset Polynomial
open scoped Classical Differential
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000

theorem ceil_sides (d u r:ℕ):
    MarkedAdaptive.price (Fintype.card I) d 179730*u≤(seedWeight d u:ℚ) ∧
    MarkedAdaptive.price (Fintype.card I) d 179730*r≤(ordWeight d r:ℚ):=by
  let R:=MarkedAdaptive.price (Fintype.card I) d 179730
  have x:=Nat.le_ceil (R*u)
  let ext:ℚ:=((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ)
  have t:=Nat.le_ceil (R*r+ext)
  have en:0≤ext:=by dsimp [ext];positivity
  constructor
  · change R*u≤((⌈R*u⌉₊+4:ℕ):ℚ);push_cast;linarith
  · change R*r≤((⌈R*r+ext⌉₊+4:ℕ):ℚ);push_cast;linarith

private theorem round_area {t d r u s g v x:ℕ}
    (cost:(t:ℚ)≤((2*(g*u*s+v*r*s+x*r*u):ℕ):ℚ)*MarkedAdaptive.price (Fintype.card I) d 179730^2):
    t≤2*g*seedWeight d u*seedWeight d s+2*ordWeight d r*(v*seedWeight d s+x*seedWeight d u):=by
  let R:=MarkedAdaptive.price (Fintype.card I) d 179730
  have rn:0≤R:=by dsimp [R,MarkedAdaptive.price];positivity
  have ⟨ub,rb⟩:=ceil_sides d u r
  have sb:=(ceil_sides d s r).1
  change R*u≤_ at ub
  change R*r≤_ at rb
  change R*s≤_ at sb
  have xy:=mul_le_mul ub sb (by positivity) (Nat.cast_nonneg _)
  have ry:=mul_le_mul rb sb (by positivity) (Nat.cast_nonneg _)
  have rx:=mul_le_mul rb ub (by positivity) (Nat.cast_nonneg _)
  have x1:=mul_le_mul_of_nonneg_left xy (Nat.cast_nonneg g : (0:ℚ)≤g)
  have x2:=mul_le_mul_of_nonneg_left ry (Nat.cast_nonneg v : (0:ℚ)≤v)
  have x3:=mul_le_mul_of_nonneg_left rx (Nat.cast_nonneg x : (0:ℚ)≤x)
  push_cast at cost
  change (t:ℚ)≤2*(g*u*s+v*r*s+x*r*u)*R^2 at cost
  have upper:(t:ℚ)≤2*g*(seedWeight d u:ℚ)*seedWeight d s+2*(ordWeight d r:ℚ)*(v*(seedWeight d s:ℚ)+x*(seedWeight d u:ℚ)):=by
    linarith only [cost,x1,x2,x3]
  exact_mod_cast upper

theorem price {u₀ del} {M:P1.ModelAt 33755 u₀ del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    {d u s:ℕ} (char:(2*G.graphDegree-1)*u<p)
    (total:∀j i,((N.poly.coeff j).coeff i).totalDegree≤u)
    (one:∀j i,((N.poly.coeff j).coeff i).degreeOf 1≤s)
    (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p)
    {H:Equation} (hn:H≠0) (laws:∀z∈T,WordRates.law F N z) (surf:∀z∈T,WordRates.ev F z H=0):
    T.card≤(2*G.graphDegree-1)*((p+1)*u)+2*H.natDegree*seedWeight d u*seedWeight d s+
      2*ordWeight d (G.graphDegree-1)*(K1_14_4.seedDegree H*seedWeight d s+KoalaRect.axisDegree H 1*seedWeight d u):=by
  classical
  let r:=G.graphDegree-1
  have rp:0<r:=by dsimp [r];omega
  have ref:0<seedWeight d s:=by unfold seedWeight;omega
  have rb:0<seedWeight d u:=by unfold seedWeight;omega
  have hc:=(K1_14_4.seedDegree_le_iff H _).mp le_rfl
  let V:=K1_14_4.seedDegree H
  let X₁:=KoalaRect.axisDegree H 1
  obtain ⟨S,part,good,fail⟩:=WordRates.good F N gp total char laws
  have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
  have deg z (hz:z∈S):(F.scalar z).natDegree≤d:=by
    rcases (F.mark z (sub (part hz))).scalar_degree with zero|h
    · simp [zero]
    · change ((F.scalar z).natDegree:ℤ)≤131071+M.overhead at h;omega
  have enough:S.card≤2*H.natDegree*seedWeight d u*seedWeight d s+
      2*ordWeight d r*(V*seedWeight d s+X₁*seedWeight d u):=by
    by_cases uz:u=0
    · subst u
      by_cases vz:V=0
      · have raw:=ZeroSeeds.roots F (part.trans sub) H hn (fun i=>Nat.eq_zero_of_le_zero ((hc i).trans_eq vz)) (fun z hz=>surf z (part hz))
        have first:H.natDegree≤2*H.natDegree*seedWeight d 0*seedWeight d s:=
          ((Nat.le_mul_of_pos_left _ (by decide:0<2)).trans (Nat.le_mul_of_pos_right _ rb)).trans (Nat.le_mul_of_pos_right _ ref)
        exact raw.trans (first.trans (Nat.le_add_right ..))
      · have raw:=WordRates.constant_regular F N gp nonlinear total (part.trans sub) phys dp gap tame
          (fun z hz=>laws z (part hz)) good
        apply raw.trans
        apply (Nat.le_mul_of_pos_left (ordWeight d r) (by decide:0<2)).trans
        apply (Nat.le_mul_of_pos_right _ (show 0<V*seedWeight d s+X₁*seedWeight d 0 from
          (Nat.mul_pos (Nat.pos_of_ne_zero vz) ref).trans_le (Nat.le_add_right ..))).trans
        exact Nat.le_add_left .. 
    obtain ⟨ay,byDeg⟩:=NativeGraphMarks.equation_degrees N gp
    have ax j i:((N.poly.coeff j).coeff i).degreeOf 0≤u:=(MvPolynomial.degreeOf_le_totalDegree ..).trans (total j i)
    by_cases sz:s=0
    · have restrict (j:ℕ):OneSeed.supportedOn 0 (N.poly.coeff j):=by
        intro i k ne
        have kk:k=1:=by fin_cases k <;>simp_all
        rw [kk];exact Nat.eq_zero_of_le_zero ((one j i).trans_eq sz)
      have restrictB:OneSeed.supportedOn 0 (rhs N):=by intro i k nk;simpa [rhs,coeff_neg] using restrict 0 i k nk
      have c:=OneSeed.native F (part.trans sub) 0 rp (Nat.pos_of_ne_zero uz) dp gap fit tame
        (den N) (rhs N) H ay (byDeg.trans (by dsimp [r];omega)) (restrict 1) restrictB
        (ax 1) (fun i=>by simpa [rhs,coeff_neg] using ax 0 i) hn le_rfl
        (fun i=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (hc i)) deg
        (fun z hz=>laws z (part hz)) good (fun z hz=>surf z (part hz))
      have notzero (no:¬OneSeed.supportedOn 0 H):0<X₁:=by
        by_contra! zero
        apply no
        intro i k ne
        have kk:k=1:=by fin_cases k <;>simp_all
        rw [kk]
        exact Nat.eq_zero_of_le_zero (((KoalaRect.axisDegree_le_iff H 1 X₁).mp le_rfl i).trans zero)
      have nn:0≤MarkedAdaptive.price (Fintype.card I) d 179730:=by unfold MarkedAdaptive.price;positivity
      exact RectNative.one_axis_price (OneSeed.supportedOn 0 H) nn c notzero _ _ (ceil_sides d u r).1 (ceil_sides d u r).2 ref
    let U:Fin 2→ℕ:=![u,s]
    let W:Fin 2→ℕ:=![V,X₁]
    have axis j i (k:Fin 2):((N.poly.coeff j).coeff i).degreeOf k≤U k:=by fin_cases k;exact ax j i;exact one j i
    have haxis (k:Fin 2) i:(H.coeff i).degreeOf k≤W k:=by
      fin_cases k
      · exact (MvPolynomial.degreeOf_le_totalDegree ..).trans (hc i)
      · exact (KoalaRect.axisDegree_le_iff H 1 X₁).mp le_rfl i
    have counted:=RectNative.regular F (part.trans sub) U W rp (by intro k;fin_cases k;exact Nat.pos_of_ne_zero uz;exact Nat.pos_of_ne_zero sz)
      dp gap tame (den N) (rhs N) H ay (byDeg.trans (by dsimp [r];omega)) (fun k i=>axis 1 i k)
      (fun k i=>by simpa only [rhs,coeff_neg,MvPolynomial.degreeOf_neg] using axis 0 i k) hn le_rfl haxis deg
      (fun z hz=>⟨laws z (part hz),good z hz,surf z (part hz)⟩)
    exact round_area counted
  dsimp only [r,V,X₁] at enough
  omega

end
end Research6969.RectWordPrice
end Z6969Source2547

-- Source: Research6969.PriceMethod
section Z6969Source2548
set_option autoImplicit true
namespace Research6969.PriceMethod
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L atX jetAt graphEval)
open K1_14_1 (PoleData CRTLift poleProduct MarkResidues)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

inductive Mode where | marked | markedAxis | affine | surface | separate | ambient | node (fee:ℕ)
deriving DecidableEq
structure Rate where
  cash:ℕ
  y:ℕ
  seed:ℕ
  axis:ℕ
deriving DecidableEq

def rates (m:Mode) (d a u sideCap g allSeed:ℕ):Rate:=
  let b:=FastHeight.side d u
  let x:=FastHeight.side d sideCap
  let y:=FastHeight.ordinate d (a-1)
  let bad:=(2*a-1)*((p+1)*u)
  match m with
  | .marked=>⟨ThreeLedger.tail g,0,ThreeLedger.rate g*p,0⟩
  | .markedAxis=>⟨ThreeLedger.tail g+ThreeLedger.rate g*allSeed,0,0,ThreeLedger.rate g*p⟩
  | .affine=>⟨WholeAffine.fee d (max 1 u),0,0,0⟩
  | .surface=>⟨bad,b^2,2*b*y,0⟩
  | .separate=>⟨bad,2*b*x,2*y*x,2*y*b⟩
  | .ambient=>⟨bad+3*y*b^2,0,0,0⟩
  | .node fee=>⟨fee,0,0,0⟩

theorem rate_mono:Monotone ThreeLedger.rate:=by
  intro i j le
  by_cases zero:i=0
  · simp [zero,ThreeLedger.rate]
  · have jn:j≠0:=by omega
    simp only [ThreeLedger.rate,ite_eq_right zero,ite_eq_right jn]
    exact Nat.sub_le_sub_right (Nat.add_le_add (Near6969FactorPrice.rate_mono (max_le_max_left 3 le))
      (Nat.mul_le_mul_left 2 le)) _
theorem tail_mono:Monotone ThreeLedger.tail:=by
  intro i j le
  exact Nat.mul_le_mul (Nat.sub_le_sub_right (max_le_max_left 3 le) _) le

def Rate.pay (t:Rate) (f:Equation):ℕ:=
  t.cash+t.y*f.natDegree+t.seed*K1_14_4.seedDegree f+t.axis*KoalaRect.axisDegree f 1

/-- The native root tariff and both of its possible seed-width bounds. -/
theorem marked {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) (hi:M.overhead.toNat≤2557) {f:Equation} (prim:f.IsPrimitive)
    (sep:(f.map (algebraMap K1_14.Seeds SeedField)).Separable) {k cap:ℕ} (small:k<64) (grade:f.natDegree≤k)
    (mass:K1_14_4.seedDegree f≤cap) (safe:(2*k-1)*cap<p) (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (d a v side:ℕ):
    T.card≤(rates .marked d a v side k cap).pay f ∧ T.card≤(rates .markedAxis d a v side k cap).pay f := by
  have h:=ThreeLedger.marked F sub hi prim sep (grade.trans_lt small)
    ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 grade) _) mass).trans_lt safe) roots
  have coef:=rate_mono grade
  have tail:=tail_mono grade
  have density:=Nat.mul_le_mul_right p coef
  constructor
  · have cost:=h.1.trans (Nat.add_le_add (Nat.mul_le_mul_right _ density) tail)
    simpa [rates,Rate.pay,Nat.add_comm, Nat.add_left_comm,Nat.add_assoc] using cost
  · have cost:=h.2.trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul coef mass) (Nat.mul_le_mul_right _ density)) tail)
    simpa [rates,Rate.pay,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using cost

theorem nonlinear {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ) (sub:T⊆Γ)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (large:2≤G.graphDegree) {d v s:ℕ} (char:(2*G.graphDegree-1)*v<p)
    (top:∀j i,((N.poly.coeff j).coeff i).totalDegree≤v) (narrow:∀j i,((N.poly.coeff j).coeff i).degreeOf 1≤s)
    (ph:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p) {f:Equation} (fn:f≠0)
    (laws:∀z∈T,WordRates.law F N z) (roots:∀ z∈T,WordRates.ev F z f=0) (k cap:ℕ):
    T.card≤(rates .surface d G.graphDegree v s k cap).pay f ∧
    T.card≤(rates .separate d G.graphDegree v s k cap).pay f ∧
    T.card≤(rates .ambient d G.graphDegree v s k cap).pay f:=by
  have ord:=WordRates.on_surface F N gp large top char sub ph dp gap tame fn laws roots
  have rect:=RectWordPrice.price F sub N gp large char top narrow ph dp gap tame fn laws roots
  have direct:=WordRates.ambient F N gp large top char sub ph dp gap tame laws
  rw [FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at ord direct
  simp only [FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at rect
  constructor
  · exact ord.trans_eq (by simp [rates,Rate.pay];ring)
  constructor
  · exact rect.trans_eq (by simp [rates,Rate.pay];ring)
  · simpa [rates,Rate.pay] using direct

end
end Research6969.PriceMethod
end Z6969Source2548

-- Source: Research6969.DistinctCore
section Z6969Source2549
set_option autoImplicit true
namespace Research6969.DistinctCore
noncomputable section
open K1 (K p)
open K1_14 (Equation Jet)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (SeedField Surface)
open K1_14_2_2 (mass)
open Lower6960.Far6969RescueGeometry (Model Family)
open Research6966
open PadeNativeQuotient (Native)
open TransitionPacket (Pair)
open PairedMarks (mainLabels rescueLabels)
open JointLedger (Book)
open Finset Polynomial
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

variable {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat} {Crt:CRTLift D} {H:Jet}
variable {m r:Book} (P:Pair F Crt H m r) {G:Pade.Row SeedField} (B:Native G)
variable {f onEq offEq:Equation} (C:PairedComparison.Base P B f onEq offEq)

theorem shared_invoice (extra:ℕ) {off low hi seedMax axisMax:ℕ} (high:M.overhead.toNat≤2557) (three:3≤P.mainGrade)
    (small:off<64) (safe:(2*off-1)*m.seedMass<p) (offCap:C.main.offEq.natDegree≤off)
    (lowG:low≤C.main.onEq.natDegree) (highG:C.main.onEq.natDegree≤hi)
    (maxSeed:K1_14_4.seedDegree C.main.onEq≤seedMax) (maxAxis:KoalaRect.axisDegree C.main.onEq 1≤axisMax)
    (K₀ coefficientY coefficientSeed coefficientAxis:ℤ) (positive:0≤coefficientAxis)
    (localFee:(C.main.onLabels.card:ℤ)+extra≤K₀+coefficientY*C.main.onEq.natDegree+
      coefficientSeed*K1_14_4.seedDegree C.main.onEq+coefficientAxis*KoalaRect.axisDegree C.main.onEq 1)
    (rcost:ℕ)
    (rescue:(rescueLabels P).card≤extra+r.ordinateCredit*C.rescueFull.natDegree+
      r.seedCredit*K1_14_4.seedDegree C.rescueFull+rcost):
    (Γ.card:ℤ)≤m.fee+r.fee+GraphLedger.excess m P.mainGrade off low hi seedMax axisMax
        K₀ coefficientY coefficientSeed coefficientAxis+rcost := by
  obtain ⟨t,td,te,tv,tw,ta,n₀,n₁⟩:=GraphLedger.inputs C.main (PairedMarks.main_sub P) high m P.mainGrade off
    three P.aSrc P.mainActive P.mainOrigin P.mainDegreeCap P.boundsM offCap small safe 1
  let q:= { t with onMarks:=t.onMarks+extra }
  have step:=GraphLedger.bound q low hi seedMax axisMax K₀ coefficientY coefficientSeed coefficientAxis
    (by simpa only [q,td,tv,ta,n₀,Nat.cast_add] using localFee) (td ▸ lowG) (td ▸ highG) (tv ▸ maxSeed) (ta ▸ maxAxis) positive
  dsimp only [q] at step
  rw [td,te,tv,tw,n₀,n₁,Nat.cast_add] at step
  have funding:=PairedComparison.budgets P B C
  have funds:(P.paid.card:ℤ)+m.ordinateCredit*((C.main.onEq.natDegree:ℤ)+C.main.offEq.natDegree)+
      m.seedCredit*((K1_14_4.seedDegree C.main.onEq:ℤ)+K1_14_4.seedDegree C.main.offEq)+
      r.ordinateCredit*(C.rescueFull.natDegree:ℤ)+r.seedCredit*(K1_14_4.seedDegree C.rescueFull:ℤ)≤m.fee+r.fee:=by
    exact_mod_cast funding
  have part:=C.main.size
  have total:(Γ.card:ℤ)≤P.paid.card+((C.main.onLabels.card:ℤ)+C.main.offLabels.card)+(rescueLabels P).card:=by
    exact_mod_cast (part ▸ PairedMarks.total P)
  have rp:((rescueLabels P).card:ℤ)≤extra+r.ordinateCredit*(C.rescueFull.natDegree:ℤ)+
      r.seedCredit*(K1_14_4.seedDegree C.rescueFull:ℤ)+rcost:=by exact_mod_cast rescue
  linarith only [step,funds,total,rp]

theorem invoice {off low hi seedMax axisMax:ℕ} (high:M.overhead.toNat≤2557) (three:3≤P.mainGrade)
    (small:off<64) (safe:(2*off-1)*m.seedMass<p) (offCap:C.main.offEq.natDegree≤off)
    (lowG:low≤C.main.onEq.natDegree) (highG:C.main.onEq.natDegree≤hi)
    (maxSeed:K1_14_4.seedDegree C.main.onEq≤seedMax) (maxAxis:KoalaRect.axisDegree C.main.onEq 1≤axisMax)
    (K₀ coefficientY coefficientSeed coefficientAxis:ℤ) (positive:0≤coefficientAxis)
    (localFee:(C.main.onLabels.card:ℤ)≤K₀+coefficientY*C.main.onEq.natDegree+
      coefficientSeed*K1_14_4.seedDegree C.main.onEq+coefficientAxis*KoalaRect.axisDegree C.main.onEq 1)
    (rcost:ℕ)
    (rescue:(rescueLabels P).card≤r.ordinateCredit*C.rescueFull.natDegree+
      r.seedCredit*K1_14_4.seedDegree C.rescueFull+rcost):
    (Γ.card:ℤ)≤m.fee+r.fee+GraphLedger.excess m P.mainGrade off low hi seedMax axisMax
        K₀ coefficientY coefficientSeed coefficientAxis+rcost := by
  apply shared_invoice P B C 0 high three small safe offCap lowG highG maxSeed maxAxis
    K₀ coefficientY coefficientSeed coefficientAxis positive _ rcost _
  · simpa using localFee
  · simpa using rescue


end
end Research6969.DistinctCore
end Z6969Source2549

-- Source: Research6969.PairCell
section Z6969Source2550
set_option autoImplicit true
namespace Research6969.PairCell
noncomputable section
open Finset Polynomial
open K1 (K I p)
open K1_14 (Jet Equation FX L)
open K1_14_2_2_2_1 (seedDegree)
open K1_14_3 (Surface SeedField ProjectedProduct)
open Lower6960.Far6969RescueGeometry (word)
open Research6966
open TransitionPacket.NormalCatalogue (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open HighPackets (State)
open NormalGeometry (Geometry helper nativeHelper)
open PriceMethod (Mode Rate)
open scoped Classical
set_option maxRecDepth 14000
set_option maxHeartbeats 1900000

structure Row where
  lowerGrade:ℕ
  upperGrade:ℕ
  content:ℕ
  graph:ℕ
  seedLo:ℕ
  seedHi:Option ℕ
  axisLo:ℕ
  axisHi:Option ℕ
  wt:ℕ
  tests:List MeasuredBound.Test
  rect:List AxisTests.Test

def Row.off (b:Row):=b.content-b.graph
def Row.cross (b:Row):=2+b.graph-1
def Row.loPrimary (b:Row):=b.lowerGrade-b.off-b.cross
def Row.cap (b:Row) (i:Fin 18):NormalGeometry.Bounds:=
  NormalGeometry.limits ⟨b.upperGrade,(mainBook i).seedMass+(rescueBook i).seedMass⟩ b.tests (if b.axisHi.isSome then b.rect else [])
    b.graph b.seedLo b.wt b.seedHi b.axisLo (b.axisHi.getD 0)
def Row.gm (b:Row) (i:Fin 18):=min (b.cap i).grade (savedMainGrade i)
def Row.vm (b:Row) (i:Fin 18):=min (b.cap i).seed (mainBook i).seedMass
def Row.gr (b:Row) (i:Fin 18):=min (b.cap i).grade (savedRescueGrade i)
def Row.vr (b:Row) (i:Fin 18):=min (b.cap i).seed (rescueBook i).seedMass

structure Facts {i} (s:State i) (b:Row):Prop where
  gradeLow:b.lowerGrade≤s.f.natDegree
  gradeHigh:s.f.natDegree≤b.upperGrade
  control:NormalGeometry.content s=b.content
  degree:s.graph.graphDegree=b.graph
  seedLow:b.seedLo≤seedDegree s.native.poly
  seedHigh:∀v,b.seedHi=some v→seedDegree s.native.poly≤v
  axisLow:b.axisLo≤PadeNativeQuotient.axis s.native.poly 1
  axisHigh:∀v,b.axisHi=some v→PadeNativeQuotient.axis s.native.poly 1≤v
  physical:b.wt≤NormalGeometry.weight s

theorem caps {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s):
    z.onPoly.natDegree≤(b.cap i).grade ∧ K1_14_4.seedDegree z.onPoly≤(b.cap i).seed ∧
      KoalaRect.axisDegree z.onPoly 1≤(b.cap i).axis:=by
  cases height:b.axisHi with
  | none=>
    have bounds:=NormalGeometry.measured s z b.tests [] b.upperGrade b.graph b.seedLo b.wt b.axisLo
      (PadeNativeQuotient.axis s.native.poly 1) b.seedHi h.gradeHigh h.degree h.seedLow h.seedHigh h.axisLow le_rfl h.physical
    simpa only [Row.cap,height,Option.isSome_none,Bool.false_eq_true,ite_false,Option.getD_none,
      NormalGeometry.limits,AxisTests.run] using bounds
  | some v=>
    have bounds:=NormalGeometry.measured s z b.tests b.rect b.upperGrade b.graph b.seedLo b.wt b.axisLo v
      b.seedHi h.gradeHigh h.degree h.seedLow h.seedHigh h.axisLow (h.axisHigh v height) h.physical
    simpa only [Row.cap,height,Option.isSome_some,ite_true,Option.getD_some] using bounds

theorem primary_bounds {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s):
    z.pairData.main.onEq.natDegree≤b.gm i ∧ K1_14_4.seedDegree z.pairData.main.onEq≤b.vm i ∧
      KoalaRect.axisDegree z.pairData.main.onEq 1≤(b.cap i).axis ∧ z.pairData.main.offEq.natDegree≤b.off := by
  obtain ⟨grade,seedCap,axis⟩:=caps s b h z
  have d:=natDegree_le_of_dvd z.pairData.mainOn_dvd z.onWitness.1.primitive.ne_zero
  have v:=JointOwnership.rescue_caps z.onWitness.1 z.pairData.mainOn_dvd
  have m:=GraphPartition.measured z.pairData.main s.pair.aSrc s.pair.mainActive s.pair.mainOrigin
  have off:=natDegree_le_of_dvd z.pairData.mainOff_dvd z.offProduct.primitive.ne_zero
  refine ⟨le_min (d.trans grade) (((Nat.le_add_right ..).trans (m.1.trans s.pair.mainDegreeCap)).trans_eq s.mainGrade),
    le_min (v.2.1.trans seedCap) ((Nat.le_add_right ..).trans (m.2.trans s.pair.boundsM)),(v.2.2 1).trans axis,?_⟩
  have bound:=z.offCap
  rw [h.control,h.degree] at bound
  exact off.trans bound

theorem distinct_total {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s)
    (different:GraphIntersection.determinant (nativeHelper s) s.native≠0):
    z.pairData.rescueFull.natDegree≤b.off+b.cross ∧ s.f.natDegree≤z.pairData.main.onEq.natDegree+b.off+b.cross := by
  have d0:=NormalGeometry.helper_degree s
  have pos:0<s.graph.graphDegree:=by unfold Pade.Row.graphDegree;exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  have d1:=(SharedGraphCount.degrees (nativeHelper s) s.native (PhysicalHelperTariff.primitive s.prime s.slope) s.gp
    (by omega) pos (NormalGeometry.helper_cap s) ((K1_14_2_2_2_1.seedDegree_le s.native.poly _).mp le_rfl)).1
  rw [d0,h.degree] at d1
  have off:=z.offCap
  rw [h.control,h.degree] at off
  obtain ⟨r,total⟩:=PairedComparison.distinct s.pair (nativeHelper s) s.native z.pairData s.product z.offProduct
    (PhysicalHelperTariff.primitive s.prime s.slope) s.gp rfl different d1 off
  exact ⟨r,total⟩

theorem distinct_bounds {i} (s:State i) (b:Row) (h:Facts s b) (z:Geometry s)
    (different:GraphIntersection.determinant (nativeHelper s) s.native≠0):
    z.pairData.rescueFull.natDegree≤b.off+b.cross ∧ b.loPrimary≤z.pairData.main.onEq.natDegree := by
  obtain ⟨rcap,all⟩:=distinct_total s b h z different
  have left:=h.gradeLow
  exact ⟨rcap,by unfold Row.loPrimary;omega⟩

end
end Research6969.PairCell
end Z6969Source2550

-- Source: Research6969.OnTariffHeader
section Z6969Source2551
set_option autoImplicit true
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

def Legal (how:Mode) (a:ℕ) (height narrow:Option ℕ) (grade mainSeed last cutoff:ℕ):Prop:=
  match how with
  | .marked=>grade<64 ∧ (2*grade-1)*mainSeed<p
  | .markedAxis=>grade<64 ∧ (2*grade-1)*mainSeed<p
  | .affine=>a=1 ∧ height.isSome=true ∧ max 1 (height.getD 0)<p
  | .surface=>2≤a ∧ height.isSome=true ∧ (2*a-1)*(height.getD 0)<p
  | .ambient=>2≤a ∧ height.isSome=true ∧ (2*a-1)*(height.getD 0)<p
  | .separate=>2≤a ∧ height.isSome=true ∧ narrow.isSome=true ∧ (2*a-1)*(height.getD 0)<p
  | .node fee=>a=2 ∧ height.isSome=true ∧ 3*height.getD 0<p ∧ NodeBudget.Valid last (height.getD 0) cutoff fee

instance (how a h s g v last w):Decidable (Legal how a h s g v last w):=by
  cases how <;>unfold Legal <;>infer_instance

def NodeGuard (how:Mode) (act cutoff:ℕ):Prop:=match how with | .node _=>act<cutoff | _=>True

theorem selected {u:Option ℕ} (yes:u.isSome=true):u=some (u.getD 0):=by
  cases u <;> simp_all

theorem degree_bound {h:ℤ} (bound:h.toNat≤2411):131071+h≤(133482:ℤ):=by omega

end
end Research6969.OnTariff
end Z6969Source2551

-- Source: Research6969.PairPrices
section Z6969Source2552
set_option autoImplicit true
namespace Research6969.PairPrices
open K1 (p)
open HighPackets (State)
open TransitionPacket.NormalCatalogue (mainBook rescueBook savedMainGrade savedRescueGrade seed)
open PairCell (Row)
open PriceMethod (Mode Rate)
open Finset
set_option maxHeartbeats 1300000
set_option maxRecDepth 12500

inductive Rescue where | whole | intersection
deriving DecidableEq
inductive Same where | impossible | marked | surface | node (allowance:ℕ)
deriving DecidableEq

structure Decision where
  main:Mode
  rescue:Rescue
  same:Same
  cutoff:ℕ

abbrev d:ℕ:=133482
def sx (i:Fin 18):=FastHeight.side d (seed i)
def sy:=FastHeight.ordinate d 1
def modeNode:Mode→Bool | .node _=>true | _=>false
def primaryRate (b:Row) (i:Fin 18) (p:Decision):Rate:=
  PriceMethod.rates p.main d b.graph (b.seedHi.getD 0) (b.axisHi.getD 0) (b.gm i) (mainBook i).seedMass

def primaryCharge (b:Row) (i:Fin 18) (p:Decision):ℤ:=
  let t:=primaryRate b i p
  GraphLedger.excess (mainBook i) (savedMainGrade i) b.off b.loPrimary (b.gm i) (b.vm i) (b.cap i).axis
    ((savedMainGrade i)^2+t.cash:ℕ) t.y t.seed t.axis

def crossCharge (b:Row) (i:Fin 18):ℕ:=b.cross*(sx i)^2+2*(seed i+b.seedHi.getD 0)*sx i*sy

def rescueCharge (b:Row) (i:Fin 18) (p:Decision):ℕ:=
  match p.rescue with
  | .whole=>RescuePrice.ticket (rescueBook i) (b.off+b.cross) (sx i) sy
  | .intersection=>RescuePrice.ticket (rescueBook i) b.off (sx i) sy+
      if modeNode p.main then 0 else crossCharge b i

def distinctOK (b:Row) (i:Fin 18) (p:Decision):Prop:=
  savedMainGrade i<b.loPrimary ∨
  (OnTariff.Legal p.main b.graph b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2411 p.cutoff ∧
    (match p.rescue with | .whole=>True | .intersection=>modeNode p.main=true ∨ b.seedHi.isSome=true) ∧
    ((mainBook i).fee:ℤ)+(rescueBook i).fee+primaryCharge b i p+rescueCharge b i p≤CertifiedCell.target)

def impossible (b:Row) (i:Fin 18):Prop:=
  b.graph≠2 ∨ seed i<b.seedLo ∨ (match b.seedHi with | none=>False | some v=>v<seed i) ∨
    savedRescueGrade i<b.lowerGrade-b.off

def sameOK (b:Row) (i:Fin 18) (p:Decision):Prop:=
  let pay:=SameCore.due (mainBook i) (rescueBook i) b.off b.lowerGrade (b.gr i) (b.vr i)
  match p.same with
  | .impossible=>impossible b i
  | .marked=>(b.gr i)<64 ∧ (2*b.gr i-1)*b.vr i<K1.p ∧
      pay (ThreeLedger.tail (b.gr i)) 0 (JointLedger.coefficient (b.gr i))≤CertifiedCell.target
  | .surface=>pay 0 ((sx i)^2:ℕ) (2*sx i*sy:ℕ)≤CertifiedCell.target
  | .node fee=>b.graph=2 ∧ b.seedHi.isSome=true ∧ 3*b.seedHi.getD 0<K1.p ∧ NodeBudget.Valid 2411 (b.seedHi.getD 0) p.cutoff fee ∧
      pay fee 0 0≤CertifiedCell.target

def valid (b:Row) (i:Fin 18) (p:Decision):Prop:=
  b.content<b.lowerGrade ∧ 3≤savedMainGrade i ∧ b.off+b.cross<64 ∧ (2*b.off-1)*(mainBook i).seedMass<K1.p ∧
  (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<K1.p ∧ distinctOK b i p ∧ sameOK b i p

instance (b:Row) (i:Fin 18):Decidable (impossible b i):=by unfold impossible;cases b.seedHi <;>infer_instance
instance (b:Row) (i:Fin 18) (p:Decision):Decidable (distinctOK b i p):=by unfold distinctOK;cases p.rescue <;>infer_instance
instance (b:Row) (i:Fin 18) (p:Decision):Decidable (sameOK b i p):=by unfold sameOK;cases p.same <;>infer_instance
instance (b:Row) (i:Fin 18) (p:Decision):Decidable (valid b i p):=by unfold valid;infer_instance
end Research6969.PairPrices
end Z6969Source2552

-- Source: Research6969.PairRoute
section Z6969Source2553
set_option autoImplicit true
namespace Research6969.PairRoute
noncomputable section
open HighPackets (State)
open OrdinaryRoute (Region)
open PairCell (Row)
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 9000

structure Window where
  region:Region
  axisLo:ℕ
  axisHi:Option ℕ
  weightLo:ℕ
  weightHi:Option ℕ
deriving DecidableEq

def of_row (b:Row) (wh:Option ℕ):Window:=
  ⟨⟨b.lowerGrade,b.upperGrade,b.content,b.graph,b.seedLo,b.seedHi⟩,b.axisLo,b.axisHi,b.wt,wh⟩

structure Applies {i} (s:State i) (w:Window):Prop where
  root:NormalRoute.Applies s w.region
  al:w.axisLo≤Research6966.PadeNativeQuotient.axis s.native.poly 1
  ah:∀n,w.axisHi=some n→Research6966.PadeNativeQuotient.axis s.native.poly 1≤n
  wl:w.weightLo≤NormalGeometry.weight s
  wh:∀n,w.weightHi=some n→NormalGeometry.weight s<n

abbrev Done (i:Fin 18) (w:Window):Prop:=∀s:State i,Applies s w→s.labels.card≤CertifiedCell.target

theorem facts {i} {s:State i} {b:Row} {w:Option ℕ} (h:Applies s (of_row b w)):PairCell.Facts s b :=
  ⟨h.root.1,h.root.2.1,h.root.2.2.1,h.root.2.2.2.1,h.root.2.2.2.2.1,h.root.2.2.2.2.2,h.al,h.ah,h.wl⟩

theorem weight {i r l u low high} (cut:ℕ)
    (left:Done i ⟨r,l,u,low,some cut⟩) (right:Done i ⟨r,l,u,cut,high⟩):
    Done i ⟨r,l,u,low,high⟩:=by
  intro s h
  by_cases below:NormalGeometry.weight s<cut
  · exact left s ⟨h.root,h.al,h.ah,h.wl,fun v eq=>by
      have same:cut=v:=Option.some.inj eq;simpa [←same] using below⟩
  · exact right s ⟨h.root,h.al,h.ah,Nat.le_of_not_lt below,h.wh⟩

theorem axis {i r lo hi w high} (cut:ℕ)
    (left:Done i ⟨r,lo,some cut,w,high⟩) (right:Done i ⟨r,cut+1,hi,w,high⟩):
    Done i ⟨r,lo,hi,w,high⟩:=by
  intro s h
  by_cases below:Research6966.PadeNativeQuotient.axis s.native.poly 1≤cut
  · exact left s ⟨h.root,h.al,fun v eq=>by
      have same:cut=v:=Option.some.inj eq;simpa [←same] using below,h.wl,h.wh⟩
  · exact right s ⟨h.root,by change cut+1≤_;omega,h.ah,h.wl,h.wh⟩

theorem axes_of_total {i e top c a lo hi wt high}
    (all:Done i ⟨⟨e,top,c,a,lo,some hi⟩,0,some hi,wt,high⟩):
    Done i ⟨⟨e,top,c,a,lo,some hi⟩,0,none,wt,high⟩:=by
  intro s h
  have seed:=h.root.2.2.2.2.2 hi rfl
  have axis:Research6966.PadeNativeQuotient.axis s.native.poly 1≤hi:=
    (Research6966.NearTerminal.axis_seed s.native.poly 1).trans seed
  exact all s ⟨h.root,h.al,fun v eq=>by have same:hi=v:=Option.some.inj eq;simpa [←same] using axis,h.wl,h.wh⟩

theorem grade {i e top c a sl su l u w wh} (mid:ℕ)
    (left:Done i ⟨⟨e,mid,c,a,sl,su⟩,l,u,w,wh⟩)
    (right:Done i ⟨⟨mid+1,top,c,a,sl,su⟩,l,u,w,wh⟩) :
    Done i ⟨⟨e,top,c,a,sl,su⟩,l,u,w,wh⟩:=by
  intro s h
  obtain ⟨gl,gh,ct,d,low,up⟩:=h.root
  by_cases lower:s.f.natDegree≤mid
  · exact left s ⟨⟨gl,lower,ct,d,low,up⟩,h.al,h.ah,h.wl,h.wh⟩
  · exact right s ⟨⟨by change mid+1≤_;omega,gh,ct,d,low,up⟩,h.al,h.ah,h.wl,h.wh⟩

theorem splitSeed {i e top c a lo hi l u w wh} (cut:ℕ)
    (left:Done i ⟨⟨e,top,c,a,lo,some cut⟩,l,u,w,wh⟩)
    (right:Done i ⟨⟨e,top,c,a,cut+1,some hi⟩,l,u,w,wh⟩) :
    Done i ⟨⟨e,top,c,a,lo,some hi⟩,l,u,w,wh⟩:=by
  intro s h
  obtain ⟨gl,gh,ct,d,low,up⟩:=h.root
  by_cases lower:K1_14_2_2_2_1.seedDegree s.native.poly≤cut
  · exact left s ⟨⟨gl,gh,ct,d,low,fun v eq=>by
      have same:cut=v:=Option.some.inj eq
      simpa [←same] using lower⟩,h.al,h.ah,h.wl,h.wh⟩
  · exact right s ⟨⟨gl,gh,ct,d,by change cut+1≤_;omega,up⟩,h.al,h.ah,h.wl,h.wh⟩

theorem start {i} (r:Region) (all:Done i ⟨r,0,none,r.graph*(131071-2411)-1,none⟩):NormalRoute.Done i r:=by
  intro s h
  have degree:=h.2.2.2.1
  exact all s ⟨h,Nat.zero_le _,by simp,degree ▸ NormalGeometry.base s,by simp⟩

end
end Research6969.PairRoute
end Z6969Source2553

-- Source: Research6969.OnTariffMarked
section Z6969Source2554
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem marked_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .marked G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard .marked (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .marked 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  exact (PriceMethod.marked F sub (hi.trans (by decide)) prim sep legal.1 limit seed legal.2 roots
    133482 G.graphDegree (width.getD 0) (axis.getD 0)).1

end
end Research6969.OnTariff
end Z6969Source2554

end Merged_Z6969Pack0932

-- merged module Z6969Pack0933
section Merged_Z6969Pack0933

-- Source: Research6969.OnTariffMarkedAxis
section Z6969Source2555
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem markedAxis_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .markedAxis G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard .markedAxis (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .markedAxis 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  exact (PriceMethod.marked F sub (hi.trans (by decide)) prim sep legal.1 limit seed legal.2 roots
    133482 G.graphDegree (width.getD 0) (axis.getD 0)).2

end
end Research6969.OnTariff
end Z6969Source2555

-- Source: Research6969.OnTariffAffine
section Z6969Source2556
set_option autoImplicit true
set_option Elab.async false
set_option maxHeartbeats 100000
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

attribute [local irreducible] WholeAffine.fee FastHeight.side FastHeight.ordinate
private theorem affine_pay (d a w x g u:ℕ) (f:Equation):
    (PriceMethod.rates .affine d a w x g u).pay f=WholeAffine.fee d (max 1 w):=by
  simp only [PriceMethod.rates,PriceMethod.Rate.pay,Nat.zero_mul,Nat.add_zero]

set_option maxHeartbeats 100000
theorem affine_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .affine G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard .affine (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .affine 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  rw [affine_pay]
  obtain ⟨linear,present,small⟩:=legal
  have member:T⊆UnionTariffs.group F N parents:=by
    intro z hz
    obtain ⟨q,hq,contains,vanishes⟩:=owners z hz
    exact Finset.mem_filter.mpr ⟨sub hz,q,Finset.mem_filter.mpr ⟨hq,contains⟩,vanishes⟩
  have widthCap:K1_14_2_2_2_1.seedDegree N.poly≤max 1 (width.getD 0):=
    (trueWidth _ (selected present)).trans (le_max_right ..)
  exact (Finset.card_le_card member).trans (UnionTariffs.affine (d:=133482) (w:=max 1 (width.getD 0))
    F N parents gp linear (Nat.zero_lt_one.trans_le (le_max_left ..)) small widthCap (degree_bound hi)
    (by decide:0<133482) (by decide:133482<179730) (by decide:133482<K1.p))

end
end Research6969.OnTariff
end Z6969Source2556

-- Source: Research6969.OnTariffSurface
section Z6969Source2557
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem surface_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .surface G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard .surface (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .surface 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133482
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2314).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  have laws z (hz:z∈T):WordRates.law F N z:=by
    obtain ⟨q,_,owned,atQ⟩:=owners z hz;exact NativeGraphMarks.mark_law N gp owned atQ
  have on z (hz:z∈T):WordRates.ev F z f=0:=by
    have root:=roots z hz
    rw [Polynomial.eval_map] at root
    exact root
  obtain ⟨big,yes,char⟩:=legal
  have pay:=WordRates.on_surface F N gp big (bounds yes) char sub ph dp gap tame prim.ne_zero laws on
  rw [FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at pay
  exact pay.trans_eq (by simp [PriceMethod.rates,PriceMethod.Rate.pay,d];ring)

end
end Research6969.OnTariff
end Z6969Source2557

-- Source: Research6969.OnTariffAmbient
section Z6969Source2558
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem ambient_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .ambient G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard .ambient (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .ambient 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133482
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2314).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  have laws z (hz:z∈T):WordRates.law F N z:=by
    obtain ⟨q,_,owned,atQ⟩:=owners z hz;exact NativeGraphMarks.mark_law N gp owned atQ
  obtain ⟨big,yes,char⟩:=legal
  have pay:=WordRates.ambient F N gp big (bounds yes) char sub ph dp gap tame laws
  rw [FastHeight.side_eq,FastHeight.ordinate_eq d _ gap] at pay
  simpa [PriceMethod.rates,PriceMethod.Rate.pay,d] using pay

end
end Research6969.OnTariff
end Z6969Source2558

-- Source: Research6969.OnTariffSeparate
section Z6969Source2559
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem separate_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ)  (legal:Legal .separate G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard .separate (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates .separate 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133482
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2314).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  have laws z (hz:z∈T):WordRates.law F N z:=by
    obtain ⟨q,_,owned,atQ⟩:=owners z hz;exact NativeGraphMarks.mark_law N gp owned atQ
  have on z (hz:z∈T):WordRates.ev F z f=0:=by
    have root:=roots z hz
    rw [Polynomial.eval_map] at root
    exact root
  obtain ⟨big,yes,thin,char⟩:=legal
  have point:=trueAxis (axis.getD 0) (selected thin)
  have one:∀j k,((N.poly.coeff j).coeff k).degreeOf 1≤axis.getD 0:=(PadeNativeQuotient.axis_le ..).mp point
  exact (PriceMethod.nonlinear F sub N gp big char (bounds yes) one ph dp gap tame prim.ne_zero laws on grade v).2.1

end
end Research6969.OnTariff
end Z6969Source2559

-- Source: Research6969.OnTariffNode
section Z6969Source2560
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem node_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ) (fee:ℕ) (legal:Legal (.node fee) G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard (.node fee) (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates (.node fee) 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  classical
  let d:=133482
  have ph:131071+M.overhead≤(d:ℤ):=degree_bound hi
  have dp:0<d:=by decide
  have gap:d<179730:=by decide
  have tame:d<p:=by decide
  have age:0<M.overhead.toNat:=(by decide:0<2314).trans_le lo
  have bounds (yes:width.isSome=true):∀j k,((N.poly.coeff j).coeff k).totalDegree≤width.getD 0:=
    (K1_14_2_2_2_1.seedDegree_le N.poly (width.getD 0)).mp (trueWidth _ (selected yes))
  obtain ⟨q,yes,char,ok⟩:=legal
  have pay:=NodeBudget.family F sub rfl age hi (by decide) phys (OrdinaryCell.native_prime N gp) (NativeGraphMarks.slope_degree N gp)
    ((HelperWeightCap.native_degree N gp).trans q) char (bounds yes) nodes res
    (fun z hz=>by obtain ⟨q,_,hit,mark⟩:=owners z hz;exact mark _ hit) nodeGuard ok
  simpa only [PriceMethod.rates,PriceMethod.Rate.pay,Nat.zero_mul,Nat.add_zero] using pay

end
end Research6969.OnTariff
end Z6969Source2560

-- Source: Research6969.OnTariff
section Z6969Source2561
set_option autoImplicit true
set_option Elab.async false
namespace Research6969.OnTariff
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation FX L Seeds jetAt atX graphEval)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open K1_14_3 (Surface SeedField)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open PriceMethod (Mode Rate)
open Finset Polynomial
open scoped Classical Differential
set_option maxHeartbeats 1800000
set_option maxRecDepth 11000

theorem on_marks {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) {D:PoleData M.overhead.toNat} (Crt:CRTLift D) {G:Pade.Row SeedField} (N:Native G)
    (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {parents:Finset Surface} (owners:NativeAffineRows.Owned F T parents N)
    {f:Equation} (prim:f.IsPrimitive) (sep:(f.map (algebraMap Seeds SeedField)).Separable)
    (roots:∀z∈T,(f.map (graphEval (M.label z))).eval (atX (F.scalar z))=0)
    (grade v cap:ℕ) (width axis:Option ℕ) (how:Mode) (legal:Legal how G.graphDegree width axis grade v 2411 cap)
    (limit:f.natDegree≤grade) (seed:K1_14_4.seedDegree f≤v)
    (trueWidth:∀u,width=some u→K1_14_2_2_2_1.seedDegree N.poly≤u)
    (trueAxis:∀u,axis=some u→PadeNativeQuotient.axis N.poly 1≤u)
    (lo:2314≤M.overhead.toNat) (hi:M.overhead.toNat≤2411)
    (nodeGuard:NodeGuard how (RawPhysicalDegree.weight (131071-M.overhead.toNat) (131071-M.overhead.toNat-1) phys.raw) cap)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)):
    T.card≤(PriceMethod.rates how 133482 G.graphDegree (width.getD 0) (axis.getD 0) grade v).pay f:=by
  cases how with
  | marked=>exact marked_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | markedAxis=>exact markedAxis_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | affine=>exact affine_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | surface=>exact surface_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | ambient=>exact ambient_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | separate=>exact separate_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res
  | node fee=>exact node_marks F sub Crt N gp phys owners prim sep roots grade v cap width axis fee legal limit seed trueWidth trueAxis lo hi nodeGuard nodes res

end
end Research6969.OnTariff
end Z6969Source2561

-- Source: Research6969.DistinctPaymentCharges
section Z6969Source2562
set_option autoImplicit true
namespace Research6969.DistinctPaymentCharges
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (rescueBook)
set_option Elab.async false
set_option maxRecDepth 2000
attribute [local irreducible] RescuePrice.ticket PairPrices.sx PairPrices.sy
  PairPrices.crossCharge TransitionPacket.NormalCatalogue.rescueBook

theorem nodeCharge {b : Row} {i : Fin 18} {p₀ : Decision}
    (mode : p₀.rescue = .intersection) (node : PairPrices.modeNode p₀.main = true) :
    PairPrices.rescueCharge b i p₀ =
      RescuePrice.ticket (rescueBook i) b.off (PairPrices.sx i) PairPrices.sy := by
  unfold PairPrices.rescueCharge
  rw [mode]
  change _ + (if PairPrices.modeNode p₀.main=true then 0 else PairPrices.crossCharge b i) = _
  rw [if_pos node, Nat.add_zero]


theorem graphCharge {b : Row} {i : Fin 18} {p₀ : Decision}
    (mode : p₀.rescue = .intersection) (node : ¬ PairPrices.modeNode p₀.main = true) :
    PairPrices.rescueCharge b i p₀ =
      RescuePrice.ticket (rescueBook i) b.off (PairPrices.sx i) PairPrices.sy+PairPrices.crossCharge b i := by
  unfold PairPrices.rescueCharge
  rw [mode]
  change _ + (if PairPrices.modeNode p₀.main=true then 0 else PairPrices.crossCharge b i) = _
  rw [if_neg node]

end Research6969.DistinctPaymentCharges
end Z6969Source2562

-- Source: Research6969.DistinctPaymentRescueCore
section Z6969Source2563
set_option autoImplicit true
namespace Research6969.DistinctPaymentRescue
noncomputable section

open K1 (p)
open Research6966
open HighPackets (State)
open NormalGeometry (Geometry nativeHelper)
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (rescueBook seed)
open PairedMarks (rescueLabels)
open Polynomial
open scoped Classical

set_option Elab.async false
set_option maxRecDepth 13000
set_option maxHeartbeats 2500000
attribute [local irreducible] FastHeight.side FastHeight.ordinate RescuePrice.ticket
  TransitionPacket.NormalCatalogue.rescueBook

private theorem wholeCharge {b : Row} {i : Fin 18} {p₀ : Decision}
    (mode : p₀.rescue = .whole) :
    PairPrices.rescueCharge b i p₀ =
      RescuePrice.ticket (rescueBook i) (b.off+b.cross) (PairPrices.sx i) PairPrices.sy := by
  rw [PairPrices.rescueCharge, mode]

theorem whole {i} (s : State i) (b : Row) (z : Geometry s) (p₀ : Decision)
    (mode : p₀.rescue = .whole) (cap : z.pairData.rescueFull.natDegree≤b.off+b.cross)
    (small : b.off+b.cross<64)
    (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    (rescueLabels s.pair).card≤(rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+PairPrices.rescueCharge b i p₀ := by
  have degree := NormalGeometry.helper_degree s
  have pos : 0<seed i := Nat.zero_lt_succ _
  have result := RescueComparison.full s.pair (nativeHelper s) s.native z.pairData
    (PhysicalHelperTariff.primitive s.prime s.slope) rfl degree.ge pos (NormalGeometry.helper_cap s)
    (OnTariff.degree_bound s.higher) (by decide) (by decide) (by decide)
    (s.higher.trans (by decide)) cap small safe
  rw [degree,FastHeight.side_eq,FastHeight.ordinate_eq 133482 _ (by decide)] at result
  rw [wholeCharge mode]
  exact result

theorem outside {i} (s : State i) (b : Row) (h : PairCell.Facts s b) (z : Geometry s)
    (small : b.off+b.cross<64)
    (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    z.pairData.rescue.offLabels.card≤(rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+
        RescuePrice.ticket (rescueBook i) b.off (PairPrices.sx i) PairPrices.sy := by
  have offRes : z.pairData.rescue.offEq.natDegree≤b.off :=
    (natDegree_le_of_dvd z.pairData.rescueOff_dvd z.offProduct.primitive.ne_zero).trans (by
      have no:=z.offCap;rw [h.control,h.degree] at no;exact no)
  have le : b.off≤b.off+b.cross := Nat.le_add_right _ _
  have sR : (2*b.off-1)*(rescueBook i).seedMass<p :=
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 le) _)).trans_lt safe
  have degree := NormalGeometry.helper_degree s
  have pos : 0<seed i := Nat.zero_lt_succ _
  have result := RescueComparison.outside s.pair (nativeHelper s) s.native z.pairData
    (PhysicalHelperTariff.primitive s.prime s.slope) rfl degree.ge pos (NormalGeometry.helper_cap s)
    (OnTariff.degree_bound s.higher) (by decide) (by decide) (by decide)
    (s.higher.trans (by decide)) offRes (le.trans_lt small) sR
  rw [degree,FastHeight.side_eq,FastHeight.ordinate_eq 133482 _ (by decide)] at result
  exact result


end
end Research6969.DistinctPaymentRescue
end Z6969Source2563

-- Source: Research6969.DistinctPaymentRescue
section Z6969Source2564
set_option autoImplicit true
namespace Research6969.DistinctPaymentRescue
noncomputable section

open K1 (p)
open Research6966
open HighPackets (State)
open NormalGeometry (Geometry nativeHelper)
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (rescueBook seed)
open PairedMarks (rescueLabels)
open Polynomial
open scoped Classical

set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1500000
attribute [local irreducible] FastHeight.side FastHeight.ordinate RescuePrice.ticket
  TransitionPacket.NormalCatalogue.rescueBook

private theorem node_rescue_count (n a b x y ticket cost : ℕ) (split : a+b=n)
    (off : b≤x+y+ticket) (eq : cost=ticket) : n≤a+x+y+cost := by omega

theorem node_rescue {i} (s : State i) (b : Row) (h : PairCell.Facts s b) (z : Geometry s)
    (p₀ : Decision) (mode : p₀.rescue = .intersection) (node : PairPrices.modeNode p₀.main = true)
    (small : b.off+b.cross<64) (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    (rescueLabels s.pair).card≤z.pairData.rescue.onLabels.card+
      (rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+PairPrices.rescueCharge b i p₀ := by
  have cost := DistinctPaymentCharges.nodeCharge (b:=b) (i:=i) mode node
  exact node_rescue_count
    (rescueLabels s.pair).card z.pairData.rescue.onLabels.card z.pairData.rescue.offLabels.card
    ((rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree)
    ((rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull)
    (RescuePrice.ticket (rescueBook i) b.off (PairPrices.sx i) PairPrices.sy)
    (PairPrices.rescueCharge b i p₀) z.pairData.rescue.size (outside s b h z small safe) cost


end
end Research6969.DistinctPaymentRescue
end Z6969Source2564

-- Source: Research6969.DistinctPaymentIntersection
section Z6969Source2565
set_option autoImplicit true
namespace Research6969.DistinctPaymentRescue
noncomputable section

open K1 (p)
open Research6966
open HighPackets (State)
open NormalGeometry (Geometry nativeHelper)
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (rescueBook seed)
open PairedMarks (rescueLabels)
open Polynomial
open scoped Classical

set_option Elab.async false
set_option maxRecDepth 13000
set_option maxHeartbeats 2500000
attribute [local irreducible] FastHeight.side FastHeight.ordinate RescuePrice.ticket
  TransitionPacket.NormalCatalogue.rescueBook

private theorem graph_rescue_count (n a b x y ticket cross cost : ℕ) (split : a+b=n)
    (off : b≤x+y+ticket) (on : a≤cross) (eq : cost=ticket+cross) : n≤x+y+cost := by omega

theorem graph_rescue {i} (s : State i) (b : Row) (h : PairCell.Facts s b) (z : Geometry s)
    (p₀ : Decision) (mode : p₀.rescue = .intersection) (node : ¬ PairPrices.modeNode p₀.main = true)
    (different : GraphIntersection.determinant (nativeHelper s) s.native≠0) (given : b.seedHi.isSome=true)
    (small : b.off+b.cross<64) (safe : (2*(b.off+b.cross)-1)*(rescueBook i).seedMass<p) :
    (rescueLabels s.pair).card≤(rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree+
      (rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull+PairPrices.rescueCharge b i p₀ := by
  have bound:=(K1_14_2_2_2_1.seedDegree_le ..).mp (h.seedHigh _ (OnTariff.selected given))
  have positive:0<s.graph.graphDegree:=by
    unfold Pade.Row.graphDegree
    exact (Nat.zero_lt_succ _).trans_le (le_max_left ..)
  have degree := NormalGeometry.helper_degree s
  have pos : 0<seed i := Nat.zero_lt_succ _
  have inter:=RescueComparison.intersection s.pair (nativeHelper s) s.native z.pairData
    (PhysicalHelperTariff.primitive s.prime s.slope) s.gp rfl degree.ge positive pos
    (NormalGeometry.helper_cap s) bound different (OnTariff.degree_bound s.higher)
    (by decide) (by decide) (by decide)
  rw [degree,h.degree,FastHeight.side_eq,FastHeight.ordinate_eq 133482 _ (by decide)] at inter
  have cross : z.pairData.rescue.onLabels.card≤PairPrices.crossCharge b i := by
    rw [PairPrices.crossCharge,PairCell.Row.cross,PairPrices.sx,PairPrices.sy]
    exact inter
  have cost := DistinctPaymentCharges.graphCharge (b:=b) (i:=i) mode node
  exact graph_rescue_count
    (rescueLabels s.pair).card z.pairData.rescue.onLabels.card z.pairData.rescue.offLabels.card
    ((rescueBook i).ordinateCredit*z.pairData.rescueFull.natDegree)
    ((rescueBook i).seedCredit*K1_14_4.seedDegree z.pairData.rescueFull)
    (RescuePrice.ticket (rescueBook i) b.off (PairPrices.sx i) PairPrices.sy)
    (PairPrices.crossCharge b i) (PairPrices.rescueCharge b i p₀)
    z.pairData.rescue.size (outside s b h z small safe) cross cost


end
end Research6969.DistinctPaymentRescue
end Z6969Source2565

-- Source: Research6969.DistinctPaymentNode
section Z6969Source2566
set_option autoImplicit true
namespace Research6969.DistinctPaymentNode
noncomputable section
open K1_14 (jetAt)
open Research6966
open HighPackets (State)
open NormalGeometry (Geometry)
open PairCell (Row)
open PairPrices (Decision)
open TransitionPacket.NormalCatalogue (mainBook)
open Finset
open scoped Classical

set_option Elab.async false
set_option maxHeartbeats 2500000
set_option maxRecDepth 13000
attribute [local irreducible] TransitionPacket.NormalCatalogue.mainBook

private theorem node_mode (m : PriceMethod.Mode) (h : PairPrices.modeNode m = true) :
    ∃ fee, m = .node fee := by
  cases m <;> cases h; exact ⟨_,rfl⟩


theorem pays {i} (s : State i) (b : Row) (h : PairCell.Facts s b) (z : Geometry s) (p₀ : Decision)
    (node : PairPrices.modeNode p₀.main = true)
    (legal : OnTariff.Legal p₀.main b.graph b.seedHi b.axisHi (b.gm i) (mainBook i).seedMass 2411 p₀.cutoff)
    (nodeGuard : OnTariff.NodeGuard p₀.main (NormalGeometry.weight s) p₀.cutoff) :
    z.pairData.main.onLabels.card+z.pairData.rescue.onLabels.card≤
      (PairPrices.primaryRate b i p₀).pay z.pairData.main.onEq := by
  let C := z.pairData
  obtain ⟨fee,which⟩ := node_mode p₀.main node
  rw [which] at legal nodeGuard
  obtain ⟨q,yes,char,ok⟩:=legal
  let U:=C.main.onLabels∪C.rescue.onLabels
  have sub:U⊆s.labels:=by
    intro y hy
    exact (mem_union.mp hy).elim (fun l=>PairedMarks.main_sub s.pair (C.main.onSub l))
      (fun r=>PairedMarks.rescue_sub s.pair (C.rescue.onSub r))
  have hit y (hy:y∈U):jetAt s.native.poly (s.model.label y) (s.F.scalar y)=0:=by
    rcases mem_union.mp hy with m|r
    · obtain ⟨q,hq,atQ⟩:=C.main.onMarks y m;exact atQ s.native.poly (mem_filter.mp hq).2
    · obtain ⟨q,hq,atQ⟩:=C.rescue.onMarks y r;exact atQ s.native.poly (mem_filter.mp hq).2
  have count:=NodeBudget.family s.F sub rfl ((by decide:0<2314).trans_le s.lower) s.higher (by decide)
    s.physical (OrdinaryCell.native_prime s.native s.gp) (NativeGraphMarks.slope_degree s.native s.gp)
    ((HelperWeightCap.native_degree s.native s.gp).trans (h.degree.trans q)) char
    ((K1_14_2_2_2_1.seedDegree_le ..).mp (h.seedHigh _ (OnTariff.selected yes)))
    s.nodes (fun y hy=>s.residues y (sub hy)) hit nodeGuard ok
  have dis:Disjoint C.main.onLabels C.rescue.onLabels:=Finset.disjoint_left.mpr (fun y hm hr=>
    (PairedMarks.main s.pair (C.main.onSub hm)).1 (PairedMarks.rescue s.pair (C.rescue.onSub hr)).1)
  change (C.main.onLabels∪C.rescue.onLabels).card≤fee at count
  rw [card_union_of_disjoint dis] at count
  simpa only [PairPrices.primaryRate,which,PriceMethod.rates,PriceMethod.Rate.pay,Nat.zero_mul,Nat.add_zero] using count

end
end Research6969.DistinctPaymentNode
end Z6969Source2566

end Merged_Z6969Pack0933
