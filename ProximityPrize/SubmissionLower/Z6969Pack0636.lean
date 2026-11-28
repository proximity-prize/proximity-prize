import ProximityPrize.SubmissionLower.Z6969Pack0635
import ProximityPrize.SubmissionLower.R6966ProofPhysicalHelperTariff
import ProximityPrize.SubmissionLower.Z6969Pack0589
import ProximityPrize.SubmissionLower.R6966ProofNativeWitnessBank
import ProximityPrize.SubmissionLower.Z6969Pack0558
import ProximityPrize.SubmissionLower.R6966ProofHelperWindowNative

set_option Elab.async false

-- Source: Research6969.ZeroSeeds
section Z6969Source0845
set_option autoImplicit true
namespace Research6969.ZeroSeeds
noncomputable section
open K1 (I K p)
open K1_14 (FX atX)
open OneSeed
open Research6966.NonlinearMarkRows (Eqn evaluate)
open Finset MvPolynomial
open scoped Classical Differential
attribute [local instance] Research6966.GenericPhysicalCentre.physical Research6966.GenericPhysicalCentre.seeds
set_option maxHeartbeats 1100000
set_option maxRecDepth 7500

def coefficients (P:Eqn (Fin 2) FX):Polynomial FX:=P.map (eval (fun _=>0))

theorem source_eq (P:Eqn (Fin 2) FX) (empty:∀i,(P.coeff i).totalDegree=0) :
    (coefficients P).map MvPolynomial.C=P := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map,coefficients,Polynomial.coeff_map]
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (empty n),MvPolynomial.eval_C]

theorem read (P:Eqn (Fin 2) FX) (empty:∀i,(P.coeff i).totalDegree=0) (z:Fin 2→FX) (y:FX) :
    evaluate z y P=(coefficients P).eval y := by
  conv_lhs=>rw [←source_eq P empty]
  change Polynomial.eval₂ _ y ((coefficients P).map _)=_
  rw [Polynomial.eval₂_map]
  have h:(MvPolynomial.eval z).comp (MvPolynomial.C:FX→+*MvPolynomial (Fin 2) FX) = RingHom.id _:=by ext;simp
  rw [h,Polynomial.eval₂_id]

private theorem supported (P:Eqn (Fin 2) FX) (empty:∀i,(P.coeff i).totalDegree=0) (j:Fin 2):supportedOn j P := by
  intro n k _
  exact Nat.eq_zero_of_le_zero ((MvPolynomial.degreeOf_le_totalDegree _ _).trans_eq (empty n))

/-- When the differential equation has no seed, every regular word lies
on the dummy zero-seed line. Its point count costs only the ordinate degree. -/
theorem line {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ) (sub:T⊆Γ)
    {r d:ℕ} (rp:0<r) (dp:0<d) (gap:d<179730) (tame:d<p)
    (A B:Eqn (Fin 2) FX) (ay:A.natDegree≤r) (byDeg:B.natDegree≤r+1)
    (az:∀i,(A.coeff i).totalDegree=0) (bz:∀i,(B.coeff i).totalDegree=0)
    (degree:∀z∈T,(F.scalar z).natDegree≤d)
    (laws:∀z∈T,let ev:=evaluate (NativeSurfaceCount.label (M.label z)) (atX (F.scalar z))
      (ev A*atX (F.scalar z).derivative=ev B) ∧ ev A≠0) :
    (T.card:ℚ)≤(r:ℚ)*MarkedAdaptive.price (Fintype.card I) d 179730 := by
  let H:Eqn (Fin 2) FX:=Polynomial.C (MvPolynomial.X 0)
  have hm:supportedOn 0 H:=by
    intro n k hk
    cases n with
    | zero=>simp [H,MvPolynomial.degreeOf_X,Ne.symm hk,hk]
    | succ n=>simp [H]
  have hv (i:ℕ):(H.coeff i).degreeOf 0≤1:=by
    cases i <;>simp [H,MvPolynomial.degreeOf_X]
  have size:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
  have pair (z) (hz:z∈T):
      evaluate (fun _=>0) (atX (F.scalar z)) A * atX (F.scalar z).derivative =
        evaluate (fun _=>0) (atX (F.scalar z)) B ∧ evaluate (fun _=>0) (atX (F.scalar z)) A≠0:=by
    simpa only [read A az,read B bz] using laws z hz
  have bound:=OneSeed.native_at F sub (fun _ _=>0) (fun _ _=>map_zero _) 0 rp (by decide : 0<1)
    dp gap size tame A B H ay byDeg (supported A az 0) (supported B bz 0)
    (fun i=>((MvPolynomial.degreeOf_le_totalDegree _ _).trans_eq (az i)).trans (by decide:0≤1))
    (fun i=>((MvPolynomial.degreeOf_le_totalDegree _ _).trans_eq (bz i)).trans (by decide:0≤1))
    (show H≠0 by simp [H]) (show H.natDegree≤0 by simp [H]) hv degree
    (fun z hz=>(pair z hz).1) (fun z hz=>(pair z hz).2)
    (fun z _=>by simp [H,evaluate])
  simpa [hm] using bound

/-- A seed-independent retained equation has at most its degree many
distinct marked words, regardless of the number of labels. -/
theorem roots {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
    (sub:T⊆Γ) (H:Eqn (Fin 2) FX) (hn:H≠0) (empty:∀i,(H.coeff i).totalDegree=0)
    (hits:∀z∈T,evaluate (NativeSurfaceCount.label (M.label z)) (atX (F.scalar z)) H=0) : T.card≤H.natDegree:=by
  classical
  have nz:coefficients H≠0:=fun zero=>hn ((source_eq H empty).symm.trans (by rw [zero,Polynomial.map_zero]))
  have inject:Set.InjOn (fun z=>atX (F.scalar z)) (T:Set K):=
    K1_14_3.scalar_atX_injective.comp_injOn (F.distinct.mono sub)
  rw [←card_image_of_injOn inject]
  apply (Polynomial.card_le_degree_of_subset_roots (p:=coefficients H) ?_).trans Polynomial.natDegree_map_le
  rintro x hx
  obtain ⟨z,hz,rfl⟩:=mem_image.mp hx
  exact (Polynomial.mem_roots nz).mpr ((read H empty _ _).symm.trans (hits z hz))

end
end Research6969.ZeroSeeds
end Z6969Source0845

-- Source: Research6969.NodeBudget
section Z6969Source0846
set_option autoImplicit true
namespace Research6969.NodeBudget
open K1 (K I p)
open K1_14 (Jet L jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct)
open Research6966
open Finset
set_option maxHeartbeats 1300000
set_option maxRecDepth 9000

abbrev A:ℕ:=179730
abbrev n:ℕ:=262144
def num (d u:ℕ):ℕ:=(n-A)*((2*d-1)*u)+(A-d)
def linePrice (d u:ℕ):ℕ:=num d u^2/(A-d)^2
def singular (u:ℕ):ℕ:=3*(u+p*u)
def votes (h w:ℕ):ℕ:=A-(w-(131071-h-1))

theorem line_mono {x y u:ℕ} (le:x≤y) (gap:y<A) : linePrice x u≤linePrice y u:=by
  have small:0<A-y:=by omega
  have db:A-y≤A-x:=Nat.sub_le_sub_left le _
  have big:0<A-x:=small.trans_le db
  have coeff:(n-A)*((2*x-1)*u)≤(n-A)*((2*y-1)*u):=Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 le) 1))
  have frac:num x u*(A-y)≤num y u*(A-x):=by
    have l:=Nat.mul_le_mul coeff db
    unfold num;rw [Nat.add_mul,Nat.add_mul,Nat.mul_comm (A-x) (A-y)]
    exact Nat.add_le_add_right l _
  have sq:=Nat.pow_le_pow_left frac 2
  rw [Nat.mul_pow,Nat.mul_pow] at sq
  have div:linePrice x u*(A-x)^2≤(num x u)^2:=Nat.div_mul_le_self .. 
  apply (Nat.le_div_iff_mul_le (pow_pos small _)).mpr
  apply Nat.le_of_mul_le_mul_right (c:=(A-x)^2) _ (pow_pos big _)
  calc (linePrice x u*(A-y)^2)*(A-x)^2=(linePrice x u*(A-x)^2)*(A-y)^2:=by ring
       _≤num x u^2*(A-y)^2:=Nat.mul_le_mul_right _ div
       _≤_:=sq

def Valid (last u cutoff fee:ℕ):Prop:=
  0<votes last (cutoff-1) ∧ singular u≤fee ∧ n*linePrice (131071+last) u≤(fee-singular u)*votes last (cutoff-1)

instance (last u cutoff fee:ℕ):Decidable (Valid last u cutoff fee):=by unfold Valid;infer_instance

theorem from_votes {last h u cutoff fee count wt:ℕ} (hi:h≤last) (legal:131071+last<A)
    (below:wt<cutoff) (ok:Valid last u cutoff fee)
    (bound:count*votes h wt≤singular u*votes h wt+n*linePrice (131071+h) u) : count≤fee:=by
  obtain ⟨vp,safe,price⟩:=ok
  have fit:votes last (cutoff-1)≤votes h wt:=by unfold votes;omega
  have per:=line_mono (u:=u) (Nat.add_le_add_left hi 131071) legal
  have rhs:n*linePrice (131071+h) u≤(fee-singular u)*votes h wt:=
    (Nat.mul_le_mul_left n per).trans (price.trans (Nat.mul_le_mul_left _ fit))
  apply Nat.le_of_mul_le_mul_right (c:=votes h wt) _ (vp.trans_le fit)
  exact bound.trans ((Nat.add_le_add_left rhs _).trans_eq (by rw [←Nat.add_mul,Nat.add_sub_of_le safe]))

theorem family {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt A M Γ) (sub:T⊆Γ)
    {h last width cutoff fee:ℕ} (hEq:h=M.overhead.toNat) (hp:0<h) (hi:h≤last) (lastFit:last≤2557)
    {D:PoleData h} {Crt:CRTLift D} {G:Jet} (phys:HelperPhysicalModel.Model Crt G) (prime:Prime G)
    (slope:G.natDegree=1) (quad:K1_14_2_2_2_1.jetDegree G=2) (char:3*width<p)
    (cap:∀j i,((G.coeff j).coeff i).totalDegree≤width)
    (nodes:∀ i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀z∈T,MarkResidues D (M.label z) (F.scalar z)) (belongs:∀z∈T,jetAt G (M.label z) (F.scalar z)=0)
    (low:RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw<cutoff) (ok:Valid last width cutoff fee): T.card≤fee:=by
  have hl:h≤131070:=by omega
  have primeCap:131071+h<p:=by change 131071+h<2130706433;omega
  have lastA:131071+last<A:=by change 131071+last<179730;omega
  have physical:131071+M.overhead≤(131071+h:ℕ):=by omega
  have priced:=PhysicalHelperTariff.price F sub hp hl phys prime slope quad width (131071+h) cap char
    physical le_rfl primeCap (by omega) nodes res belongs
  rw [show Fintype.card I=n from Fintype.card_fin (2^18)] at priced
  exact from_votes hi lastA low ok priced

end Research6969.NodeBudget
end Z6969Source0846

-- Source: Research6969.WordRates
section Z6969Source0847
set_option autoImplicit true
namespace Research6969.WordRates
noncomputable section
open K1 (K I p)
open K1_14 (FX Equation Jet atX jetAt)
open K1_14_3 (SeedField)
open Research6966
open Research6966.NativeGraphExceptional (den rhs)
open Research6966.NonlinearMarkRows (evaluate)
open NativeSurfaceCount (label)
open Finset Polynomial
open scoped Classical Differential
attribute [local instance] GenericPhysicalCentre.physical GenericPhysicalCentre.seeds
set_option maxRecDepth 9500
set_option maxHeartbeats 1600000

variable {u del} {M:P1.ModelAt 33755 u del} {Γ T:Finset K} (F:P1.FamilyAt 179730 M Γ)
variable {G:Pade.Row SeedField} (N:Research6966.PadeNativeQuotient.Native G)

abbrev ev (z:K):Equation→+*FX:=evaluate (label (M.label z)) (atX (F.scalar z))
def regular (z:K):Prop:=ev F z (den N)≠0
def law (z:K):Prop:=ev F z (den N)*atX (F.scalar z).derivative=ev F z (rhs N)

theorem good (gp:G.primitive) {width:ℕ} (cap:∀j i,((N.poly.coeff j).coeff i).totalDegree≤width)
    (char:(2*G.graphDegree-1)*width<p) (laws:∀z∈T,law F N z) :
    ∃S:Finset K,S⊆T ∧ (∀z∈S,regular F N z) ∧ T.card≤(2*G.graphDegree-1)*((p+1)*width)+S.card:=by
  classical
  let bad:=T.filter (fun z=>ev F z (den N)=0)
  have id:Function.Injective M.label:=fun _ _ e=>sub_left_inj.mp e
  have charge:=NativeGraphExceptional.singular_count N gp (fun _=>width)
    (fun j i z=>(MvPolynomial.degreeOf_le_totalDegree ..).trans (cap j i)) char bad _ id.injOn
    (fun z=>atX (F.scalar z)) (fun z h=>(mem_filter.mp h).2) (by
      intro z hz;have e:=laws z (mem_filter.mp hz).1
      change ev F z (den N)*atX (F.scalar z).derivative=ev F z (rhs N) at e
      rw [(mem_filter.mp hz).2,zero_mul] at e;exact e.symm)
  have badBound:bad.card≤(2*G.graphDegree-1)*((p+1)*width):=by
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm width] using charge
  have club:(T\bad).card+bad.card=T.card:=card_sdiff_add_card_eq_card (filter_subset _ _)
  exact ⟨T\bad,sdiff_subset,fun z hz zero=>(mem_sdiff.mp hz).2 (mem_filter.mpr ⟨(mem_sdiff.mp hz).1,zero⟩),by omega⟩

private theorem degree {d:ℕ} (phys:131071+M.overhead≤(d:ℤ)) (sub:T⊆Γ) {z:K} (hz:z∈T):(F.scalar z).natDegree≤d:=by
  rcases (F.mark z (sub hz)).scalar_degree with zero|bound
  · simp [zero]
  · change ((F.scalar z).natDegree:ℤ)≤131071+M.overhead at bound;omega

theorem constant_regular {d:ℕ} (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    (empty:∀j i,((N.poly.coeff j).coeff i).totalDegree≤0) (sub:T⊆Γ) (phys:131071+M.overhead≤(d:ℤ))
    (dp:0<d) (gap:d<179730) (tame:d<p) (laws:∀z∈T,law F N z) (reg:∀z∈T,regular F N z) :
    T.card≤JointRouted.ordWeight d (G.graphDegree-1):=by
  obtain ⟨ord,rh⟩:=NativeGraphMarks.equation_degrees N gp
  have raw:=ZeroSeeds.line F sub (by omega:0<G.graphDegree-1) dp gap tame (den N) (rhs N) ord
    (rh.trans (by omega)) (fun i=>Nat.eq_zero_of_le_zero (empty 1 i))
    (fun i=>by simpa only [rhs,coeff_neg,MvPolynomial.totalDegree_neg] using Nat.eq_zero_of_le_zero (empty 0 i))
    (fun _ hz=>degree F phys sub hz) (fun z hz=>⟨laws z hz,reg z hz⟩)
  let R:=MarkedAdaptive.price (Fintype.card I) d 179730
  have ceil:=Nat.le_ceil (R*(G.graphDegree-1:ℕ)+((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ))
  have extra:(0:ℚ)≤((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ):=by positivity
  have bound:(T.card:ℚ)≤(JointRouted.ordWeight d (G.graphDegree-1):ℚ):=by
    change (T.card:ℚ)≤((G.graphDegree-1:ℕ):ℚ)*R at raw
    unfold JointRouted.ordWeight
    change (T.card:ℚ)≤((⌈R*(G.graphDegree-1:ℕ)+((Fintype.card I-d:ℕ):ℚ)/(179730-d:ℕ)⌉₊+4:ℕ):ℚ)
    push_cast;linarith
  exact_mod_cast bound

theorem ambient {d width:ℕ} (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    (cap:∀j i,((N.poly.coeff j).coeff i).totalDegree≤width) (char:(2*G.graphDegree-1)*width<p)
    (sub:T⊆Γ) (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p)
    (laws:∀z∈T,law F N z) :
    T.card≤(2*G.graphDegree-1)*((p+1)*width)+3*JointRouted.ordWeight d (G.graphDegree-1)*JointRouted.seedWeight d width^2:=by
  obtain ⟨S,part,good,split⟩:=good F N gp cap char laws
  apply split.trans
  apply Nat.add_le_add_left
  by_cases zero:width=0
  · subst width
    have word:=constant_regular F N gp nonlinear cap (part.trans sub) phys dp gap tame
      (fun z hz=>laws z (part hz)) good
    rw [show JointRouted.seedWeight d 0=4 by simp [JointRouted.seedWeight]]
    exact word.trans ((Nat.le_mul_of_pos_left _ (by decide:0<3)).trans (Nat.le_mul_of_pos_right _ (by decide:0<4^2)))
  · have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
    exact NativeAmbient.round (NativeAmbient.regular F (part.trans sub) N gp nonlinear (Nat.pos_of_ne_zero zero)
      cap phys dp gap fit tame (fun z hz=>laws z (part hz)) good)

theorem on_surface {d width:ℕ} (gp:G.primitive) (nonlinear:2≤G.graphDegree)
    (cap:∀j i,((N.poly.coeff j).coeff i).totalDegree≤width) (char:(2*G.graphDegree-1)*width<p)
    (sub:T⊆Γ) (phys:131071+M.overhead≤(d:ℤ)) (dp:0<d) (gap:d<179730) (tame:d<p)
    {H:Equation} (hn:H≠0) (laws:∀z∈T,law F N z) (roots:∀z∈T,ev F z H=0) :
    T.card≤(2*G.graphDegree-1)*((p+1)*width)+H.natDegree*JointRouted.seedWeight d width^2+
      2*K1_14_4.seedDegree H*JointRouted.seedWeight d width*JointRouted.ordWeight d (G.graphDegree-1) := by
  by_cases zero:width=0
  · subst width
    rw [Nat.mul_zero,Nat.mul_zero,Nat.zero_add,show JointRouted.seedWeight d 0=4 by simp [JointRouted.seedWeight]]
    by_cases s0:K1_14_4.seedDegree H=0
    · have m:=ZeroSeeds.roots F sub H hn (fun i=>Nat.eq_zero_of_le_zero ((K1_14_4.seedDegree_le_iff ..).mp s0.le i)) roots
      simp only [s0,Nat.mul_zero,Nat.zero_mul,Nat.add_zero]
      exact m.trans (Nat.le_mul_of_pos_right _ (by decide))
    · obtain ⟨S,part,reg,split⟩:=good F N gp cap char laws
      have n:=constant_regular F N gp nonlinear cap (part.trans sub) phys dp gap tame (fun z hz=>laws z (part hz)) reg
      simp only [Nat.mul_zero,Nat.zero_add] at split
      exact (split.trans n).trans ((Nat.le_mul_of_pos_left _ (show 0<2*K1_14_4.seedDegree H*4 by positivity)).trans (Nat.le_add_left ..))
  · have fit:179730≤Fintype.card I:=by rw [show Fintype.card I=262144 from Fintype.card_fin (2^18)];decide
    exact NativeSurfaceCount.round_price (NativeSurfaceCount.price_equation F sub hn N gp nonlinear (Nat.pos_of_ne_zero zero)
      cap ((K1_14_4.seedDegree_le_iff ..).mp le_rfl) char phys dp gap fit tame laws roots)

end
end Research6969.WordRates
end Z6969Source0847

-- Source: Research6969.OrdinaryGeometry
section Z6969Source0848
set_option autoImplicit true
namespace Research6969.OrdinaryGeometry
noncomputable section
open K1 (K I p)
open K1_14 (Jet Equation atX jetAt)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (SeedField Surface ProjectedProduct)
open Lower6960
open Far6969RescueGeometry (Model Family OnSurface)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open JointLedger (Book)
open Finset Polynomial
open scoped Classical Differential
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

variable {u del} {M:Model u del} {Γ} {F:Family M Γ} {D:PoleData M.overhead.toNat} {Crt:CRTLift D}
variable {m:Book} {gc:ℕ} (P:Prefix6969Early.Packet F Crt m.fee m.ordinateCredit m.seedCredit gc m.seedMass)
abbrev remaining:=Γ\P.paid

theorem remaining_marks : ∀z∈remaining P,∃q∈P.parents,OnSurface F q z :=
  fun z hz=>(P.cover z (mem_sdiff.mp hz).1).resolve_left (mem_sdiff.mp hz).2

variable {G:Pade.Row SeedField} (N:Native G) {H J:Equation}
variable (S:OffFirst.Parts F (remaining P) P.parents N.poly P.projected H J)

theorem owners:NativeAffineRows.Owned F S.onLabels (NearBook.owning N.poly P.parents) N:=by
  intro z hz
  obtain ⟨q,hq,atQ⟩:=S.onSurface z hz
  exact ⟨q,hq,(mem_filter.mp hq).2,atQ⟩

theorem laws (gp:G.primitive):∀z∈S.onLabels,WordRates.law F N z :=
  fun z hz=>by obtain ⟨_,_,hit,atQ⟩:=owners P N S z hz;exact NativeGraphMarks.mark_law N gp hit atQ

theorem invoice (hi:M.overhead.toNat≤2557) (degreeCap:3≤gc) (moff:JointProjection.Product (NearBook.outside N.poly P.parents) J)
    {off minG maxOn maxSeed:ℕ} (offDeg:J.natDegree≤off) (tiny:off<64) (safe:(2*off-1)*m.seedMass<p)
    (lower:minG≤P.projected.natDegree) (gd:S.onEq.natDegree≤maxOn) (seed:K1_14_4.seedDegree S.onEq≤maxSeed)
    (mode:Bool) (fixed y z:ℤ)
    (onCost:(S.onLabels.card:ℤ)≤(gc:ℤ)^2+fixed+y*S.onEq.natDegree+z*K1_14_4.seedDegree S.onEq):
    (Γ.card:ℤ)≤OrdinaryLedger.due m gc off minG maxOn maxSeed mode fixed y z := by
  let v:=K1_14_4.seedDegree J
  have cap:v≤m.seedMass:=((Nat.le_add_right ..).trans_eq S.seed).trans P.seed_cap
  have pay:=JointMarked.owned_count F (S.offSub.trans sdiff_subset) hi J moff.primitive moff.separable
    (offDeg.trans_lt tiny) le_rfl ((Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 offDeg) _) cap).trans_lt safe)
    S.offRoots
  have tail:=pay.trans (GraphLedger.marked_fee offDeg ((Nat.le_add_right ..).trans (S.degree.le.trans P.degree_cap)) degreeCap)
  have total:Γ.card≤P.paid.card+(S.onLabels.card+S.offLabels.card):=by
    rw [S.partition,Nat.add_comm]
    exact card_le_card_sdiff_add_card
  have prefixPaid:P.paid.card+m.ordinateCredit*(S.onEq.natDegree+J.natDegree)+
      m.seedCredit*(K1_14_4.seedDegree S.onEq+v)≤m.fee:=by
    rw [Nat.add_comm S.onEq.natDegree,S.degree]
    change _+m.seedCredit*(K1_14_4.seedDegree S.onEq+K1_14_4.seedDegree J)≤m.fee
    rw [Nat.add_comm (K1_14_4.seedDegree S.onEq),S.seed]
    exact P.bill
  have ground:minG≤S.onEq.natDegree+J.natDegree:=by rw [Nat.add_comm,S.degree];exact lower
  have seedCap:K1_14_4.seedDegree S.onEq+v≤m.seedMass:=by
    rw [Nat.add_comm];exact S.seed.le.trans P.seed_cap
  exact OrdinaryLedger.counts m gc off minG maxOn maxSeed mode fixed y z total prefixPaid offDeg ground gd seed seedCap
    onCost (by exact_mod_cast tail)

end
end Research6969.OrdinaryGeometry
end Z6969Source0848

-- Source: Research6969.TotalSeedWitness
section Z6969Source0849
set_option autoImplicit true
namespace Research6969.TotalSeedWitness
noncomputable section
open Polynomial Finset
open K1_14 (Jet Equation Shape L SeedBound)
open K1_14_4 (seedView seedDegree seedDegree_le_iff seedDegree_pow)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (SeedField Surface Parent)
open Research6966
open PadeNativeQuotient (Native)
open NativeGraphExceptional (den rhs)
open scoped BigOperators Classical

theorem cleared_bound (A B:Equation) (Q:Jet) (J U u:ℕ)
    (ay:SeedBound A u) (byDeg:SeedBound B u) (degree:Q.natDegree≤J)
    (caps:∀ j,SeedBound (Q.coeff j) U) :
    seedDegree (TerminalProjection.cleared A B Q J)≤U+J*u := by
  have a: (seedView A).totalDegree≤u:=(seedDegree_le_iff ..).mpr ay
  have b: (seedView B).totalDegree≤u:=(seedDegree_le_iff ..).mpr byDeg
  unfold seedDegree TerminalProjection.cleared
  rw [Polynomial.sum_def,map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j hj
  have bound:j≤J:=(le_natDegree_of_mem_supp j hj).trans degree
  have row:(seedView (Q.coeff j)).totalDegree≤U:=(seedDegree_le_iff ..).mpr (caps j)
  rw [map_mul,map_mul,map_pow,map_pow]
  calc _ ≤ ((seedView (Q.coeff j)).totalDegree+(seedView B^j).totalDegree)+
        (seedView A^(J-j)).totalDegree :=
      (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add_right (MvPolynomial.totalDegree_mul _ _) _)
    _ ≤ (U+j*u)+(J-j)*u :=
      Nat.add_le_add (Nat.add_le_add row ((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ b)))
        ((MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ a))
    _ = _ := by rw [Nat.add_assoc,←Nat.add_mul,Nat.add_sub_of_le bound]

/-- A triangular test controls the total degree across the two seeds on
the very same native projected product used in all the other tests. -/
theorem triangular {h agreement r top:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    (phys:HelperPhysicalModel.Model Crt N.poly) {parents:Finset Surface} {H:Equation}
    (chosen:NativeWitnessBank.witnessed N parents H) (bank:P1_7.Bank) {envelope:Shape}
    (u:ℕ) (seeded:K1_14_2.UsesSeed N.poly) (char:bank.shape.U<K1.p) (charB:bank.shape.B<K1.p)
    {L0 lower:ℕ} (physical:L0≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (ulo:lower≤K1_14_2_2_2_1.seedDegree N.poly) (uhi:∀ j,SeedBound (N.poly.coeff j) u)
    (wide:bank.shape.B*(131071-h)≤top) (pos:0<top)
    (nodes:P1_7_1.nodeRows bank.shape=bank.nodeRows)
    (pole:P1_7_1.groupedPoleMoment bank.shape.B bank.shape.J≤bank.poleMoment)
    (surplus:P1_7.debit h bank + ∑ W∈range top,HelperAvoidance.debitAt bank.shape h top W
      G.graphDegree 1 L0 (HelperAvoidance.triSlots bank.shape.U lower) <
      K1_14.triangle bank.shape.U*K1_14.shapeSum bank.shape (fun q j=>top+j-q*(131071-h)))
    (cut:top-1+2*h*r<bank.shape.m*agreement) (fits:TerminalBanks.inside bank.shape envelope)
    (small:r+1<K1.p) (geo:∀ q∈parents,Parent q) (pass:∀ q∈parents,TerminalBanks.Pass Crt word agreement envelope q) :
    (r+1)*seedDegree H≤bank.shape.U+bank.shape.J*u := by
  have nd:=NativeGraphMarks.slope_degree N gp
  obtain ⟨Q,mem,avoid⟩:=HelperAvoidance.triangle_avoiding hp hl Crt word bank phys (NativeWitnessBank.irreducible N gp)
    (by omega) seeded char (HelperWeightCap.native_degree N gp).ge nd.ge physical ulo charB pos wide nodes pole surplus
  have qn:Q≠0:=fun eq=>avoid (eq ▸ dvd_zero _)
  have coeff (j i:ℕ) (nz:(Q.coeff j).coeff i≠0):=
    K1_14_1.evaluated_shape Crt word mem j i nz
  have cap:Q.natDegree≤bank.shape.J := by
    have z : (Q.coeff Q.natDegree).coeff Q.leadingCoeff.natDegree≠0 := by
      rw [Polynomial.coeff_natDegree,Polynomial.coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr qn)
    exact (coeff _ _ z).2.1
  have qs (j):SeedBound (Q.coeff j) bank.shape.U:=by
    intro i
    by_cases nz:(Q.coeff j).coeff i=0
    · simp [nz]
    · exact (coeff j i nz).2.2
  let _:=UniqueFactorizationMonoid.strongNormalizationMonoid (α:=Equation)
  let _:=UniqueFactorizationMonoid.toNormalizedGCDMonoid Equation
  have eq:=NativeProjectedWitness.graph_eq N gp
  have nz:=TerminalProjection.integral_nonzero_of_avoids (den N) (rhs N) Q bank.shape.J cap
    (NativeGraphExceptional.den_ne N gp) (eq ▸ N.primitive) (eq ▸ avoid)
  have div:=chosen.2 Q bank.shape.J (r+1) cap (fun q hq=>TerminalBanks.retained_order
    Crt word (geo q hq) (pass q hq) fits small cut mem)
  have le:=MvPolynomial.totalDegree_le_of_dvd_of_isDomain (map_dvd seedView div)
    ((map_ne_zero_iff _ seedView.injective).mpr nz)
  change seedDegree (H^(r+1))≤seedDegree (TerminalProjection.cleared _ _ Q _) at le
  rw [seedDegree_pow chosen.1.primitive.ne_zero] at le
  exact le.trans (cleared_bound (den N) (rhs N) Q _ _ _ (uhi 1)
    (fun i=>by simpa [rhs,coeff_neg] using uhi 0 i) cap qs)

end
end Research6969.TotalSeedWitness
end Z6969Source0849

-- Source: Research6969.TerminalWitness
section Z6969Source0850
set_option autoImplicit true
namespace Research6969.TerminalWitness
noncomputable section
open Research6966
open Finset
open K1_14 (L Shape Equation SeedBound)
open K1_14_1 (PoleData CRTLift)
open K1_14_3 (Surface Parent SeedField)
open K1_14_2 (UsesSeed)
open K1_14_2_2_2_1 (seedDegree)
open PhysicalWindow (Request Triangular Rectangle Cover agreement)
open PadeNativeQuotient (Native)
open HelperAvoidance (debitAt rectSlots)
open HelperWindowIntervals (box axis)
open HelperWindowNative (orient)
set_option maxHeartbeats 1300000
set_option maxRecDepth 9000

structure Fits (b:Request) (first last:ℕ) (env:Shape):Prop where
  rank:P3_7_1.BankOK b.bank
  shape:TerminalBanks.inside b.shape env
  narrow:b.shape.J<131071-last
  slope:b.slope=1
  seedChar:b.shape.U<K1.p
  order:b.reserve+1<K1.p
  push:2*b.reserve≤b.shape.B
  wide:Lower6960.HelperSource.WidthGuard b.bank agreement first b.reserve

private theorem room {b:Request} {first last h:ℕ} {env:Shape} (fit:Fits b first last env)
    (lo:first≤h) (hi:h≤131070) :
    b.shape.B*(131071-h)≤b.top h ∧ 0<b.top h ∧ b.top h-1+2*h*b.reserve<b.shape.m*agreement := by
  have v:=Lower6960.HelperSource.width_at_height b.bank agreement first h b.reserve lo (by omega) fit.push fit.wide
  change b.shape.B*(131071-h)<b.top h at v
  have nt:0<b.top h:=(Nat.zero_le _).trans_lt v
  refine ⟨v.le,nt,?_⟩
  change 0<b.shape.m*agreement-2*h*b.reserve at nt
  change b.shape.m*agreement-2*h*b.reserve-1+2*h*b.reserve<b.shape.m*agreement
  omega

theorem triangular {b:Request} {first last h:ℕ} {env:Shape} (fits:Fits b first last env) {ends:List ℕ}
    (checked:Cover (Triangular b) last first ends) (lo:first≤h) (hi:h≤last) (pos:0<h) (legal:h≤131070)
    {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive)
    (phys:HelperPhysicalModel.Model Crt N.poly) {S:Finset Surface} {H:Equation} (project:NativeWitnessBank.witnessed N S H)
    (degree:G.graphDegree=b.jet) (seeded:UsesSeed N.poly)
    (physical:b.weight≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (low:b.seed≤seedDegree N.poly) {u:ℕ} (high:∀j,SeedBound (N.poly.coeff j) u)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word agreement env q) :
    (b.reserve+1)*H.natDegree≤b.shape.B+(G.graphDegree-1)*b.shape.J ∧
    (b.reserve+1)*K1_14_4.seedDegree H≤b.shape.U+b.shape.J*u := by
  obtain ⟨l,r,lh,hr,rt,cert⟩:=PhysicalWindow.covered checked lo hi
  have s:=PhysicalWindow.triangle_positive b pos lh hr (fits.narrow.trans_le (Nat.sub_le_sub_left rt _))
    (fits.slope ▸ Nat.zero_lt_one) cert
  rw [←degree,fits.slope] at s
  obtain ⟨wide,nt,cut⟩:=room fits lo legal
  have axisHigh (j i:ℕ) (z:Fin 2):((N.poly.coeff j).coeff i).degreeOf z≤u:=
    (MvPolynomial.degreeOf_le_totalDegree _ _).trans (high j i)
  have d:=NativeWitnessBank.triangular pos legal Crt word N gp phys project b.bank (fun _=>u) seeded
    fits.seedChar fits.rank.moment.2 physical low axisHigh wide nt fits.rank.nodes fits.rank.moment.1
    s cut fits.shape fits.order geo pass
  exact ⟨d.1,TotalSeedWitness.triangular pos legal Crt word N gp phys project b.bank u seeded fits.seedChar
    fits.rank.moment.2 physical low high wide nt fits.rank.nodes fits.rank.moment.1 s cut fits.shape fits.order geo pass⟩

private theorem area_orient (narrow : Fin 2) (U : Fin 2 → ℕ) :
    KoalaRect.area (orient narrow U) = KoalaRect.area U := by
  fin_cases narrow
  · change (U 1+1)*(U 0+1) = (U 0+1)*(U 1+1)
    exact Nat.mul_comm _ _
  · rfl

private theorem sum_orient (narrow : Fin 2) (U : Fin 2 → ℕ) :
    orient narrow U 0+orient narrow U 1 = U 0+U 1 := by
  fin_cases narrow
  · change U 1+U 0=U 0+U 1
    exact Nat.add_comm _ _
  · rfl

private theorem slots_orient (narrow : Fin 2) (U d : Fin 2 → ℕ) :
    rectSlots (orient narrow U) (orient narrow d) = rectSlots U d := by
  funext k
  have fit : (∀ z,k*orient narrow d z ≤ orient narrow U z) ↔ (∀ z,k*d z ≤ U z) := by
    fin_cases narrow
    · constructor <;> intro h z <;> fin_cases z
      · exact h 1
      · exact h 0
      · exact h 1
      · exact h 0
    · constructor <;> intro h z <;> fin_cases z
      · exact h 0
      · exact h 1
      · exact h 0
      · exact h 1
  unfold rectSlots
  by_cases room : ∀ z,k*d z ≤ U z
  · rw [ite_eq_left (fit.mpr room),ite_eq_left room]
    have eq : (fun z => orient narrow U z-k*orient narrow d z) =
        orient narrow (fun z => U z-k*d z) := by
      funext z
      by_cases same : z=narrow <;> simp only [orient,same,ite_true,ite_false]
    rw [eq,area_orient]
  · rw [ite_eq_right (fun h => room (fit.mp h)),ite_eq_right room]


theorem rectangle {b:Request} {first last h v:ℕ} {env:Shape} (fits:Fits b first last env) {ends:List ℕ}
    (checked:Cover (Rectangle b v) last first ends) (vfit:v≤b.shape.U)
    (lo:first≤h) (hi:h≤last) (pos:0<h) (legal:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    {G:Pade.Row SeedField} (N:Native G) (gp:G.primitive) (phys:HelperPhysicalModel.Model Crt N.poly)
    {S:Finset Surface} {H:Equation} (project:NativeWitnessBank.witnessed N S H)
    (degree:G.graphDegree=b.jet) (seeded:UsesSeed N.poly)
    (physical:b.weight≤RawPhysicalDegree.weight (131071-h) (131071-h-1) phys.raw)
    (j:Fin 2) (low:b.seed≤PadeNativeQuotient.axis N.poly j) (width:Fin 2→ℕ)
    (high:∀ k i z,((N.poly.coeff k).coeff i).degreeOf z≤width z)
    (geo:∀q∈S,Parent q) (pass:∀q∈S,TerminalBanks.Pass Crt word agreement env q) :
    (b.reserve+1)*H.natDegree≤b.shape.B+(G.graphDegree-1)*b.shape.J ∧
    (b.reserve+1)*KoalaRect.axisDegree H j≤v+b.shape.J*width j := by
  obtain ⟨l,r,lh,hr,rt,cert⟩:=PhysicalWindow.covered checked lo hi
  have s:=PhysicalWindow.rectangle_positive b v pos lh hr (fits.narrow.trans_le (Nat.sub_le_sub_left rt _))
    (fits.slope ▸ Nat.zero_lt_one) cert
  rw [←degree,fits.slope] at s
  obtain ⟨wide,nt,cut⟩:=room fits lo legal
  let U:=orient j (box b.shape.U v)
  let lower:=orient j (axis b.seed)
  have slots:U 0+U 1≤b.shape.U:=by
    dsimp only [U];rw [sum_orient];change b.shape.U-v+v≤b.shape.U;rw [Nat.sub_add_cancel vfit]
  have low' z:lower z≤PadeNativeQuotient.axis N.poly z:=by
    by_cases eq:z=j
    · subst z;simpa [lower,orient,axis] using low
    · simp [lower,orient,axis,eq]
  have cost:KoalaRect.rectDebit h b.bank.nodeRows b.bank.poleMoment U+
      (∑ W∈range (b.top h),debitAt b.shape h (b.top h) W G.graphDegree 1 b.weight (rectSlots U lower)) <
      KoalaRect.area U*K1_14.shapeSum b.shape (fun q k=>b.top h+k-q*(131071-h)):=by
    dsimp only [U,lower]
    rw [KoalaRect.rectDebit,area_orient,sum_orient,slots_orient]
    exact s
  have d:=NativeWitnessBank.rectangle pos legal Crt word N gp phys project U lower width seeded
    fits.seedChar fits.rank.moment.2 physical low' high slots wide nt fits.rank.nodes.le fits.rank.moment.1
    cost cut fits.shape fits.order geo pass
  exact ⟨d.1,by simpa [U,orient,box] using d.2 j⟩

end
end Research6969.TerminalWitness
end Z6969Source0850
