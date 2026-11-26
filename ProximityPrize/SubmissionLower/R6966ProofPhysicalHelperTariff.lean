import ProximityPrize.SubmissionLower.R6966ProofPhysicalMonitor

set_option Elab.async false

namespace Research6966.PhysicalHelperTariff
open Polynomial Finset
open K1 (I K p)
open K1_14 (Jet L FX Seeds seedEmbedding atX graphEval liftPoly jetAt)
open K1_14_1 (PoleData CRTLift MarkResidues poleProduct seedPair)
open K1_14_3 (SeedField SeedClosure)
open PadeNativeQuotient (Native)
open scoped Polynomial Classical
noncomputable section
set_option maxHeartbeats 950000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev f:=algebraMap Seeds SeedField

def graphOf (N:Jet) : Pade.Row SeedField:=⟨(N.coeff 1).map f,-(N.coeff 0).map f⟩

private theorem equation {N:Jet} (deg:N.natDegree=1) :
    (graphOf N).polynomial=K1_14_1_4.doubleMap f N := by
  have eq:=congrArg (K1_14_1_4.doubleMap f) (eq_X_add_C_of_natDegree_le_one deg.le)
  simpa only [graphOf,Pade.Row.polynomial,map_neg,sub_neg_eq_add,K1_14_1_4.doubleMap,coe_mapRingHom,
    Polynomial.map_C,Polynomial.map_X,Polynomial.map_mul,Polynomial.map_add] using eq.symm

theorem primitive {N:Jet} (prime:Prime N) (deg:N.natDegree=1) : (graphOf N).primitive := by
  have fi:=IsFractionRing.injective Seeds SeedField
  have ir:=HelperPhysicalModel.generic_prime prime (show 0<N.natDegree from deg ▸ Nat.zero_lt_one)
  have nde:(K1_14_1_4.doubleMap f N).natDegree=1:=(natDegree_map_eq_of_injective (map_injective f fi) N).trans deg
  have prim:(graphOf N).polynomial.IsPrimitive := (equation deg) ▸ ir.isPrimitive (nde.trans_ne one_ne_zero)
  constructor
  · change (N.coeff 1).map f≠0
    apply (map_ne_zero_iff (mapRingHom f) (map_injective f fi)).mpr
    rw [←deg,coeff_natDegree];exact leadingCoeff_ne_zero.mpr prime.ne_zero
  · apply isRelPrime_iff_isCoprime.mp
    intro d da db
    apply prim d
    exact dvd_sub ((_root_.map_dvd C da).mul_right _) (_root_.map_dvd C db)

def realization {N:Jet} (prime:Prime N) (deg:N.natDegree=1) : Native (graphOf N) where
  poly:=N
  primitive:=prime.irreducible.isPrimitive (deg.trans_ne one_ne_zero)
  scalar:=1
  nonzero:=one_ne_zero
  eq:=by
    have eq:=congrArg (K1_14_1_4.doubleMap K1_14_3.seedGeneric) (eq_X_add_C_of_natDegree_le_one deg.le)
    simp only [graphOf,Pade.Row.map,Pade.Row.polynomial,K1_14_1.jetConstant,RingHom.comp_apply,map_one,one_mul,
      Polynomial.map_neg,map_neg,sub_neg_eq_add,Polynomial.map_map,K1_14_1_4.doubleMap,K1_14_3.fibreRow,coe_mapRingHom,
      Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,K1_14_3.seedGeneric] at eq ⊢
    exact eq

private theorem root_law {N:Jet} (nd:N.natDegree=1) {S:K[X]} {z:K} (root:jetAt N z S=0) :
    (N.coeff 1).eval₂ (graphEval z) (atX S)*atX S.derivative=(-N.coeff 0).eval₂ (graphEval z) (atX S) := by
  let ev:=eval₂RingHom (eval₂RingHom (graphEval z) (atX S)) (atX S.derivative)
  change ev N=0 at root
  have id:=congrArg ev (eq_X_add_C_of_natDegree_le_one nd.le)
  simp only [ev,map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X] at id
  rw [eval₂_neg];apply eq_neg_of_add_eq_zero_left
  exact id.symm.trans root

/-- Word-level price on the quadratic helper before terminal selection.
The CRT residues, physical graph weight, node count and seed degree all
refer to the same original helper and the same marked P1 words. -/
theorem price {u deleted maxHeight a} {anchor:P1.ModelAt maxHeight u deleted} {Γ T:Finset K}
    (fam:P1.FamilyAt a anchor Γ) (sub:T⊆Γ) {h:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    {Crt:CRTLift D} {N:Jet} (M:HelperPhysicalModel.Model Crt N) (prime:Prime N) (ns:N.natDegree=1)
    (quad:K1_14_2_2_2_1.jetDegree N=2) (width d:ℕ)
    (cap:∀ j i,((N.coeff j).coeff i).totalDegree≤width) (small:3*width<p)
    (physical:(131071:ℤ)+anchor.overhead≤d) (dCap:d≤131071+h) (dp:d<p) (gap:d<a)
    (nodes:∀i:I,(poleProduct D).eval (algebraMap K L (K1.node i))≠0)
    (res:∀ γ∈T,MarkResidues D (anchor.label γ) (fam.scalar γ))
    (belongs:∀ γ∈T,jetAt N (anchor.label γ) (fam.scalar γ)=0) :
    let w:=131071-h
    let Lw:=RawPhysicalDegree.weight w (w-1) M.raw
    let votes:=a-(Lw-(w-1))
    let target:=((Fintype.card I-a)*((2*d-1)*width)+(a-d))^2/(a-d)^2
    T.card*votes ≤ (3*(width+p*width))*votes+Fintype.card I*target := by
  classical
  let G:=graphOf N
  let N₀:=realization prime ns
  have gp:=primitive prime ns
  obtain ⟨data⟩:=IntegralGraphModels.exists_model M prime ns
  have graph:G.graphDegree=2 := (HelperWeightCap.native_degree N₀ gp).symm.trans quad
  let y (z:K):=atX (fam.scalar z)
  let evalAt (z:K) (P:K1_14.Equation):=P.eval₂ (graphEval (anchor.label z)) (y z)
  let bad:=T.filter (fun z=>evalAt z (N.coeff 1)=0)
  let good:=T\bad
  have good_sub:good⊆T:=sdiff_subset
  have nz (z:↥good):evalAt z.val (N.coeff 1)≠0 :=
    fun eq=>(mem_sdiff.mp z.property).2 (mem_filter.mpr ⟨good_sub z.property,eq⟩)
  have law (z:K) (mem:z∈T):evalAt z (N.coeff 1)*atX (fam.scalar z).derivative=evalAt z (-N.coeff 0) :=
    root_law ns (belongs z mem)
  have inj:Function.Injective anchor.label:=fun _ _ eq=>sub_left_injective (b:=anchor.shift) eq
  have badBudget:bad.card≤3*(width+p*width) := by
    have bound:=NativeGraphExceptional.singular_count N₀ gp (fun _=>width)
      (fun j i z=>(((N.coeff j).coeff i).degreeOf_le_totalDegree z).trans (cap j i))
      (by change (2*G.graphDegree-1)*width<p;rw [graph];exact small)
      bad anchor.label inj.injOn y (fun z mem=>(mem_filter.mp mem).2) (by
        intro z mem
        obtain ⟨orig,den⟩:=mem_filter.mp mem
        have step:=law z orig;rw [den,zero_mul] at step;exact step.symm)
    change bad.card≤(2*G.graphDegree-1)*(width+p*width) at bound
    rwa [graph] at bound
  let words (z:↥good):=liftPoly (fam.scalar z.val)
  have mark (z:↥good):=fam.mark z.val (sub (good_sub z.property))
  have deg (z:↥good):(words z).natDegree≤d := by
    change ((fam.scalar z.val).map (algebraMap K L)).natDegree≤d
    rw [natDegree_map_eq_of_injective (algebraMap K L).injective]
    rcases (mark z).scalar_degree with zero|limit
    · simp [zero]
    · change ((fam.scalar z.val).natDegree:ℤ)≤131071+anchor.overhead at limit;omega
  let n (i:I):L:=algebraMap K L (K1.node i)
  let ans (i:I):L:=algebraMap K L (anchor.word i)
  have unique:Function.Injective words:=fun x z eq=>Subtype.ext (fam.distinct (sub (good_sub x.property))
    (sub (good_sub z.property)) ((map_injective _ (algebraMap K L).injective) eq))
  have weights:=FixedNodeTariff.count (fun z:↥good=>seedPair (anchor.label z.val)) words unique n
    ((algebraMap K L).injective.comp ProximityPrize.Benchmark.IRSProfile.domain.injective) ans
    (PhysicalOriginal.integralA data.original) (PhysicalOriginal.integralB data.original)
    d width a (RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw-(131071-h-1))
    (fun i=>by rw [PhysicalOriginal.integralA,coeff_map];exact (PhysicalOriginal.coefficient_height data 1 i).trans (cap 1 i))
    (fun i=>by rw [PhysicalOriginal.integralB,coeff_neg,MvPolynomial.totalDegree_neg,coeff_map];exact (PhysicalOriginal.coefficient_height data 0 i).trans (cap 0 i))
    (fun i hi=>by
      intro zero
      have badInt:=congrArg (algebraMap L FX) zero
      simp only [map_natCast,map_zero] at badInt
      exact K1_14_2_4_2.factorial_ne_zero (hi.trans_lt dp) badInt)
    gap deg (fun z=>PhysicalOriginal.word_law data _ _ (law z (good_sub z.property))) (by
      intro z;let b:=mark z
      exact ⟨b.bad.support,b.bad.agreement,fun i mem=>(Polynomial.eval_map_apply (algebraMap K L) _).trans (congrArg _ (b.scalar_hits i mem))⟩)
    (by
      intro z
      obtain ⟨P,pn,pd,whenGood⟩:=PhysicalMonitor.witness hp hl data (anchor.label z.val) (fam.scalar z.val)
        (res z (good_sub z.property)) ((deg z).trans dCap) (nz z)
      exact ⟨P,pn,pd,fun i=>whenGood _ (nodes i)⟩)
  rw [Fintype.card_coe] at weights
  have size:good.card+bad.card=T.card:=card_sdiff_add_card_eq_card (filter_subset _ _)
  dsimp only
  rw [←size,Nat.add_mul]
  exact (Nat.add_le_add weights (Nat.mul_le_mul_right _ badBudget)).trans_eq (Nat.add_comm _ _)

end
end Research6966.PhysicalHelperTariff
