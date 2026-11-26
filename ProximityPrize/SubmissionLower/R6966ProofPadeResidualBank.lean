import ProximityPrize.SubmissionLower.R6966ProofPadePhysicalQuotient
import ProximityPrize.SubmissionLower.R6966ProofPadeCutoff

set_option Elab.async false

namespace Research6966.PadeResidualBank
open Polynomial Finset Module
open K1_14 (FX Seeds Jet L Shape)
open K1_14_1 (PoleData CRTLift centerEval jetConstant)
open K1_14_3 (SeedField SeedClosure Parent Surface fibreRow ProjectedProduct)
open PadeRank (Plane)
open KoalaRect (rectEvaluated rectComplete area rectSlots)
open scoped Polynomial
noncomputable section
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 20
set_option backward.isDefEq.respectTransparency false

private abbrev E:=SeedClosure
private abbrev f:=algebraMap SeedField E

private theorem fibre_top {Q:Jet} (qn:Q≠0) : (fibreRow Q).natDegree=Q.natDegree ∧
    (fibreRow Q).leadingCoeff.natDegree=Q.leadingCoeff.natDegree ∧ fibreRow Q≠0 := by
  let l:=K1_14_3.seedGeneric
  have inj:Function.Injective l:=f.injective.comp (IsFractionRing.injective Seeds SeedField)
  have maps:=map_injective l inj
  change (Q.map (mapRingHom l)).natDegree=_ ∧ (Q.map (mapRingHom l)).leadingCoeff.natDegree=_ ∧ _≠0
  rw [natDegree_map_eq_of_injective maps,leadingCoeff_map_of_injective maps]
  change _ ∧ (Q.leadingCoeff.map l).natDegree=_ ∧ Q.map (mapRingHom l)≠0
  rw [natDegree_map_eq_of_injective inj]
  exact ⟨rfl,rfl,(map_ne_zero_iff (mapRingHom (mapRingHom l)) (map_injective _ maps)).mpr qn⟩

private theorem total_scalar (c:E) : Pade.totalJet (jetConstant c)=0 := by
  apply Nat.eq_zero_of_le_zero
  apply (Pade.totalJet_le _ 0).mpr
  intro j i ne
  by_cases hj:j=0
  · subst j
    by_cases hi:i=0
    · omega
    · exact False.elim (ne (by simp [jetConstant,coeff_C,hi]))
  · exact False.elim (ne (by simp [jetConstant,coeff_C,hj]))

private theorem native_degrees {G:Pade.Row SeedField} (gp:G.primitive) (N:PadeNativeQuotient.Native G)
    {Q:Jet} (qn:Q≠0) (t:ℕ) :
    Pade.totalJet (fibreRow (N.poly^t*Q))=t*G.graphDegree+Pade.totalJet (fibreRow Q) ∧
    (N.poly^t*Q).natDegree=t+Q.natDegree := by
  have gpn:=(G.primitive_map f).mpr gp
  have eq:fibreRow (N.poly^t*Q)=(fibreRow N.poly)^t*fibreRow Q := by
    change K1_14_1_4.doubleMap K1_14_3.seedGeneric (N.poly^t*Q)=_
    rw [map_mul,map_pow];rfl
  have nTop:=fibre_top N.primitive.ne_zero
  have qTop:=fibre_top qn
  have td:Pade.totalJet (fibreRow N.poly)=G.graphDegree:=by
    rw [N.eq]
    change Pade.totalJet (jetConstant N.scalar*(G.map f).polynomial)=_
    rw [Pade.totalJet_mul (show (jetConstant N.scalar:Plane E)≠0 from C_ne_zero.mpr (C_ne_zero.mpr N.nonzero)) ((G.map f).polynomial_ne gpn),
      total_scalar,zero_add,(G.map f).total_polynomial gpn,Pade.Row.degree_map]
  have powd (k:ℕ):Pade.totalJet ((fibreRow N.poly)^k)=k*G.graphDegree := by
    induction k with
    | zero=>simp [Pade.totalJet,Pade.jetVars]
    | succ k ih=>rw [pow_succ,Pade.totalJet_mul (pow_ne_zero _ nTop.2.2) nTop.2.2,ih,td,Nat.succ_mul]
  have slope:N.poly.natDegree=1 := by
    rw [←nTop.1,N.eq]
    change (jetConstant N.scalar*(G.map f).polynomial).natDegree=1
    rw [natDegree_mul (show (jetConstant N.scalar:Plane E)≠0 from C_ne_zero.mpr (C_ne_zero.mpr N.nonzero))
      ((G.map f).polynomial_ne gpn),(G.map f).slope_degree gpn];simp [jetConstant]
  rw [eq,Pade.totalJet_mul (pow_ne_zero _ nTop.2.2) qTop.2.2,powd,
    natDegree_mul (pow_ne_zero _ N.primitive.ne_zero) qn,natDegree_pow,slope,mul_one]
  exact ⟨rfl,rfl⟩

private def position {h} {D:PoleData h} {Crt:CRTLift D} {G:Pade.Row SeedField}
    (M:PadeConcentration.Model Crt G) (j i:ℕ) : Jet→ₗ[FX]E :=
  (((Polynomial.lcoeff E i).comp ((Polynomial.lcoeff E[X] j).restrictScalars E)).restrictScalars FX).comp
    ((M.transform.toLinearMap.restrictScalars FX).comp PadeBankRank.fibre)

/-- The residual bank at one physical cutoff. The span is taken after
dividing the integral native rows, so different seed denominators cannot
silently add independent physical positions. -/
def residual {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (s:Shape) (W:ℕ) (U:Fin 2→ℕ)
    (N:Jet) (t:ℕ) : Submodule FX Jet :=
  Submodule.span FX {Q | ∃ P∈rectComplete Crt word s W U,centerEval P=N^t*Q}

theorem restore {h} {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L) (s:Shape)
    (W:ℕ) (U:Fin 2→ℕ) (N:Jet) (t:ℕ) (all:∀ P∈rectComplete Crt word s W U,N^t∣centerEval P) :
    (residual Crt word s W U N t).map (Algebra.lmul FX Jet (N^t))=rectEvaluated Crt word s W U := by
  unfold residual rectEvaluated
  rw [Submodule.map_span]
  congr 1
  ext P
  constructor
  · rintro ⟨Q,⟨S,hs,eq⟩,rfl⟩;exact ⟨S,hs,eq⟩
  · rintro ⟨S,hs,rfl⟩
    obtain ⟨Q,eq⟩:=all S hs
    exact ⟨Q,⟨S,hs,eq⟩,eq.symm⟩

/-- Pointwise native and physical budgets for every nonzero vector of the
residual FX-span. All bounds refer to the same t, graph and original bank. -/
theorem residual_caps {h A W r:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    {G:Pade.Row SeedField} (gp:G.primitive) (M:PadeConcentration.Model Crt G) (N:PadeNativeQuotient.Native G)
    (ys:Finset E) (v:E→E) (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ (G.map f).err v y=0)
    (many:2*G.graphDegree-1<ys.card) (b:ℕ) (capB:min s.B ((W+s.J)/(131071-h))≤b) :
    let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
    let quotSpace:=residual Crt word s W U N.poly t
    let wt:=RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw
    quotSpace.map (Algebra.lmul FX Jet (N.poly^t))=rectEvaluated Crt word s W U ∧
    ∀ Q∈quotSpace, Q≠0 →
      Q.leadingCoeff.natDegree+Q.natDegree+t*G.graphDegree≤s.B ∧
      Q.natDegree+t≤s.J ∧
      (Q.leadingCoeff.natDegree+Q.natDegree)*(131071-h)+t*wt≤W+Q.natDegree ∧
      (∀ z,PadeNativeQuotient.axis Q z+t*PadeNativeQuotient.axis N.poly z≤U z) ∧
      ∀ q∈parents,K1_14_3.OrderAt q Q (r+1-t) := by
  classical
  dsimp only
  let step:=131071-h
  let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
  let quotSpace:=residual Crt word s W U N.poly t
  let wt:=RawPhysicalDegree.weight step (step-1) M.raw
  have restored:quotSpace.map (Algebra.lmul FX Jet (N.poly^t))=rectEvaluated Crt word s W U := by
    apply restore
    intro P mem
    have gen:centerEval P∈rectEvaluated Crt word s W U:=Submodule.subset_span ⟨P,mem,rfl⟩
    have inBank:fibreRow (centerEval P)∈PadeBankRank.rows Crt word s W U:=
      Submodule.subset_span ⟨centerEval P,gen,rfl⟩
    apply N.divides
    have dv:=PadeFiltered.forced_bank_layers hp hl Crt word U fits small cut geo pass ys v
      ((G.primitive_map f).mpr gp) sheets (by rwa [Pade.Row.degree_map]) b capB inBank
    rwa [Pade.Row.degree_map] at dv
  refine ⟨restored,?_⟩
  intro Q mem nz
  have src:N.poly^t*Q∈rectEvaluated Crt word s W U:=restored ▸ (show
    (Algebra.lmul FX Jet (N.poly^t)) Q∈quotSpace.map _ from ⟨Q,mem,rfl⟩)
  have inH:fibreRow (N.poly^t*Q)∈PadeBankRank.rows Crt word s W U := Submodule.subset_span ⟨_,src,rfl⟩
  have sn:=mul_ne_zero (pow_ne_zero t N.primitive.ne_zero) nz
  have sc:=(PadeRank.mem_box (fibre_top sn).2.2).mp (PadeBankRank.rows_shape Crt word s W U inH)
  have degrees:=native_degrees gp N nz t
  rw [degrees.1,(fibre_top sn).1,degrees.2] at sc
  have qt:=fibre_top nz
  have bound:= (Pade.totalJet_le (fibreRow Q) _).mp le_rfl (fibreRow Q).natDegree (fibreRow Q).leadingCoeff.natDegree
    (by rw [coeff_natDegree,coeff_natDegree];exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr qt.2.2))
  rw [qt.1,qt.2.1] at bound
  have tb:t*G.graphDegree+Pade.totalJet (fibreRow Q)≤s.B:=Nat.le_of_lt_succ sc.1
  have sb:t+Q.natDegree≤s.J:=Nat.le_of_lt_succ sc.2
  refine ⟨(Nat.add_le_add_right bound (t*G.graphDegree)).trans (Nat.add_comm _ _ ▸ tb),
    Nat.add_comm _ _ ▸ sb,?_,?_,?_⟩
  · let j:=Q.natDegree
    let i:=Q.leadingCoeff.natDegree
    have nonzero:position M j i Q≠0 := by
      have top:=M.leading qt.2.2
      change ((M.transform (fibreRow Q)).coeff j).coeff i≠0
      rw [show j=(M.transform (fibreRow Q)).natDegree from (top.1.trans qt.1).symm,coeff_natDegree,
        show i=(M.transform (fibreRow Q)).leadingCoeff.natDegree from (top.2.1.trans qt.2.1).symm,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr top.2.2)
    have paid:step*i+(step-1)*j+t*wt≤W := by
      by_contra no
      have null:quotSpace≤(position M j i).ker := by
        apply Submodule.span_le.mpr
        rintro V ⟨S,memS,nEq⟩
        obtain ⟨R,rEq,_⟩:=M.quotient hp hl gp word U fits small cut geo pass ys v sheets many b capB memS
        by_contra out
        exact no (PadePhysicalQuotient.support hp hl Crt word M N gp t memS.1 nEq rEq j i out)
      exact nonzero (null mem)
    have off:(step-1)*j+j=step*j := by rw [←Nat.succ_mul];congr 1;dsimp [step];omega
    change (i+j)*step+t*wt≤W+j
    rw [Nat.add_mul,Nat.mul_comm i _,Nat.mul_comm j _]
    omega
  · intro z
    have cap: PadeNativeQuotient.axis (N.poly^t*Q) z≤U z :=
      (PadeNativeQuotient.axis_le ..).mpr (fun j i=>KoalaRect.rectEvaluated_axis Crt word src j i z)
    rw [PadeNativeQuotient.axis_mul (pow_ne_zero _ N.primitive.ne_zero) nz,PadeNativeQuotient.axis_pow N.primitive.ne_zero] at cap
    exact (Nat.add_comm _ _ ▸ cap)
  · intro q hq
    exact N.remaining_order gp t (r+1) rfl (TerminalBanks.retained_order Crt word (geo q hq) (pass q hq)
      fits small cut (KoalaRect.rectEvaluated_le Crt word s W U src))


/-- The free-column count times the remaining native seed slots. If a
coordinate budget is exhausted the whole residual space is zero. -/
def cost (step W B J e k t a wt:ℕ) (U width:Fin 2→ℕ) : ℕ :=
  if t*a≤B ∧ t≤J ∧ t*wt≤W ∧ ∀ z,t*width z≤U z then
    ∑ j∈range (J-t+1),
      (K1_14_4.gradeWidth step (B-t*a) (W-t*wt) j - (k-t-j)*e) *
        area (fun z=>U z-t*width z)
  else 0

theorem concentration_rank {h A W r e:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h}
    (Crt:CRTLift D) (word:K1.I→L) {s envelope:Shape} (U:Fin 2→ℕ)
    (fits:TerminalBanks.inside s envelope) (small:r+1<K1.p) (cut:W+2*h*r<s.m*A)
    {parents:Finset Surface} (geo:∀ q∈parents,Parent q)
    (pass:∀ q∈parents,TerminalBanks.Pass Crt word A envelope q)
    {prod:K1_14.Equation} (project:ProjectedProduct parents prod) (ed:e≤prod.natDegree)
    {G:Pade.Row SeedField} (gp:G.primitive) (M:PadeConcentration.Model Crt G) (N:PadeNativeQuotient.Native G)
    (ys:Finset E) (v:E→E) (sheets:∀ y∈ys,(∃ q∈parents,K1_14_3.OnSeedFibre q y (v y)) ∧ (G.map f).err v y=0)
    (many:2*G.graphDegree-1<ys.card) (b:ℕ) (capB:min s.B ((W+s.J)/(131071-h))≤b) :
    let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
    let wt:=RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw
    finrank FX (rectEvaluated Crt word s W U)≤
      cost (131071-h) W s.B s.J e (r+1) t G.graphDegree wt U (PadeNativeQuotient.axis N.poly) := by
  classical
  dsimp only
  let step:=131071-h
  let wt:=RawPhysicalDegree.weight step (step-1) M.raw
  let t:=Pade.layers G.graphDegree ys.card b s.J (r+1)
  let quotSpace:=residual Crt word s W U N.poly t
  let width:=PadeNativeQuotient.axis N.poly
  obtain ⟨restore,bounds⟩:=residual_caps hp hl Crt word U fits small cut geo pass gp M N ys v sheets many b capB
  let L:=Algebra.lmul FX Jet (N.poly^t)
  have inj:Function.Injective L:=fun _ _ eq=>mul_left_cancel₀ (pow_ne_zero t N.primitive.ne_zero) eq
  have same:finrank FX (rectEvaluated Crt word s W U)=finrank FX quotSpace := by
    rw [←restore]
    exact (Submodule.equivMapOfInjective L inj quotSpace).finrank_eq.symm
  rw [same]
  change finrank FX quotSpace≤cost step W s.B s.J e (r+1) t G.graphDegree wt U width
  unfold cost
  split
  · rename_i room
    let slots:=fun z=>U z-t*width z
    have rank:=KoalaRect.rectContact_finrank_le step (s.B-t*G.graphDegree) (s.J-t)
      (r+1-t) e (W-t*wt) slots (fun _=>0) quotSpace project.primitive.ne_zero ed (by dsimp [step];omega)
      (by intro Q mem nz;obtain ⟨a,j,_,_,_⟩:=bounds Q mem nz;exact ⟨Nat.le_sub_of_add_le a,Nat.le_sub_of_add_le j⟩)
      (by
        intro Q mem j i z
        by_cases zero:Q=0
        · simp [zero]
        have seed: PadeNativeQuotient.axis Q z+t*width z≤U z := (bounds Q mem zero).2.2.2.1 z
        exact (PadeNativeQuotient.axis_le ..).mp (by change PadeNativeQuotient.axis Q z≤U z-t*width z;omega) j i)
      (by
        intro Q mem nz
        have physical: (Q.leadingCoeff.natDegree+Q.natDegree)*step+t*wt≤W+Q.natDegree :=
          (bounds Q mem nz).2.2.1
        omega)
      (by intro Q mem nz;exact project.divides_leading Q _ nz (bounds Q mem nz).2.2.2.2)
      (fun z=>by simpa [rectSlots,area] using KoalaRect.rectSlots_antitone slots (KoalaRect.axisDegree prod) (Nat.zero_le z))
    simpa only [rectSlots,mul_zero,Nat.sub_zero,area] using rank
  · rename_i no
    have trivial:quotSpace=⊥:=le_antisymm (by
      intro Q mem
      by_contra nz
      have n:Q≠0:=nz
      obtain ⟨a,j,p,axes,_⟩:=bounds Q mem n
      have stepPositive:1≤step:=by dsimp [step];omega
      have wide:Q.natDegree≤(Q.leadingCoeff.natDegree+Q.natDegree)*step :=
        (by simpa only [mul_one] using Nat.mul_le_mul_left (Q.leadingCoeff.natDegree+Q.natDegree) stepPositive :
          Q.leadingCoeff.natDegree+Q.natDegree ≤ (Q.leadingCoeff.natDegree+Q.natDegree)*step) |>.trans' (by omega)
      change (Q.leadingCoeff.natDegree+Q.natDegree)*step+t*wt≤W+Q.natDegree at p
      exact no ⟨(Nat.le_add_left _ _).trans a,(Nat.le_add_left _ _).trans j,
        by omega,fun z=>(Nat.le_add_left _ _).trans (axes z)⟩) bot_le
    rw [trivial,finrank_bot]

end
end Research6966.PadeResidualBank
