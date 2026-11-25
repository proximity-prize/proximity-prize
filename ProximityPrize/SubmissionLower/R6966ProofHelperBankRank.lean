import ProximityPrize.SubmissionLower.R6966ProofHelperPhysicalModel
import ProximityPrize.SubmissionLower.R6966ProofPadeResidualBank
import ProximityPrize.SubmissionLower.R6966ProofWordSurfaceMarks

set_option Elab.async false

namespace Research6966.HelperBankRank
open Polynomial Finset Module
open K1_14 (FX L Seeds Jet Equation Shape)
open K1_14_1 (PoleData CRTLift centerEval evaluated_shape evaluated_mono)
open K1_14_2_2_2_1 (jetDegree seedDegree jetDegree_le seedDegree_le jetDegree_mul seedDegree_mul)
open KoalaRect (rectEvaluated rectComplete area)
open scoped Polynomial
noncomputable section
set_option maxSynthPendingDepth 18
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private theorem read_positions (P:Finset (ℕ×ℕ)) (V:Submodule FX Jet)
    (slots:Submodule FX Seeds) [FiniteDimensional FX slots]
    (fits:∀ Q∈V,∀ j i,(Q.coeff j).coeff i∈slots)
    (lead:∀ Q∈V,Q≠0 → (Q.natDegree,Q.leadingCoeff.natDegree)∈P) :
    finrank FX V≤P.card*finrank FX slots := by
  let coord (t:P):↥V→ₗ[FX]Seeds:=(((lcoeff Seeds t.val.2).restrictScalars FX).comp
    ((lcoeff Equation t.val.1).restrictScalars FX)).comp V.subtype
  let read:↥V→ₗ[FX](P→slots):=LinearMap.pi (fun t=>(coord t).codRestrict _ (fun Q=>fits Q.val Q.property ..))
  have inj:Function.Injective read:=by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro q h
    apply Subtype.ext
    by_contra ne
    have nz:q.val≠0:=ne
    let t:P:=⟨(q.val.natDegree,q.val.leadingCoeff.natDegree),lead q.val q.property nz⟩
    have test:=congrArg (fun v:P→slots=>(v t).val) (LinearMap.mem_ker.mp h)
    change (q.val.coeff q.val.natDegree).coeff q.val.leadingCoeff.natDegree=0 at test
    rw [coeff_natDegree,coeff_natDegree] at test
    exact (leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz)) test
  have out:=LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_pi_fintype,sum_const,card_univ,Fintype.card_coe,smul_eq_mul] at out
  exact out

def cells (s:Shape) (h W t a b wt:ℕ) : Finset (ℕ×ℕ) :=
  if t*a≤s.B ∧ t*b≤s.J ∧ t*wt≤W then
    PadeFiltered.physicalWindow (s.B-t*a) (s.J-t*b) (131071-h) (W-t*wt) else ∅

private theorem power_jet {N:Jet} (nz:N≠0) (t:ℕ) : jetDegree (N^t)=t*jetDegree N := by
  induction t with
  | zero=>simp [jetDegree]
  | succ t ih=>rw [pow_succ,jetDegree_mul (pow_ne_zero _ nz) nz,ih,Nat.succ_mul]

private theorem power_seed {N:Jet} (nz:N≠0) (t:ℕ) : seedDegree (N^t)=t*seedDegree N := by
  induction t with
  | zero=>simp [seedDegree]
  | succ t ih=>rw [pow_succ,seedDegree_mul (pow_ne_zero _ nz) nz,ih,Nat.succ_mul]

/-- Both seed geometries use the same physical position set. This theorem
also applies when the common divisor is a product of distinct primes. -/
theorem bank_rank {h W t:ℕ} (hp:0<h) (hl:h≤131070) {D:PoleData h} (Crt:CRTLift D) (word:K1.I→L)
    (s:Shape) (U:Fin 2→ℕ) {N:Jet} (M:HelperPhysicalModel.Model Crt N) (nn:N≠0)
    (force:∀ P∈rectComplete Crt word s W U,N^t∣centerEval P) :
    let wt:=RawPhysicalDegree.weight (131071-h) (131071-h-1) M.raw
    let count:=(cells s h W t (jetDegree N) N.natDegree wt).card
    finrank FX (rectEvaluated Crt word s W U)≤count*
      (if ∀ z,t*PadeNativeQuotient.axis N z≤U z then area (fun z=>U z-t*PadeNativeQuotient.axis N z) else 0) ∧
    finrank FX (rectEvaluated Crt word s W U)≤count*
      (if t*seedDegree N≤s.U then K1_14.triangle (s.U-t*seedDegree N) else 0) := by
  classical
  dsimp only
  let step:=131071-h
  let wt:=RawPhysicalDegree.weight step (step-1) M.raw
  let V:=PadeResidualBank.residual Crt word s W U N t
  let pts:=cells s h W t (jetDegree N) N.natDegree wt
  have restored:=PadeResidualBank.restore Crt word s W U N t force
  let Lmul:=Algebra.lmul FX Jet (N^t)
  have inj:Function.Injective Lmul:=fun _ _ eq=>mul_left_cancel₀ (pow_ne_zero t nn) eq
  have same:finrank FX (rectEvaluated Crt word s W U)=finrank FX V := by
    rw [←restored]
    exact (Submodule.equivMapOfInjective Lmul inj V).finrank_eq.symm
  have src {q:Jet} (mem:q∈V):N^t*q∈rectEvaluated Crt word s W U:=restored ▸ (show
    Lmul q∈V.map Lmul from ⟨q,mem,rfl⟩)
  have totals {Q:Jet} (mem:Q∈V) (nz:Q≠0):t*seedDegree N+seedDegree Q≤s.U := by
    have source:=KoalaRect.rectEvaluated_le Crt word s W U (src mem)
    have deg:seedDegree (N^t*Q)≤s.U:= (seedDegree_le ..).mpr (by
      intro j i
      by_cases z:((N^t*Q).coeff j).coeff i=0
      · simp [z]
      · exact (evaluated_shape Crt word source j i z).2.2)
    rwa [seedDegree_mul (pow_ne_zero _ nn) nz,power_seed nn] at deg
  have axes {Q:Jet} (mem:Q∈V) (nz:Q≠0) (z:Fin 2):
      t*PadeNativeQuotient.axis N z+PadeNativeQuotient.axis Q z≤U z := by
    have cap: PadeNativeQuotient.axis (N^t*Q) z≤U z:=(PadeNativeQuotient.axis_le ..).mpr
      (fun j i=>KoalaRect.rectEvaluated_axis Crt word (src mem) j i z)
    rwa [PadeNativeQuotient.axis_mul (pow_ne_zero _ nn) nz,PadeNativeQuotient.axis_pow nn] at cap
  have leading (Q:Jet) (mem:Q∈V) (nz:Q≠0):(Q.natDegree,Q.leadingCoeff.natDegree)∈pts := by
    let j:=Q.natDegree
    let i:=Q.leadingCoeff.natDegree
    have a:=KoalaRect.rectEvaluated_le Crt word s W U (src mem)
    have jc:jetDegree (N^t*Q)≤s.B:=(jetDegree_le ..).mpr (fun j i ne=>(evaluated_shape Crt word a j i ne).1)
    have sn:=mul_ne_zero (pow_ne_zero t nn) nz
    have top:((N^t*Q).coeff (N^t*Q).natDegree).coeff (N^t*Q).leadingCoeff.natDegree≠0 := by
      rw [coeff_natDegree,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr sn)
    have lim: (N^t*Q).natDegree≤s.J := (evaluated_shape Crt word a _ _ top).2.1
    rw [jetDegree_mul (pow_ne_zero _ nn) nz,power_jet nn] at jc
    rw [natDegree_mul (pow_ne_zero _ nn) nz,natDegree_pow] at lim
    have total:i+j≤jetDegree Q:=(jetDegree_le ..).mp le_rfl j i (by
      dsimp only [i,j];rw [coeff_natDegree,coeff_natDegree];exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr nz))
    have nonzero:K1_14_1_4.rawPosition Crt j i Q≠0 := by
      have top:=K1_14_1_4.specialized_leading Crt nz
      change (((K1_14_1_4.specialized Crt Q).coeff j).coeff i)≠0
      rw [show j=(K1_14_1_4.specialized Crt Q).natDegree from top.1.symm,coeff_natDegree,
        show i=(K1_14_1_4.specialized Crt Q).leadingCoeff.natDegree from top.2.1.symm,coeff_natDegree]
      exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr top.2.2)
    have paid:step*i+(step-1)*j+t*wt≤W := by
      by_contra no
      have bound:V≤(K1_14_1_4.rawPosition Crt j i).ker := by
        apply Submodule.span_le.mpr
        rintro S ⟨P,inSource,id⟩
        by_contra ne
        exact no (M.physical_support hp hl word inSource.1 id j i ne)
      exact nonzero (bound mem)
    change (j,i)∈cells s h W t (jetDegree N) N.natDegree wt
    rw [cells,ite_eq_left (by omega)]
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · change (j,i)∈PadeRank.positions (s.B-t*jetDegree N+1) (s.J-t*N.natDegree+1)
      change t*N.natDegree+j≤s.J at lim
      simp [PadeRank.positions];omega
    · exact Nat.le_sub_of_add_le paid
  rw [same]
  constructor
  · split
    · let U':=fun z=>U z-t*PadeNativeQuotient.axis N z
      have bound:=read_positions pts V (WordSurfaceInterpolation.rect (Fin 2) FX U') (by
        intro Q mem j i
        apply WordSurfaceInterpolation.in_rect.mpr
        intro z
        by_cases zero:Q=0
        · simp [zero]
        · exact (PadeNativeQuotient.axis_le ..).mp (by
            have p:=axes mem zero z
            change PadeNativeQuotient.axis Q z≤U z-t*PadeNativeQuotient.axis N z;omega) j i) leading
      rw [WordSurfaceInterpolation.rectangle_dimension,Fin.prod_univ_two] at bound
      exact bound
    · rename_i no
      have bot:V=⊥:=le_antisymm (by
        intro Q mem;by_contra n;exact no (fun z=>(Nat.le_add_right _ _).trans (axes mem n z))) bot_le
      rw [bot,finrank_bot,mul_zero]
  · split
    · have bound:=read_positions pts V (MvPolynomial.restrictTotalDegree (Fin 2) FX (s.U-t*seedDegree N)) (by
        intro Q mem j i
        apply (MvPolynomial.mem_restrictTotalDegree ..).mpr
        by_cases zero:Q=0
        · simp [zero]
        · have s:=totals mem zero
          exact (seedDegree_le ..).mp (by omega : seedDegree Q≤_ ) j i) leading
      rw [K1_14_2_1_2.seed_finrank] at bound
      exact bound
    · rename_i no
      have bot:V=⊥:=le_antisymm (by
        intro Q mem;by_contra n;exact no ((Nat.le_add_right _ _).trans (totals mem n))) bot_le
      rw [bot,finrank_bot,mul_zero]

#print axioms bank_rank
end
end Research6966.HelperBankRank
