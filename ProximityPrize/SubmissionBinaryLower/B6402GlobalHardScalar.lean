import ProximityPrize.SubmissionBinaryLower.B6402ScalarPoint
import ProximityPrize.SubmissionBinaryLower.B6402ScalarLift
import ProximityPrize.SubmissionBinaryLower.B6402ScalarCases

namespace ProximityPrize.SubmissionBinaryLower.B6402GlobalHardScalar
open Polynomial ProximityPrize.Benchmark ProximityPrize.Benchmark.Binary
open B6401Params hiding A
open B6402HybridP64 (A linePow)
open B6401ContactKerD B6401QuotInterp B6401ResLineOrd B6402PrimarySystem B6402Table4Common B6402PointSurplus
open B6402HardFactor B6402SpecialRouting B6402CleanFamily B6402ScalarCases
open B6401FactorBound (cLiftZ cLiftZ_natDegree cLiftZ_wdeg cLiftZ_sum_kerDBasisPoly evalZContact_cLiftZ irreducible_liftCRat_cLiftZ G_val std5Slot)
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000
local notation "K" => BinaryIRSProfile.Field
local notation "I" => BinaryIRSProfile.Index

theorem hard_scalar (bank : Bank) : HardList := by
  intro u F0 WF fc eq0 irr0 inv0 s0 w0 degree1 degree0 wmin wmax ratio res54 T hp ha root
  classical
  let F:=cLiftZ F0
  let fcZ (e : KerDIdx wY WF 1) := C (fc e)
  have eqF : F=∑ e,cC (fcZ e)*kerDBasisPoly e.1 := by rw [←cLiftZ_sum_kerDBasisPoly,←eq0]
  have irr : Irreducible F := B6402ScalarLift.irreducible F0 irr0
  have dr : F.natDegree=1 := (cLiftZ_natDegree _).trans s0
  have wt : wdeg wY F=WF := cLiftZ_wdeg.trans w0
  have onSeed z P (hz : P∈T) : evalContact (evalZContact F z) P=0 := by rw [evalZContact_cLiftZ]; exact root P hz
  have sdeg (i : ℕ) : (F.coeff i).natDegree=(F0.coeff i).natDegree := by
    dsimp only [F,cLiftZ]; rw [coeff_map]
    exact natDegree_map_eq_of_injective (Polynomial.map_injective _ Polynomial.C_injective) _
  have zeroheight : wYZ 0 F=0 := B6402ScalarLift.constant_height F0
  have dF : contactDeriv F=0 := by
    have d0 : wYZ 0 (contactDeriv F)≤0 := by
      rw [wYZ_le_iff]; intro k j i _
      simpa only [zero_mul,add_zero] using
        B6401Main.degZ_contactDeriv_le (natDegree_Z_le_of_wYZ zeroheight.le) k j i
    have h := B6402ScalarLift.seed_constant (contactDeriv F) d0
    change cLiftZ (evalZContact (contactDeriv F) 0)=contactDeriv F at h
    rw [B6401Main.evalZContact_contactDeriv,evalZContact_cLiftZ,inv0] at h
    simpa [cLiftZ] using h.symm
  have hYZ : wYZ 1 F≤1811 := by
    rw [eqF]; apply wYZ_sum_kerDBasisPoly_le (by decide : 0<wY) fcZ
    intro e _
    have g := B6402Moments.global_grade_le wY WF 1 (by decide) e
    unfold B6402SeedCoordinates.grade at g
    simp only [fcZ,natDegree_C,zero_add,one_mul]
    have small : WF≤6*wY := by omega
    have lim : WF/(wY-1)≤1811 := (Nat.div_le_div_right small).trans (by decide : (6*wY)/(wY-1)≤1811)
    exact (Nat.le_add_right _ _).trans (g.trans lim)
  let Loc (i : I) := localized (BinaryIRSProfile.domain i) (C (u i)) fcZ
  have nz i : Loc i≠0 := localShift_ne_zero (C (BinaryIRSProfile.domain i)) (C (u i)) fcZ (eqF ▸ irr.ne_zero)
  let k (i:I) := exactTwOrd (Loc i)
  have ord (i:I) : twOrdGE (Loc i) (k i) := twOrdGE_exactTwOrd (nz i)
  have exactOrd (i:I) : ∃ a b,a+b=k i ∧ twCoeff (Loc i) a b≠0 := exists_twCoeff_exactTwOrd (nz i)
  have ey i : linePow u (fun _=>0) 1 i=C (u i) := by simp [B6402HybridP64.linePow]
  let f : Model u (fun _=>0) 1 := {
    WF:=WF
    fc:=fcZ
    F:=F
    eq:=eqF
    fw:=wt
    qz:=hYZ
    slope:=dr
    invariant:=dF
    irreducible:=irr
    lifted:=irreducible_liftCRat_cLiftZ irr0
    degree:=by
      intro i; rw [sdeg]
      rcases i with _|(_|j)
      · exact degree0
      · change (F0.coeff 1).natDegree≤5; rw [degree1]; decide
      · rw [coeff_eq_zero_of_natDegree_lt (by omega : F0.natDegree<j+2),natDegree_zero]; omega
    quartic:=(sdeg 1).trans degree1
    lower:=by omega
    k:=k
    ord:=fun i => by rw [ey]; exact ord i
    exactOrd:=fun i => by rw [ey]; exact exactOrd i }
  let agree (P : K[X]) := Finset.univ.filter fun i : I => P.eval (BinaryIRSProfile.domain i)=u i
  have baseOrd (i : I) : twOrdGE (∑ e : KerDIdx wY WF 1,locC (fc e)*kerDLocalPoly (BinaryIRSProfile.domain i) (u i) e.1) (k i) := by
    have h := twOrdGE_evalZLocal_sum (BinaryIRSProfile.domain i) (C (u i)) fcZ 0 (ord i)
    simpa only [fcZ,eval_C] using h
  let mkD (P : K[X]) (h : P∈T) : KerD45Data := {
    W_F:=WF
    hWF_lo:=wmin
    hWF_hi:=wmax
    f_coord:=fc
    y:=u
    k:=k
    hvan:=baseOrd
    P:=P
    hPdeg:=hp P h
    Az:=agree P
    hAz_card:=ha P h
    hagree:=fun i hi => (Finset.mem_filter.mp hi).2
    hFvan:=eq0 ▸ root P h
    hf1_deg:=eq0 ▸ degree1
    hRes_ne:=eq0 ▸ res54 }
  have finish (P : K[X]) (h : P∈T)
      (routed : Assigned (mkD P h) (std5Slot (G_val WF k (agree P)))) : T.card≤100000 :=
    B6402ScalarPoint.count_at bank u f fc rfl (by change WF≤26689499; exact (show WF≤6*wY by omega).trans (by decide))
      (mkD P h) rfl rfl _ routed T hp ha (fun g hg => eq0 ▸ root g hg) onSeed
  by_cases em : T.Nonempty
  · obtain ⟨P,hP⟩ := em
    rcases t4_point_dichotomy (mkD P hP) ratio.le with ⟨p,c,b,nonzero,coprime,syz,atP⟩|routed
    · by_cases all : ∀ Q∈T,p.comp (Polynomial.X^2)*Q+b.comp (Polynomial.X^2)+Polynomial.X*c.comp (Polynomial.X^2)=0
      · have sub : T⊆{P} := by
          intro Q hQ; rw [Finset.mem_singleton]
          have hq := all Q hQ
          have hn : p.comp (Polynomial.X^2)≠0 := fun hz => nonzero ((B6402Table4Common.comp_X_sq_eq_zero_iff p).mp hz)
          have e : p.comp (Polynomial.X^2)*(Q-P)=0 := by linear_combination hq-atP
          exact sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_left hn)
        exact (Finset.card_le_card sub).trans (by simp)
      · push_neg at all
        obtain ⟨Q,hQ,escape⟩ := all
        have transfer (j : Fin 3) : p*(mkD Q hQ).Pj j+c*(mkD Q hQ).Cj j+b*(mkD Q hQ).Bj j=0 := by
          have hj := syz j
          unfold KerD45Data.Pj KerD45Data.Cj KerD45Data.Bj at hj ⊢
          dsimp only [mkD] at hj ⊢; exact hj
        exact finish Q hQ (t4_point_syzygy_witness (D:=mkD Q hQ) ⟨p,c,b,nonzero,coprime,transfer,escape⟩ ratio.le)
    · exact finish P hP routed
  · simp [Finset.not_nonempty_iff_eq_empty.mp em]

#print axioms hard_scalar
end ProximityPrize.SubmissionBinaryLower.B6402GlobalHardScalar
