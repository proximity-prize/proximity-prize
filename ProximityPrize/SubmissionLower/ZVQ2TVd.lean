import ProximityPrize.SubmissionLower.ZAOw7gb
import ProximityPrize.SubmissionLower.Z5KYTEa
import ProximityPrize.SubmissionLower.ZDqG8Fa
import ProximityPrize.SubmissionLower.ZTOdMMe
set_option Elab.async false
section
set_option autoImplicit true
namespace qB9xHGe
set_option quotPrecheck false in
scoped notation "bound!" => of_decide_eq_true (by with_unfolding_all rfl)
set_option quotPrecheck false in
scoped notation "budget!" ns:arg ng:arg nr:arg nb:arg => {
 seed := by intro i; change Fin ns at i; fin_cases i <;> exact bound!
 global:= by intro i; change Fin ng at i; fin_cases i <;> exact bound!
 free := by intro i; change Fin nr at i; fin_cases i <;> exact bound!
 factor := by intro i; change Fin nr at i; fin_cases i <;> exact bound!
 aV:= by intro i; change Fin nb at i; fin_cases i <;> exact bound!
 base := by decide
 a8u:= by decide
 small:= by decide
 gH := by decide }
end qB9xHGe
end
section
set_option autoImplicit true
namespace qoK3iCb
open P5 (p)
open P5_7_2 (fO)
open q7F2qKe (wX weakAgreement scalarWitness aSz)
open qB9xHGe (StopRates)
abbrev Q:ℚ:=((p+1 :ℕ) :ℚ)
abbrev floorRate :ℚ:=graphRate 55
def shift (g:ℕ) :ℚ:= Q-(4*(g:ℚ)+8)*g
def num (v :ℚ) (g:ℕ) :ℚ:=v*(Q-floorRate*g)
def blend (v :ℚ) (g:ℕ) (d:ℚ) :ℚ:=num v g/(shift g-d/3)
private theorem blend_eq (v d:ℚ) {g:ℕ} (hg:0<g) :
  blend v g d=v*(graphRate g-floorRate)/(graphRate g-scalarSlope d g) := by
 have hgQ: (g:ℚ)≠0:=(Nat.cast_pos.mpr hg).ne'
 have hn:graphRate g-floorRate=(Q-floorRate*g)/g:= by
  apply (eq_div_iff hgQ).mpr
  rw [sub_mul,graphRate,div_mul_cancel₀ _ hgQ]
 have hd:graphRate g-scalarSlope d g=(shift g-d/3)/g:= by
  apply (eq_div_iff hgQ).mpr
  rw [sub_mul,graphRate,div_mul_cancel₀ _ hgQ]
  unfold scalarSlope shift
  field_simp
  ring
 rw [hn,hd,← mul_div_assoc,div_div_div_cancel_right₀ hgQ,blend,num]
private theorem affine_le {x u a b:ℚ} (hx :0≤x) (hxu:x≤u)
   (h0:a≤0) (hu:a+b*u≤0) :a+b*x≤0:= by
 rcases le_total b 0 with hb | hb
 · exact add_nonpos h0 (mul_nonpos_of_nonpos_of_nonneg hb hx)
 · exact (add_le_add (le_refl a) (mul_le_mul_of_nonneg_left hxu hb)).trans hu
private theorem frac_le_of_ends {x u a b s t:ℚ} (hx :0≤x) (hxu:x≤u)
  (hs :0<s-u/3) (ht:0<t-u/3)
  (h0:a/(s-0/3)≤b/(t-0/3)) (hu:a/(s-u/3)≤b/(t-u/3)) :
  a/(s-x/3)≤b/(t-x/3) := by
 have hsp:0<s-x/3:= by linarith only [hs,hxu]
 have htp:0<t-x/3:= by linarith only [ht,hxu]
 have hj:=(div_le_div_iff₀ (show 0<s-0/3 by linarith) (show 0<t-0/3 by linarith)).mp h0
 have hk :=(div_le_div_iff₀ hs ht).mp hu
 have hh:=affine_le (a :=a*t-b*s) (b:=(b-a)/3) hx hxu
  (by linarith only [hj]) (by linarith only [hk])
 exact (div_le_div_iff₀ hsp htp).mpr (by linarith only [hh])
abbrev aoF (uq:fO→ℕ→ℚ) (b:fO) :ℚ→ℚ:=blend (uq b 36) 36
abbrev FloorGrade (uq:fO→ℕ→ℚ) (b:fO) (g:ℕ) :Prop :=
 scalarSlope floorRate g≤floorRate∧0<shift g-floorRate/3 ∧
  blend (uq b g) g 0≤aoF uq b 0 ∧
  blend (uq b g) g floorRate≤aoF uq b floorRate
structure FloorOK (uq:fO→ℕ→ℚ) (b:fO) :Prop where
 numNonneg:0≤num (uq b 36) 36
 small1 : (1-floorRate/graphRate 1)*(1+3*262144/((weakAgreement-wX b:ℕ) :ℚ)) ≤
  aoF uq b 0
 small2 : (13+8*262144/((weakAgreement-wX b:ℕ) :ℚ))*
  (graphRate 2-floorRate)/(graphRate 2-16)≤aoF uq b 0
 cV : ∀ g:Fin 52,FloorGrade uq b (g.val+3)
private theorem grade_at {uq:fO→ℕ→ℚ} {b:fO} (hk :FloorOK uq b)
  {g:ℕ} (hg3:3≤g) (hg54 :g≤54) :FloorGrade uq b g:= by
 let i:Fin 52 :=⟨g-3,by omega⟩
 have hi:i.val+3=g:= by dsimp [i]; omega
 exact hi ▸ hk.cV i
private theorem rate_of_floor {uq:fO→ℕ→ℚ} {b:fO} {d h:ℚ}
   (hw : ∀ g:ℕ,3≤g→ g≤54→scalarWitness b g false (uq b g))
   (hc:FloorOK uq b) (hd:0≤d) (hdf :d≤floorRate)
   (hh:0≤h) (hp:aoF uq b d≤h) :aSz b d floorRate h:= by
 have h36:=(grade_at hc (g:=36) (by decide) (by decide)).2.1
 have hpeak :aoF uq b 0≤h:= by
   apply le_trans _ hp
   change num (uq b 36) 36/(shift 36-0/3) ≤
     num (uq b 36) 36/(shift 36-d/3)
   exact div_le_div_of_nonneg_left hc.numNonneg (by linarith only [h36,hdf])
     (by linarith only [hd])
 refine ⟨hd,hdf,le_rfl,hh,fun g hg hg54 _ => ?_⟩
 by_cases h1 :g=1
 · subst g
   exact Or.inr (Or.inl ⟨rfl,hc.small1.trans hpeak⟩)
 by_cases h2 :g=2
 · subst g
   exact Or.inr (Or.inr (Or.inl ⟨rfl,hc.small2.trans hpeak⟩))
 have hg3:3≤g:= by omega
 obtain ⟨hs,hden,h0,hF⟩:=grade_at hc hg3 hg54
 have hs' : scalarSlope d g≤floorRate := by
   apply le_trans _ hs
   unfold scalarSlope
   have hsd:=div_le_div_of_nonneg_right hdf
     (show 0≤3*(g:ℚ) by positivity)
   linarith only [hsd]
 have h:=frac_le_of_ends hd hdf hden h36 h0 hF
 change blend (uq b g) g d≤aoF uq b d at h
 have hv :=(blend_eq (uq b g) d hg).symm.le.trans (h.trans hp)
 refine Or.inr (Or.inr (Or.inr ⟨hg3,false,uq b g,?_,hw g hg3 hg54,?_⟩))
 · simpa [scalarSlope] using hs'
 · simpa [scalarSlope,graphRate] using hv
def fastCheck (uq:fO→ℕ→ℚ) (b:fO) (o j:ℕ) :Bool :=
 if boxDegree b o j≤floorRate then decide (aoF uq b (boxDegree b o j)≤b5T b o j)
 else ratesCheck uq b o j
theorem stop_of_checks {uq:fO→ℕ→ℚ} {b:fO} {o j:ℕ}
   (hw : ∀ g:ℕ,3≤g→ g≤54→scalarWitness b g false (uq b g))
   (hf :FloorOK uq b)
   (hr :rowCheck b o j=true) (hc:fastCheck uq b o j=true) :
   Nonempty (StopRates b o j) := by
 have h:=row_of_check hr
 apply stop_of_rate h
 by_cases hd:boxDegree b o j≤floorRate
 · rw [fastCheck,ite_eq_left hd] at hc
   rw [seedRate,max_eq_right hd]
   exact rate_of_floor hw hf h.dmNonneg hd h.hNonneg (of_decide_eq_true hc)
 · rw [fastCheck,ite_eq_right hd] at hc
   exact rate_of_checks hw h hc
end qoK3iCb
end
section
set_option autoImplicit true
namespace qoK3iCb
open P5_7_2 (fO)
open q7F2qKe (scalarWitness originCount afterFree)
open qB9xHGe (StopRates)
def BandWitness (b:fO) :Prop :=
 ∀ g:ℕ,3≤g→ g≤54→scalarWitness b g false (uq b g)
theorem witness_of_checks {b:fO}
  (h : ∀ i:Fin 52,scalarCheck b (i.val+3) (extra b (i.val+3)) (copies b (i.val+3))=true) :
  BandWitness b:= by
 intro g hg h54
 let i:Fin 52 :=⟨g-3,by omega⟩
 have hi:i.val+3=g:= by dsimp [i]; omega
 exact scalar_of_check (hi ▸ h i)
def BandStops (b:fO) :Prop :=
 ∀ o:Fin (originCount b),∀ j:Fin (afterFree b),Nonempty (StopRates b o (j.val+1))
set_option quotPrecheck false in
scoped notation "witnesses!" =>
 witness_of_checks (by intro i; fin_cases i <;> exact (by decide))
set_option quotPrecheck false in
scoped notation "floor!" => ({
 numNonneg:=of_decide_eq_true (by with_unfolding_all rfl)
 small1 :=of_decide_eq_true (by with_unfolding_all rfl)
 small2 :=of_decide_eq_true (by with_unfolding_all rfl)
 cV:= by intro i; fin_cases i <;> exact of_decide_eq_true (by with_unfolding_all rfl) } : FloorOK uq _)
set_option quotPrecheck false in
scoped notation "stops!" hw:arg hf:arg n:arg =>
 (by
   intro o j
   change Fin n at o
   change Fin 8 at j
   fin_cases o <;> fin_cases j <;>
    exact stop_of_checks hw hf (by with_unfolding_all rfl) (by with_unfolding_all rfl))
end qoK3iCb
end
section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace qQCEOid
noncomputable section
open Polynomial Matrix
open cu (Shape)
open DP (CI)
open Ge anc aeL
open scoped BigOperators Matrix Polynomial
open private dg1 dc3 from ProximityPrize.SubmissionLower.Z
private def expAt (side :Fin 2) (i r :ℕ) :Fin 2 →₀ ℕ :=
 Finsupp.single side i+Finsupp.single (CI side) r
private theorem other_ne (side :Fin 2) :CI side≠side := by
 fin_cases side <;> decide
private theorem expAt_same (side :Fin 2) (i r :ℕ) :expAt side i r side=i:= by
 simp [expAt,Finsupp.single_eq_of_ne (other_ne side).symm]
private theorem expAt_other (side :Fin 2) (i r :ℕ) :
  expAt side i r (CI side)=r := by
 simp [expAt,Finsupp.single_eq_of_ne (other_ne side)]
private theorem expAt_eq (side :Fin 2) (e :Fin 2 →₀ ℕ) :
   expAt side (e side) (e (CI side))=e := by
 ext t
 have ht:t=side∨t=CI side := by fin_cases t <;> fin_cases side <;> decide
 rcases ht with ht | ht
 · rw [ht]
   exact expAt_same side _ _
 · rw [ht]
   exact expAt_other side _ _
private def slice {F:Type} [Field F] (side :Fin 2) (U:ℕ)
   (r :Fin (U+1)) (p:i5 F) :F[X] :=
 ∑ i:Fin (U-r.val+1),C (p.coeff (expAt side i.val r.val))*Polynomial.X ^i.val
private theorem slice_reconstruct {F:Type} [Field F] (side :Fin 2) (U:ℕ)
    (p:i5 F) (hp:p.totalDegree≤U) :
    p = ∑ r :Fin (U+1),(slice side U r p).toMvPolynomial side *
      MvPolynomial.X (CI side)^r.val := by
  classical
  have hm (i r :ℕ) (f :F) :
      MvPolynomial.C f*MvPolynomial.X side^i*MvPolynomial.X (CI side)^r =
        MvPolynomial.monomial (expAt side i r) f := by
    simp only [expAt,MvPolynomial.X_pow_eq_monomial,MvPolynomial.C_apply,
      MvPolynomial.monomial_mul_monomial,zero_add,mul_one]
  simp only [slice,map_sum,map_mul,map_pow,Polynomial.toMvPolynomial_C,
    Polynomial.toMvPolynomial_X,Finset.sum_mul,hm]
  ext e
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  by_cases h:e side+e (CI side)≤U
  · let r :Fin (U+1) :=⟨e (CI side),by omega⟩
    let i:Fin (U-r.val+1) :=⟨e side,by dsimp [r]; omega⟩
    rw [Finset.sum_eq_single_of_mem r (Finset.mem_univ _),
      Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · simp [r,i,expAt_eq]
    · intro i' _ hi
      apply ite_eq_right
      intro he
      apply hi
      exact Fin.ext (by simpa [i,expAt_same] using congrArg (fun m:Fin 2 →₀ ℕ=>m side) he)
    · intro r' _ hr
      apply Finset.sum_eq_zero
      intro i' _
      apply ite_eq_right
      intro he
      apply hr
      exact Fin.ext (by
        simpa [r,expAt_other] using congrArg (fun m:Fin 2 →₀ ℕ=>m (CI side)) he)
  · have hz :p.coeff e=0:= by
      by_contra hne
      apply h
      rw [← dc3]
      exact (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hne)).trans hp
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro r _
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with he
    · simpa [he] using hz
    · rfl
private theorem dLK {F:Type} [Field F] (s :Shape) (t:Offset s)
   (a b c:F) (r :Pivot s t) (v :Lh s t) :
   (clearedEntry a b c r v).natDegree≤ s.B:= by
 simp only [clearedEntry]
 split_ifs with h
 · have hN : (C a*Polynomial.X (R:=F)).natDegree≤1 := by
     simpa using (natDegree_C_mul_X_pow_le a 1)
   have hD: (C b+C c*Polynomial.X (R:=F)).natDegree≤1 := by
     apply natDegree_add_le_of_degree_le (by simp)
     simpa using (natDegree_C_mul_X_pow_le c 1)
   refine (natDegree_mul_le_of_le
     (natDegree_mul_le_of_le (le_of_eq (natDegree_C _)) (natDegree_pow_le_of_le _ hN))
     (natDegree_pow_le_of_le _ hD)).trans ?_
   have hv :=v.1.isLt
   simp only [mul_one,zero_add]
   omega
 · simp
private theorem gr7 {F:Type} [Field F] (side :Fin 2) (U:ℕ)
  (r :Fin (U+1)) (p:i5 F) : (slice side U r p).natDegree≤U-r.val := by
 unfold slice
 refine natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
 exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp i.isLt)
private theorem read_slice {F:Type} [Field F] (s :Shape) (t:Offset s)
    (α:F) (side :Fin 2) (a b c:F) (P:Gm F) (r :Fin (s.U+1))
    (h: (seedMatrix s t (s.U-r.val) a b c).mulVec (sourceVector (t:=t) α side r P)=0)
    (row:Pivot s t) :
    (∑ v :Lh s t,clearedEntry a b c row v*slice side s.U r (input α v P))=0:= by
  classical
  ext d
  simp only [Polynomial.coeff_zero]
  by_cases hd:d<s.U-r.val+s.B+1
  · have hz :=congrFun h (row,⟨d,hd⟩)
    change (∑ v :SeedCol s t (s.U-r.val),_ *_)=0 at hz
    rw [Fintype.sum_prod_type] at hz
    simp only [finsetSum_coeff,slice,Finset.mul_sum]
    rw [← hz]
    refine Finset.sum_congr rfl fun v _=>Finset.sum_congr rfl fun i _ => ?_
    change (_ *(C ((input α v P).coeff (expAt side i.val r.val)) *
      Polynomial.X ^i.val)).coeff d =
      (clearedEntry a b c row v).coeff (d - i.val) *
        (if i.val≤d then 1 else 0)*(input α v P).coeff (expAt side i.val r.val)
    rw [← mul_assoc,coeff_mul_X_pow']
    split_ifs with hi
    · simp [coeff_mul_C,hi]
    · simp [not_le.mp hi,hi]
  · rw [finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro v _
    apply coeff_eq_zero_of_natDegree_lt
    exact lt_of_le_of_lt (natDegree_mul_le_of_le (dLK s t a b c row v)
      (gr7 side _ r (input α v P))) (by omega)
private theorem cleared_rows_zero {F:Type} [Field F] (s :Shape) (t:Offset s)
   (α:F) (side :Fin 2) (a b c:F) (P:Gm F) (hP:adk s P)
   (h : ∀ r :Fin (s.U+1),
     (seedMatrix s t (s.U-r.val) a b c).mulVec (sourceVector (t:=t) α side r P)=0)
   (row:Pivot s t) :
   (∑ v :Lh s t,(clearedEntry a b c row v).toMvPolynomial side*input α v P)=0:= by
 have hs (v :Lh s t) : (input α v P).totalDegree≤ s.U :=
   dg1 s α P hP _ _ _
 conv_lhs=>arg 2; ext v; rw [slice_reconstruct side s.U (input α v P) (hs v)]
 simp only [Finset.mul_sum,← mul_assoc,← map_mul]
 rw [Finset.sum_comm]
 have hzero (r :Fin (s.U+1)) :=
   read_slice s t α side a b c P r (h r) row
 simp_rw [← Finset.sum_mul,← map_sum,hzero,map_zero,zero_mul,Finset.sum_const_zero]
private theorem pole_row_zero {F:Type} [Field F] (s :Shape) (t:Offset s)
    (α:F) (side :Fin 2) (a b c:F) (hb:b≠0) (P:Gm F)
    (r :Pivot s t)
    (h: (∑ v :Lh s t,(clearedEntry a b c r v).toMvPolynomial side*input α v P)=0) :
    (Pa s t (residue side a b c) *ᵥ
      fun v=>algebraMap (i5 F) (kq F) (input α v P)) r=0:= by
  let ι:=algebraMap (i5 F) (kq F)
  let N :=ι (numerator side a)
  let D:=ι (denominator side b c)
  have hD:D ≠0:= by
    intro hd
    have hh:=IsFractionRing.injective (i5 F) (kq F) (hd.trans (map_zero ι).symm)
    have hzero :=congrArg (fun q:i5 F=>q.coeff 0) hh
    exact hb (by
      simpa [denominator,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,
        MvPolynomial.coeff_C_mul,MvPolynomial.coeff_zero_X] using hzero)
  have hC (f :F) :ι (MvPolynomial.C f)=algebraMap F (kq F) f :=
    (IsScalarTower.algebraMap_apply F (i5 F) (kq F) f).symm
  have hz :residue side a b c=N/D:= by
    simp [N,D,ι,residue,numerator,denominator,hC]
  have he (v :Lh s t) :
      ι ((clearedEntry a b c r v).toMvPolynomial side) =
        D^(s.B-r.1.val)*Pa s t (residue side a b c) r v := by
    simp only [clearedEntry,Pa]
    split_ifs with hp
    · have hv :=v.1.isLt
      have hn:s.B-v.1.val+(v.1.val-r.1.val)=s.B-r.1.val := by omega
      have hpow:D^(s.B-r.1.val)*(N/D)^(v.1.val-r.1.val) =
          N^(v.1.val-r.1.val)*D^(s.B-v.1.val) := by
        calc
          _=N^(v.1.val-r.1.val)*(D^(s.B-r.1.val)/D^(v.1.val-r.1.val)) := by
            rw [div_pow]
            ring
          _ = _:= by
            congr 1
            apply (div_eq_iff (pow_ne_zero _ hD)).2
            rw [← pow_add,hn]
      let χ:=((a2N v).choose r.2.val :kq F) *
        ((v.1.val-a2N v).choose (r.1.val-a2N v) :kq F)
      have hentry :ι ((C (((a2N v).choose r.2.val :F) *
          ((v.1.val-a2N v).choose (r.1.val-a2N v) :F)) *
          (C a*Polynomial.X (R:=F))^(v.1.val-r.1.val) *
          (C b+C c*Polynomial.X (R:=F))^(s.B-v.1.val)).toMvPolynomial side) =
          χ*(N^(v.1.val-r.1.val)*D^(s.B-v.1.val)) := by
        simp only [map_mul,map_add,map_pow,Polynomial.toMvPolynomial_C,
          Polynomial.toMvPolynomial_X,hC,map_natCast,N,D,numerator,denominator,χ] <;> ring
      rw [hentry,hz,← hpow]
      unfold χ
      ring
    · simp
  have hh:=congrArg ι h
  simp only [map_sum,map_mul,map_zero,he,mul_assoc,← Finset.mul_sum] at hh
  exact (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ hD)
theorem normalized {F:Type} [Field F] (s :Shape) (α:F) (side :Fin 2)
   (a b c:F) (hb:b≠0) (P:Gm F) (hP:adk s P)
   (h : ∀ (t:Offset s) (r :Fin (s.U+1)),
     (seedMatrix s t (s.U-r.val) a b c).mulVec (sourceVector (t:=t) α side r P)=0) :
   (DP.pW
     ((Polynomial.X (R:=kq F) - C (algebraMap F (kq F) α))^(s.B+s.J)) :EM (kq F)) ∣
     Ge.forward (Polynomial.X (R:=F) - C α) (C (residue side a b c)) P:= by
 let z :=residue side a b c
 have hm (t:Offset s) :Pa s t z *ᵥ
     (fun v=>algebraMap (i5 F) (kq F) (input α v P))=0:= by
   ext row
   exact pole_row_zero s t α side a b c hb P row
     (cleared_rows_zero s t α side a b c P hP (h t) row)
 have hp:=czW.proof F s α z
   (fun t q=>eKM (kq F) (Gv s t) _ _) P hP hm
 have hd:=cyV.proof F s (aVG s α z P) hp
 rw [← cyU.proof F s α z P hP] at hd
 exact exa α z (s.B+s.J) P hd
end
end qQCEOid
end
