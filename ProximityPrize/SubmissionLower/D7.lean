import ProximityPrize.SubmissionLower.ZPYznze
set_option Elab.async false
open _root_ renaming Algebra.algebraMap_self_apply → zEi, Fin.sum_univ_three → zCj, Finset → zJe, Finset.mul_sum → zxw, Finset.range → z4x, Finset.single_le_sum → zfK, Finset.sum_add_distrib → zfW, Finset.sum_congr → zUo, Finset.sum_le_sum → zQk, Finset.sum_range_succ → zpB, Ideal → znc, MvPolynomial → z3y, MvPolynomial.X → z9v, MvPolynomial.aeval → zIe, MvPolynomial.aeval_C → zXr, MvPolynomial.degreeOf_le_totalDegree → zQ3, MvPolynomial.pderiv → zWe, MvPolynomial.restrictCappedDegree → zVE, MvPolynomial.smul_eq_C_mul → zkq, MvPolynomial.totalDegree_pow → zVs, Nat.add_le_add_left → z3b, Nat.cast_add → z6H, Nat.cast_mul → z2R, Nat.cast_nonneg → zqJ, Nat.cast_sub → zjK, Nat.le_add_left → zmL, Nat.le_add_right → z8K, Nat.le_of_lt_succ → zeh, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.pos_of_ne_zero → zOl, Nat.sub_le_sub_right → zIu, Nat.succ_pos → ztH, Nat.zero_le → zD0, Polynomial.eval_map_apply → zdm, Polynomial.taylor → zcJ, Set.range → zxp, Submodule.smul_mem → zc2
set_option autoImplicit true
section
namespace baX
noncomputable section
open Polynomial Finset
open ana
def mix (b j:ℕ) (a v :ℚ) :ℚ:=(↑(b-j:ℕ) :ℚ)*v+j*a
theorem b9f {b j:ℕ} (h:j≤b) (a v :ℚ) :
  mix b j a v=(b:ℚ)*v+j*(a-v) := by
 unfold mix
 rw [zjK h]
 ring
theorem aCz {b j a v :ℕ} (h:j≤b) (hv :v≤a) :
  (MvPolynomial.cappedDegreeMixedVolume b j a v :ℚ)=mix b j a v := by
 rw [MvPolynomial.cappedDegreeMixedVolume_eq h hv,mix]
 push_cast
 rfl
end
end baX
end
section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace baX
noncomputable section
open Polynomial PolynomialDifferential
open P1 (K I node p)
open aR (af ao extend embed)
open oR (qg)
open ana
open cu (jz)
open aF0 (power BJ YM)
open scoped BigOperators
open private aQw auQ from ProximityPrize.SubmissionLower.C
private theorem gs2 {f :af 2} {S:K[X]} {d:ℕ}
   (hd:d<p) (hS:qg 1 f (extend S)) :
   zIe (Ia (extend S)) (initialJetSeparant center (bY f))≠0 ∧
   ∀ j≤d,rationalTaylorCoefficient center (bY f) (Ia (extend S)) j =
     (zcJ center (S.map jz)).coeff j:= by
 let P:=(extend S).map constants
 have hsol:differentialSpecialization (bY f) P=0:= by
   change differentialSpecialization (bY f) ((extend S).map constants)=0
   rw [bY,← map_differentialSpecialization,aQw,hS.1,Polynomial.map_zero]
 have hsf :differentialSpecialization (PolynomialDifferential.separant (flatten f) 1) (extend S)≠0:= by
   change differentialSpecialization
     (zWe (some 1) ((MvPolynomial.optionEquivRight ao (Fin 2)).symm f)) _≠0
   rw [← MvPolynomial.optionEquivRight_symm_pderiv]
   exact (aQw (zWe 1 f) _).substr hS.2
 have hsep:jetEvaluation (PolynomialDifferential.separant (bY f) (Fin.last 1))
     center (Ia (extend S))≠0:= by
   change jetEvaluation (PolynomialDifferential.separant (bY f) 1) center (Ia (extend S))≠0
   rw [Ia,← eval_differentialSpecialization,bY,← map_separant,
     ← map_differentialSpecialization,auQ]
   exact fun he=>hsf (bhW (he.trans (map_zero _).symm))
 refine ⟨by rwa [aeval_initialJetSeparant],?_⟩
 have hcharG:CharP ao p:=charP_of_injective_ringHom embed.injective p
 have :CharP Tv p:=charP_of_injective_ringHom constants.injective p
 have hP:P=S.map jz := by
   change (extend S).map constants= _
   rw [Polynomial.map_map]
   rfl
 intro j hj
 rw [← hP]
 refine rationalTaylorCoefficient_eq_solution center (bY f) P hsol hsep j (fun i hi ht => ?_)
 rw [Nat.choose_one_right]
 intro hz
 exact (not_le_of_gt ((ht.trans hj).trans_lt hd))
   (Nat.le_of_dvd (by omega :0< i) ((CharP.cast_eq_zero_iff Tv p i).mp hz))
private theorem gqU (f :af 2) {B J t:ℕ} (hJ:0<J)
   (hB:f.totalDegree≤B) (hj:f.degreeOf 1≤J) (j:Fin (t+1)) :
   commonTaylorNumerator center (bY f) (power t) j ∈
     zVE (Fin 2) Tv 1 (BJ t B) (YM t B J) := by
 let Q:=bY f
 let N :=commonTaylorNumerator center Q (power t) j
 have hτ:TaylorExponentSufficient 1 (t+1) (power t) :=
   taylorExponentSufficient_firstOrder_tight t
 have htot:N.totalDegree≤BJ t B :=
   (totalDegree_commonTaylorNumerator_le center Q (hτ j)).trans
     (z3b (zBI _ (zIu ((adr f).trans hB) 1)) 1)
 exact aVQ _ htot (le_min
   ((zQ3 _ _).trans htot)
   ((degreeOf_commonTaylorNumerator_firstOrder_le center Q J (t+1) (power t) hτ hJ
     ((aCA f).trans hj) j).trans (z3b (zeh j.isLt) _)))
private theorem gqS (f :af 2) {B J t:ℕ}
    (hB:f.totalDegree≤B) (hj:f.degreeOf 1≤J) :
    initialJetSeparant center (bY f)^power t ∈
      zVE (Fin 2) Tv 1 (BJ t B) (YM t B J) := by
  let Q:=bY f
  let D:=initialJetSeparant center Q^power t
  have hD₀:D.totalDegree≤BJ t B :=
    (zVs _ _).trans ((zBI _
      ((totalDegree_initialJetSeparant_le center Q).trans
        (zIu ((adr f).trans hB) 1))).trans (zmL _ _))
  have hD₁:D.degreeOf 1≤power t*(J-1) :=
    (MvPolynomial.degreeOf_pow_le _ _ _).trans (zBI _
      ((degreeOf_initialJetSeparant_le center Q).trans
        (zIu ((aCA f).trans hj) 1)))
  exact aVQ D hD₀ (le_min
    ((zQ3 _ _).trans hD₀) (hD₁.trans (z8K _ _)))
theorem cpz (f :af 2) {d t B J:ℕ} (hd:d<p) (ht:t≤d)
    (hJ:0<J) (hB:f.totalDegree≤B) (hj:f.degreeOf 1≤J)
    (sites :zJe I) (hs :d≤ sites.card+t) (w:I→K) (i:I) :
    ∃ cut:z3y (Fin 2) Tv,
      cut∈zVE (Fin 2) Tv 1 (BJ t B) (YM t B J) ∧
      ∀ S:K[X],S.natDegree≤d→qg 1 f (extend S) →
        (∀ j∈sites,S.eval (node j)=w j) →
        (zIe (Ia (extend S)) cut=0↔S.eval (node i)=w i) := by
  classical
  obtain ⟨c,a,ha⟩:=axI.bHU sites d t hs w (node i)
  let Q:=bY f
  let D:=initialJetSeparant center Q^power t
  let N (j:Fin (t+1)) :=commonTaylorNumerator center Q (power t) j
  let cut:=MvPolynomial.C (c - jz (w i))*D + ∑ j,MvPolynomial.C (a j)*N j
  have hτ:TaylorExponentSufficient 1 (t+1) (power t) :=
    taylorExponentSufficient_firstOrder_tight t
  refine ⟨cut,?_,?_⟩
  · dsimp only [cut]
    apply Submodule.add_mem
    · rw [← zkq]
      exact zc2 _ _ (gqS f hB hj)
    · apply Submodule.sum_mem
      intro j _
      rw [← zkq]
      exact zc2 _ _ (gqU f hJ hB hj j)
  · intro S hS hreg hnodes
    obtain ⟨hsep,hcoef⟩:=gs2 hd hreg
    have hval :=ha (S.map jz) (Polynomial.natDegree_map_le.trans hS)
      (fun j hj=> by rw [zdm,hnodes j hj])
    change (S.map jz).eval (jz (node i))= _ at hval
    rw [zdm] at hval
    let x :=Ia (extend S)
    have he (j:Fin (t+1)) :zIe x (N j) =
        zIe x D *(zcJ center (S.map jz)).coeff j:= by
      dsimp only [N,D]
      rw [aeval_commonTaylorNumerator center Q x (hτ j) hsep,map_pow,
        hcoef _ ((zeh j.isLt).trans ht)]
    have hdne :zIe x D ≠0:= by
      dsimp only [D]
      rw [map_pow]
      exact pow_ne_zero _ hsep
    have hc:zIe x cut =
        zIe x D *(jz (S.eval (node i)) - jz (w i)) := by
      dsimp only [cut]
      rw [hval,map_add,map_mul,map_sum,zXr,zEi,
        mul_sub,mul_add,zxw]
      simp only [map_mul,zXr,zEi,he]
      have hsum: (∑ j:Fin (t+1),a j *
          (zIe x D *(zcJ center (S.map jz)).coeff j)) =
          ∑ j:Fin (t+1),zIe x D *
            (a j*(zcJ center (S.map jz)).coeff j) :=
        zUo rfl fun _ _=> by ring
      rw [hsum]
      ring
    change zIe x cut=0↔_
    rw [hc,mul_eq_zero,or_iff_right hdne,sub_eq_zero,jz.injective.eq_iff]
end
end baX
end
section
namespace TD
noncomputable section
open Polynomial
open P1 (gJ p)
open Dt (Ls stages terminal)
open cu (Shape Jet)
open gT (Ambient)
open pI (xN NO aaS mass)
open Ty (aoD aea aaW aof)
open scoped BigOperators Classical
abbrev GM:=Fin 4→ℚ
def J2 (S:zJe (znc Ambient)) :GM:= fun k=>mass S k
def FP (a c:GM) :ℚ := ∑ k,a k*c k
def bCb (a c:GM) :GM:= fun k=>min (a k) (c k)
def aa3 (s t:Shape) :ℕ:=min s.U t.U
def ad3 (s t:Shape) :ℕ:=min s.B t.B
def aps (s t:Shape) (x z r m:ℕ) (square :Bool) (k :Fin 4) :ℚ :=
  let n:=m+1 - r
  let d:=if square || (k == 3) then n^2 else n
  (aaW x z k :ℚ)/aof r k +
    (aoD (aea s x z) (aea t x z) k :ℚ)/d
def alN (s t:Shape) (r m:ℕ) (square :Bool) (k :Fin 4) :ℚ :=
 let xs :=[0,aa3 s t]
 let zMax :=ad3 s t
 let zs :=[0,zMax,min zMax (s.B-s.J),min zMax (t.B-t.J)]
 (xs.flatMap fun x=>zs.map fun z=>aps s t x z r m square k).foldl max 0
def bf7 (s t:Shape) (dI:ℕ) (square :Bool) :GM :=
  fun k =>
    let m:=dI+1
    (List.range m).foldl
      (fun a r=>min a (alN s t (r+1) m square k))
      (alN s t 1 m square k)
def aSt:Prop :=
  ∀ (s t:Shape) (r :ℕ) (square :Bool) (P Q:Jet),
    0< r→ r<p→s.B<p→t.B<p→s.U<p→t.U<p →
    s.J≤ s.B→t.J≤t.B→P≠0→Q≠0 →
    qQ.oU P s→qQ.oU Q t→qQ.aeH P Q →
    ∀ (A:NO P s) (B:NO Q t) (S:zJe (znc Ambient)),
    (square=true → ∀ I∈S,pI.dual I) →
    (∀ I∈S,xN I∧aFX.aTw P Q I ∧
      ¬ aaS A.equation I ∧ ¬ aaS B.equation I ∧
      pI.O9 I P (r+1)∧pI.O9 I Q (r+1)) →
    ∀ k,J2 S k≤bf7 s t r square k
def nV (b:gJ) (i:ℕ) :Ls :=
 ((stages b)[i]?).getD ⟨0,terminal b,terminal b⟩
def Fo (b:gJ) :=(stages b).length - 1
def RU:gJ→List ℕ
  | .aat | .aaF | .kP | .kQ=>List.range' 1 11
  | .aaT=>List.range' 1 9 ++ [11]
  | .kV | .kY | .k6 | .l6 | .lR | .l7 |
    .l8 | .l9 | .mj | .m7 | .nT | .n6 | .pA | .qk |
    .q8 | .rq | .rC | .rN | .rQ | .sY | .s4 | .s5 |
    .tI | .s6 | .tT | .s7 | .sJ | .tv | .uH=>List.range' 1 8
  | _=>[]
def Wx :gJ→ℕ
 | .lZ=>2
 | .om=>1
 | _=>0
def auN (s :Shape) :Fin 3→ℕ := ![s.B,s.J,s.U]
def arC (s :Shape) (k :Fin 4) :Fin 3→ℕ :=
 ![![s.J,s.B-s.J,0],![0,s.U,s.J],![s.U,0,s.B],![0,0,s.U]] k
def aIe (cap old:Fin 3→ℕ) (s :Shape) (k :Fin 4) :ℕ :=
 ∑ j,(max (old j) (arC s k j) - old j)*cap j
def azi (b:gJ) (k :Fin 4) :
    List ℕ→(Fin 3→ℕ)→(Fin 3→ℕ)→ℕ
  | [],cap,old =>
    aIe cap old (nV b 0).moving.shape k +
      (![cap 0,cap 2,2*cap 0*cap 2,cap 2*cap 2] :Fin 4→ℕ) k
  | i :: is,cap,old =>
    let s :=nV b i
    let c:=s.free.shape
    aIe cap old c k+azi b k is
      (fun j=>min (cap j) (auN c j/(s.dI+1)))
      (fun j=>max (old j) (arC c k j))
def BC (b:gJ) (k :Fin 4) :ℕ :=
  let s :=nV b 0
  if (RU b).isEmpty then
    (alN s.free.shape s.moving.shape 1 1 false k).floor.toNat
  else azi b k (RU b) (auN s.free.shape) (fun _=>0)
def aE6 (b:gJ) (i:ℕ) (square :Bool) :GM :=
 let s :=nV b i
 bf7 s.free.shape s.moving.shape s.dI square
def V8 (b:gJ) :ℕ→GM
 | 0=> fun k=>BC b k
 | i+1=>bCb (V8 b i) (aE6 b (i+1) (decide (Wx b≤ i+1)))
def a3D (s :Ls) :Shape :=
 let a :=s.free.shape
 let b:=s.moving.shape
 let j:=max a.J b.J
 ⟨0,max (a.B-a.J) (b.B-b.J)+j,j,max a.U b.U⟩
def aHp (b:gJ) (i:ℕ) :Shape :=
 if i<Fo b then a3D (nV b (i+1)) else (terminal b).shape
def running (v :ℕ→GM) :ℕ→GM
 | 0=> fun _=>0
 | i+1=> fun k=>max (running v i k) (v i k)
def XM (n:ℕ) (v :ℕ→GM) (hist:ℕ→GM) :ℚ :=
 ∑ i∈z4x n,FP (fun k=>running v (i+1) k - running v i k) (hist i)
structure aBh (B J:ℕ) :Prop where
 bmin:2≤B
 jpos :0<J
 jb:J≤B
 small:B<p
end
end TD
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
namespace TD
noncomputable section
open gT (Ambient)
open pI (mass)
open scoped BigOperators Classical
theorem bfw {S T:zJe (znc Ambient)} (h:S⊆T) (k :Fin 4) :
  J2 S k≤J2 T k := by
 exact (Nat.cast_le (α:=ℚ)).mpr (pI.a5I h k)
theorem cZV (S:zJe (znc Ambient)) (k :Fin 4) :0≤J2 S k :=
 zqJ _
theorem ezI {S T:zJe (znc Ambient)} (h:T⊆S) (k :Fin 4) :
  J2 (S \ T) k+J2 T k=J2 S k := by
 unfold J2
 exact_mod_cast (Finset.sum_sdiff h :
  mass (S \ T) k+mass T k=mass S k)
theorem dYm {v c:GM} (hv : ∀ k,0≤v k) (hc : ∀ k,0≤ c k) :
  0≤FP v c :=
 Finset.sum_nonneg fun k _=>mul_nonneg (hv k) (hc k)
theorem a3x {v c d:GM} (hv : ∀ k,0≤v k) (h : ∀ k,c k≤d k) :
  FP v c≤FP v d :=
 zQk fun k _=>mul_le_mul_of_nonneg_left (h k) (hv k)
theorem dYl {v w c:GM} (hc : ∀ k,0≤ c k) (h : ∀ k,v k≤w k) :
  FP v c≤FP w c :=
 zQk fun k _=>mul_le_mul_of_nonneg_right (h k) (hc k)
theorem cK6 (a h:ℚ) (v w x :GM) :
  a*FP v x+h*FP w x=FP (fun k=>a*v k+h*w k) x := by
 simp only [FP,zxw,← zfW]
 apply zUo rfl
 intro k _
 ring
private theorem dbX (v :ℕ→GM) (i:ℕ) (k :Fin 4) :
   0≤ running v i k := by
 induction i with
 | zero=>exact le_rfl
 | succ i ih=>exact ih.trans (le_max_left _ _)
private theorem eqA (v :ℕ→GM) (i:ℕ) (k :Fin 4) :
  0≤ running v (i+1) k - running v i k :=
 sub_nonneg.mpr (le_max_left _ _)
private theorem dbY (v :ℕ→GM) (i:ℕ) (c:GM) :
   FP (running v (i+1)) c=FP (running v i) c +
     FP (fun k=>running v (i+1) k - running v i k) c:= by
 unfold FP
 rw [← zfW]
 apply zUo rfl
 intro k _
 ring
private theorem eKP (v :ℕ→GM) (hist:ℕ→GM) (i:ℕ)
    {S T U:zJe (znc Ambient)} (hT:T⊆S) (hU:U⊆S \ T)
    (hcap : ∀ k,J2 S k≤hist i k) :
    FP (v i) (J2 U)+FP (running v (i+1)) (J2 T) ≤
      FP (running v i) (J2 S) +
        FP (fun k=>running v (i+1) k - running v i k) (hist i) := by
  have hleft:FP (v i) (J2 U)≤FP (running v (i+1)) (J2 (S \ T)) :=
    (dYl (cZV U) (fun k=>le_max_right _ _)).trans
      (a3x (dbX v (i+1)) (bfw hU))
  have hsplit :
      FP (running v (i+1)) (J2 (S \ T))+FP (running v (i+1)) (J2 T) =
        FP (running v (i+1)) (J2 S) := by
    unfold FP
    rw [← zfW]
    exact zUo rfl fun k _=> by rw [← mul_add,ezI hT]
  calc
    _≤_:=add_le_add hleft le_rfl
    _ = _:=hsplit
    _ = _:=dbY v i _
    _≤_:=add_le_add le_rfl (a3x (eqA v i) hcap)
theorem bBx (n:ℕ) (v hist:ℕ→GM)
    (QV Hj:ℕ→zJe (znc Ambient))
    (next : ∀ i<n,QV (i+1)⊆QV i)
    (fail : ∀ i<n,Hj i⊆QV i \ QV (i+1))
    (cap : ∀ i<n,∀ k,J2 (QV i) k≤hist i k) :
    (∑ i∈z4x n,FP (v i) (J2 (Hj i)))≤XM n v hist:= by
  have h :
      (∑ i∈z4x n,FP (v i) (J2 (Hj i))) +
        FP (running v n) (J2 (QV n))≤XM n v hist:= by
    induction n with
    | zero=>simp [running,FP,XM]
    | succ n ih =>
      have old:=ih (fun i hi=>next i (by omega)) (fun i hi=>fail i (by omega))
        (fun i hi=>cap i (by omega))
      have step:=eKP v hist n (next n (by omega)) (fail n (by omega)) (cap n (by omega))
      unfold XM at old ⊢
      rw [zpB,zpB]
      linarith
  exact (le_add_of_nonneg_right (dYm (dbX v n) (cZV _))).trans h
theorem cSF (n:ℕ) (v :ℕ→GM) (c:GM) :
   XM n v (fun _=>c)=FP (running v n) c:= by
 induction n with
 | zero=>simp [ XM,running,FP]
 | succ n ih =>
   rw [ XM,zpB,← XM,ih,dbY]
end
end TD
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000
namespace aZC
noncomputable section
open P1 (p)
open TD (J2 aps)
open cu (Jet Shape)
open gT (Ambient)
open pI Ty Polynomial
open scoped Classical
open private bWa from ProximityPrize.SubmissionLower.CO
open private aUy from ProximityPrize.SubmissionLower.AH
private theorem bca :Ty.c3 :=
 aqb.of_children cy1.proof baz.proof
private theorem sections :Ty.c5 :=
 akQ.of_children cy2.proof cy3.proof
  cy4.proof bRJ.proof bRK.proof
private theorem dci {d m c:ℕ} (hd:0<d) (h:d*m≤ c) :
  (m:ℚ)≤(c:ℚ)/(d:ℚ) := by
 apply (le_div_iff₀ (by exact_mod_cast hd: (0:ℚ)<(d:ℚ))).mpr
 rw [mul_comm]
 exact_mod_cast h
private theorem eJM {s t:Shape} {P Q:Jet} {A:NO P s} {B:NO Q t}
    (G:bR0.bTx A B) (S:zJe (znc Ambient)) (square :Bool)
    (m r :ℕ) (k :Fin 4) (hr :0< r) (hrm:r≤ m)
    (hx :gY G.iy<p) (hz :G.iy.natDegree<p)
    (hdual:square=true → ∀ I∈S,dual I)
    (hpass : ∀ I∈S,xN I∧aFX.aTw P Q I ∧
      ¬ aaS A.equation I ∧ ¬ aaS B.equation I∧O9 I P m∧O9 I Q m) :
    J2 S k≤aps s t (gY G.iy) G.iy.natDegree r m square k := by
  let x :=gY G.iy
  let z :=G.iy.natDegree
  let n:=m+1 - r
  let d:=if square || (k == 3) then n^2 else n
  have hn:0<n:= by dsimp [n]; omega
  have hd:0<d:= by
    unfold d
    split
    · exact Nat.pow_pos hn
    · exact hn
  have hg:0<aof r k := by
    fin_cases k <;> first | exact hr | exact Nat.pow_pos hr
  have hh:aof r k*mass (S.filter (aYS G.iy r)) k≤aaW x z k := by
    apply aFX.cUH aFY.proof sections G.iy P Q
      _ r G.ordinary_ne hz hr
    · refine ⟨Gw A.equation*G.left,G.left_factor.trans ?_⟩
      ring
    · refine ⟨Gw B.equation*G.right,G.right_factor.trans ?_⟩
      ring
    intro I hI
    obtain ⟨hm,hf⟩:=Finset.mem_filter.mp hI
    exact ⟨(hpass I hm).1,(hpass I hm).2.1,hf⟩
  have hl:d*mass (S.filter fun I => ¬ aYS G.iy r I) k ≤
      aoD (aea s x z) (aea t x z) k := by
    apply sections G.left G.right _ _ _ k d G.left_ne G.right_ne G.relativelyPrime
      (min_le_right _ _) (min_le_right _ _) G.left_caps G.right_caps hd
    intro I hI
    obtain ⟨hm,hf⟩:=Finset.mem_filter.mp hI
    obtain ⟨ha,_,hA,hB,hP,hQ⟩:=hpass I hm
    rw [G.left_factor] at hP
    rw [G.right_factor] at hQ
    have hlP:=bca G.iy G.left I m r G.ordinary_ne hx hz ha hr hrm hf
      (bWa ha.prime _ _ m hA hP)
    have hlQ:=bca G.iy G.right I m r G.ordinary_ne hx hz ha hr hrm hf
      (bWa ha.prime _ _ m hB hQ)
    have hlen:=aFY.proof G.left G.right I ha n hn hlP hlQ
    refine ⟨ha,fun hdegree => ?_⟩
    by_cases hIdual:dual I
    · rw [ite_eq_left hIdual] at hlen
      apply le_trans _ hlen
      apply Nat.cast_le.mpr
      unfold d
      split
      · exact le_rfl
      · simpa only [pow_two,mul_one] using zBI n (show 1≤n by omega)
    · have hs :square=false :=Bool.eq_false_iff.mpr fun he=>hIdual (hdual he I hm)
      have hk :k≠3:= fun he=>hIdual (show 0<pN I 3 by
        rw [← he]
        exact zOl hdegree)
      simpa [d,hs,hk,hIdual] using hlen
  have hadd:mass (S.filter (aYS G.iy r)) k +
      mass (S.filter fun I => ¬ aYS G.iy r I) k=mass S k :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  change (mass S k :ℚ)≤(aaW x z k :ℚ)/aof r k +
    (aoD (aea s x z) (aea t x z) k :ℚ)/d
  rw [← hadd,z6H]
  exact add_le_add (dci hg hh) (dci hd hl)
theorem eJN (s t:Shape) (m:ℕ) (square :Bool) (P Q:Jet)
  (hsB:s.B<p) (hsU:s.U<p) (hP:P≠0) (hQ:Q≠0)
  (hPs :oU P s) (hQt:oU Q t) (hno:qQ.aeH P Q)
  (A:NO P s) (B:NO Q t) (S:zJe (znc Ambient))
  (hdual:square=true → ∀ I∈S,dual I)
  (hpass : ∀ I∈S,xN I∧aFX.aTw P Q I ∧
    ¬ aaS A.equation I ∧ ¬ aaS B.equation I∧O9 I P m∧O9 I Q m) :
  ∃ x≤TD.aa3 s t,∃ z≤TD.ad3 s t,
    ∀ r,0< r→ r≤ m → ∀ k,J2 S k≤aps s t x z r m square k := by
 obtain ⟨G⟩:=bR0.gp3 A B hP hQ hPs hQt hno
 obtain ⟨hU,hB,_⟩:=aUy hQ G.ordinary_ne hQt G.right_factor
 refine ⟨gY G.iy,le_min G.acI hU,G.iy.natDegree,
  le_min G.ordinate_le hB,?_⟩
 intro r hr hrm k
 exact eJM G S square m r k hr hrm (G.acI.trans_lt hsU)
  (G.ordinate_le.trans_lt hsB) hdual hpass
end
end aZC
end
section
set_option maxHeartbeats 1000000
namespace aZC
noncomputable section
open TD (aa3 ad3 alN aps)
open cu (Shape)
open Ty (aaW aof aoD aea)
private theorem bbN {F:ℕ→ℚ} {l x u:ℕ} {a b c M:ℚ}
   (hl:l≤x) (hu:x≤u) (ha :0≤a)
   (hF : ∀ y,l≤y→y≤u→F y=a*(y :ℚ)^2+b*(y :ℚ)+c)
   (hL:F l≤M) (hU:F u≤M) :F x≤M:= by
 have hl' : (l:ℚ)≤x := by exact_mod_cast hl
 have hu' : (x :ℚ)≤u:= by exact_mod_cast hu
 have hchord:=mul_nonneg ha (mul_nonneg (sub_nonneg.mpr hl') (sub_nonneg.mpr hu'))
 rw [hF x hl hu]
 rw [hF l le_rfl (hl.trans hu)] at hL
 rw [hF u (hl.trans hu) le_rfl] at hU
 by_cases hs :0≤a*((l:ℚ)+u)+b
 · have h:=mul_nonneg hs (sub_nonneg.mpr hu')
   linarith only [hU,hchord,h]
 · have h:=mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hl')
   linarith only [hL,hchord,h]
private def XC (s t:Shape) (a b:ℚ) (k :Fin 4) (x z :ℕ) :ℚ :=
 a*(aaW x z k :ℚ)+b*(aoD (aea s x z) (aea t x z) k :ℚ)
private theorem cEq (B C J E :ℕ) (hJ:J≤B) :
  ((B*E+C*J-J*E :ℕ) :ℚ) =
    (B:ℚ)*E+(C:ℚ)*J-(J:ℚ)*E := by
 have h:=(ztf E hJ).trans (z8K (B*E) (C*J))
 simp only [zjK h,z6H,z2R]
private theorem goV (s t:Shape) {a b M:ℚ} (hb:0≤b)
   {x z :ℕ} (hz :z≤ad3 s t) (hsJ:s.J≤ s.B) (htJ:t.J≤t.B)
   (h0:XC s t a b 0 0 0≤M)
   (hZ:XC s t a b 0 0 (ad3 s t)≤M)
   (hC:XC s t a b 0 0 (min (s.B-s.J) (t.B-t.J))≤M) :
   XC s t a b 0 x z≤M:= by
 let C:=min (s.B-s.J) (t.B-t.J)
 let limit :=ad3 s t
 let F (y :ℕ) :=XC s t a b 0 0 y
 have hcS:C≤ s.B-s.J:=min_le_left _ _
 have hcT:C≤t.B-t.J:=min_le_right _ _
 change F z≤M
 by_cases hlow:z≤C
 · refine bbN (F:=F) (l:=0) (u:=C) (a :=0)
     (b:=a - b*((s.J:ℚ)+t.J))
     (c:=b*((s.B:ℚ)*t.J+(t.B:ℚ)*s.J-(s.J:ℚ)*t.J))
     (zD0 z) hlow le_rfl ?_ h0 hC
   intro y _ hy
   have hsj:s.J≤ s.B-y := by omega
   have htj:t.J≤t.B-y := by omega
   change a*(y :ℚ)+b*(((s.B-y)*min t.J (t.B-y) +
     (t.B-y)*min s.J (s.B-y) - min s.J (s.B-y)*min t.J (t.B-y) :ℕ) :ℚ)= _
   rw [min_eq_left hsj,min_eq_left htj,cEq _ _ _ _ hsj,
     zjK (show y≤ s.B by omega),zjK (show y≤t.B by omega)]
   ring
 · refine bbN (F:=F) (l:=C) (u:=limit) (a :=b)
     (b:=a - b*((s.B:ℚ)+t.B)) (c:=b*(s.B:ℚ)*t.B)
     (by omega) hz hb ?_ hC hZ
   intro y hy hyZ
   have hyS:=hyZ.trans (min_le_left s.B t.B)
   have hyT:=hyZ.trans (min_le_right s.B t.B)
   change a*(y :ℚ)+b*(((s.B-y)*min t.J (t.B-y) +
     (t.B-y)*min s.J (s.B-y) - min s.J (s.B-y)*min t.J (t.B-y) :ℕ) :ℚ)= _
   rw [cEq _ _ _ _ (min_le_right _ _)]
   rcases min_choice (s.B-s.J) (t.B-t.J) with hc | hc
   · have hj:s.B-y≤ s.J:= by change min (s.B-s.J) (t.B-t.J)≤y at hy; omega
     rw [min_eq_right hj,Nat.cast_sub hyS,Nat.cast_sub hyT]
     ring
   · have hj:t.B-y≤t.J:= by change min (s.B-s.J) (t.B-t.J)≤y at hy; omega
     rw [min_eq_right hj,Nat.cast_sub hyS,Nat.cast_sub hyT]
     ring
private theorem eHW (s t:Shape) {a b M:ℚ} (hb:0≤b)
  {x z :ℕ} (hx :x≤aa3 s t) (hsJ:s.J≤ s.B) (htJ:t.J≤t.B)
  (h0:XC s t a b 1 0 0≤M)
  (hX:XC s t a b 1 (aa3 s t) 0≤M) :
  XC s t a b 1 x z≤M:= by
 have hmono:XC s t a b 1 x z≤XC s t a b 1 x 0:= by
  change a*(x :ℚ)+b*(((s.U-x)*min t.J (t.B-z) +
    (t.U-x)*min s.J (s.B-z) :ℕ) :ℚ)≤a*(x :ℚ) +
    b*(((s.U-x)*min t.J (t.B-0)+(t.U-x)*min s.J (s.B-0) :ℕ) :ℚ)
  simp only [Nat.sub_zero,min_eq_left hsJ,min_eq_left htJ]
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ hb)
  exact_mod_cast Nat.add_le_add (zBI _ (min_le_left _ _))
    (zBI _ (min_le_left _ _))
 apply hmono.trans
 refine bbN (F:= fun y=>XC s t a b 1 y 0)
  (l:=0) (u:=aa3 s t) (a :=0)
  (b:=a - b*((t.J:ℚ)+s.J)) (c:=b*((s.U:ℚ)*t.J+(t.U:ℚ)*s.J))
  (zD0 x) hx le_rfl ?_ h0 hX
 intro y _ hy
 change a*(y :ℚ)+b*(((s.U-y)*min t.J (t.B-0) +
  (t.U-y)*min s.J (s.B-0) :ℕ) :ℚ)= _
 simp only [Nat.sub_zero,min_eq_left hsJ,min_eq_left htJ,z6H,z2R,
  zjK (hy.trans (min_le_left s.U t.U)),
  zjK (hy.trans (min_le_right s.U t.U))]
 ring
private theorem eAR (s t:Shape) {a b M:ℚ} {x z :ℕ}
    (hx :x≤aa3 s t) (hz :z≤ad3 s t)
    (hC : ∀ y,(y=0∨y=aa3 s t) → ∀ w,
      (w=0∨w=ad3 s t)→XC s t a b 2 y w≤M) :
    XC s t a b 2 x z≤M:= by
  have hform (y w:ℕ) (hy :y≤aa3 s t) (hw:w≤ad3 s t) :
      XC s t a b 2 y w =
        a*(2*(y :ℚ)*(w:ℚ)) +
          b*(((s.U:ℚ)-y)*((t.B:ℚ)-w)+((t.U:ℚ)-y)*((s.B:ℚ)-w)) := by
    change a*((2*y*w:ℕ) :ℚ) +
      b*(((s.U-y)*(t.B-w)+(t.U-y)*(s.B-w) :ℕ) :ℚ)= _
    simp only [z2R,z6H,Nat.cast_ofNat,
      zjK (hy.trans (min_le_left s.U t.U)),
      zjK (hy.trans (min_le_right s.U t.U)),
      zjK (hw.trans (min_le_left s.B t.B)),
      zjK (hw.trans (min_le_right s.B t.B))]
  have hxCorner (y :ℕ) (hy :y=0∨y=aa3 s t) :
      XC s t a b 2 y z≤M:= by
    have hy' : y≤aa3 s t:=hy.elim (fun h=>h ▸ zD0 _) (fun h=>h ▸ le_rfl)
    refine bbN (F:=XC s t a b 2 y)
      (l:=0) (u:=ad3 s t) (a :=0)
      (b:=2*a*y - b*(((s.U:ℚ)-y)+((t.U:ℚ)-y)))
      (c:=b*(((s.U:ℚ)-y)*t.B+((t.U:ℚ)-y)*s.B))
      (zD0 z) hz le_rfl ?_ (hC y hy 0 (Or.inl rfl)) (hC y hy _ (Or.inr rfl))
    intro w _ hw
    rw [hform y w hy' hw]
    ring
  refine bbN (F:= fun y=>XC s t a b 2 y z)
    (l:=0) (u:=aa3 s t) (a :=0)
    (b:=2*a*z - b*(((t.B:ℚ)-z)+((s.B:ℚ)-z)))
    (c:=b*((s.U:ℚ)*((t.B:ℚ)-z)+(t.U:ℚ)*((s.B:ℚ)-z)))
    (zD0 x) hx le_rfl ?_ (hxCorner 0 (Or.inl rfl)) (hxCorner _ (Or.inr rfl))
  intro y _ hy
  rw [hform y z hy hz]
  ring
private theorem ep6 (s t:Shape) {a b M:ℚ} (ha :0≤a) (hb:0≤b)
  {x z :ℕ} (hx :x≤aa3 s t)
  (h0:XC s t a b 3 0 0≤M)
  (hX:XC s t a b 3 (aa3 s t) 0≤M) :
  XC s t a b 3 x z≤M:= by
 change XC s t a b 3 x 0≤M
 refine bbN (F:= fun y=>XC s t a b 3 y 0)
  (l:=0) (u:=aa3 s t) (a :=a+b)
  (b := -b*((s.U:ℚ)+t.U)) (c:=b*(s.U:ℚ)*t.U)
  (zD0 x) hx (add_nonneg ha hb) ?_ h0 hX
 intro y _ hy
 change a*((y*y :ℕ) :ℚ)+b*(((s.U-y)*(t.U-y) :ℕ) :ℚ)= _
 simp only [z2R,zjK (hy.trans (min_le_left s.U t.U)),
  zjK (hy.trans (min_le_right s.U t.U))]
 ring
private theorem edl {w:ℚ} (L:List ℚ) (init :ℚ)
   (h:w≤ init∨w∈L) :w≤L.foldl max init := by
 induction L generalizing init with
 | nil=>exact h.resolve_right List.not_mem_nil
 | cons v L ih =>
   apply ih
   rcases h with h | h
   · exact Or.inl (h.trans (le_max_left _ _))
   · rcases List.mem_cons.mp h with rfl | h
     · exact Or.inl (le_max_right _ _)
     · exact Or.inr h
private def aWe (s t:Shape) :List ℕ :=
 [0,ad3 s t,min (ad3 s t) (s.B-s.J),
   min (ad3 s t) (t.B-t.J)]
private theorem ebA (s t:Shape) :
   min (s.B-s.J) (t.B-t.J)∈aWe s t:= by
 let c:=min (s.B-s.J) (t.B-t.J)
 have hc:c≤ad3 s t :=
   le_min ((min_le_left _ _).trans (Nat.sub_le ..)) ((min_le_right _ _).trans (Nat.sub_le ..))
 rcases min_choice (s.B-s.J) (t.B-t.J) with h | h
 · have he :=min_eq_right (show s.B-s.J≤ad3 s t from h ▸ hc)
   simp [aWe,h,he]
 · have he :=min_eq_right (show t.B-t.J≤ad3 s t from h ▸ hc)
   simp [aWe,h,he]
theorem ddN (s t:Shape) {x z r m:ℕ} (square :Bool) (k :Fin 4)
   (hx :x≤aa3 s t) (hz :z≤ad3 s t)
   (hsJ:s.J≤ s.B) (htJ:t.J≤t.B) :
   aps s t x z r m square k≤alN s t r m square k := by
 let a :ℚ:=(aof r k :ℚ)⁻¹
 let n:=m+1 - r
 let d:=if square || (k == 3) then n^2 else n
 let b:ℚ:=(d:ℚ)⁻¹
 have ha :0≤a :=inv_nonneg.mpr (zqJ _)
 have hb:0≤b:=inv_nonneg.mpr (zqJ _)
 have hEq (y w:ℕ) :aps s t y w r m square k=XC s t a b k y w:= by
   simp only [aps,XC,a,b,d,n,div_eq_mul_inv,mul_comm]
 have hcorner (y w:ℕ) (hy :y=0∨y=aa3 s t) (hw:w∈aWe s t) :
     XC s t a b k y w≤alN s t r m square k := by
   rw [← hEq]
   apply edl
   refine Or.inr (List.mem_flatMap.mpr ⟨y,?_,List.mem_map.mpr ⟨w,hw,rfl⟩⟩)
   exact hy.elim (fun h=> by simp [h]) (fun h=> by simp [h])
 rw [hEq]
 have h0:0∈aWe s t:= by simp [aWe]
 have hZ:ad3 s t∈aWe s t:= by simp [aWe]
 fin_cases k
 · exact goV s t hb hz hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
     (hcorner 0 _ (Or.inl rfl) hZ) (hcorner 0 _ (Or.inl rfl) (ebA s t))
 · exact eHW s t hb hx hsJ htJ (hcorner 0 0 (Or.inl rfl) h0)
     (hcorner _ 0 (Or.inr rfl) h0)
 · exact eAR s t hx hz (fun y hy w hw =>
     hcorner y w hy (hw.elim (fun h=>h ▸ h0) (fun h=>h ▸ hZ)))
 · exact ep6 s t ha hb hx (hcorner 0 0 (Or.inl rfl) h0)
     (hcorner _ 0 (Or.inr rfl) h0)
end
end aZC
end
section
namespace akZ
noncomputable section


open cu (Jet Shape A5)
open gT (Ambient gk)
open pI (oU)
open YX (bjf)
open atc (jetDegree gY)
open scoped BigOperators
def aB5 (S:zJe (znc Ambient)) :Prop :=
 ∀ I∈S,I.IsPrime∧ringKrullDim (gk I)=2∧I.height=2∧bjf I
def yE (D:Jet) :Fin 3→ℕ :=
 ![jetDegree D,D.natDegree,gY D]
def ajz (D:zJe Jet) (j:Fin 3) :ℕ :=
 ∑ f∈D,yE f j
def dm2 :Prop :=
  ∀ (s :Shape) (P:Jet),oU P s →
    ∀ j a,oU (A5 j a P) s
end
end akZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
namespace TD
noncomputable section
open Polynomial
open gT (Ambient tK)
open pI (xN dual abM aaS pN mass)
open ac2
open ac3
open private c3F from ProximityPrize.SubmissionLower.U
open scoped BigOperators Classical
theorem fS7 (S:zJe (znc Ambient))
    (hS : ∀ I∈S,xN I ∧ ¬ dual I) {B J:ℕ}
    (hord:mass S 1≤J) (hmix :mass S 2≤B) :
    ∃ G:tK,abM G B J ∧ ∀ I∈S,aaS G I:= by
  have hchoose (I:znc Ambient) :
      ∃ G:tK,I∈S→abM G (pN I 2) (pN I 1)∧aaS G I:= by
    by_cases hI:I∈S
    · obtain ⟨G,hg⟩:=c3F bzS.proof cy5.proof
        (hS I hI).1 (hS I hI).2
      exact ⟨G,fun _=>hg⟩
    · exact ⟨1,fun h=>(hI h).elim⟩
  choose G hG using hchoose
  have hp:=akR.eOT S G (fun I=>pN I 2)
    (fun I=>pN I 1) (fun I hI=>(hG I hI).1)
  exact ⟨∏ I∈S,G I,⟨hp.1,hp.2.1.trans hord,fun j i h=>(hp.2.2 j i h).trans hmix⟩,
    fun I hI=>akR.eOY hI G (hG I hI).2⟩
end
end TD
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace akZ
noncomputable section
open P1 (K p)
open cu gT pI YX XY Polynomial
open scoped BigOperators Classical
open private a8m bYs c2M from ProximityPrize.SubmissionLower.CR
theorem bt8 {P Q:Jet} (hp:ag6 P Q) {s t:Shape}
  (hs :s.J≤ s.B) (ht:t.J≤t.B) (hP:oU P s) (hQ:oU Q t) :
  ∃ S:zJe (znc Ambient),aB5 S∧dM S (aJh s t) ∧
    ∀ z R,rD P z R=0→ rD Q z R=0 → ∃ I∈S,IZ I z R:= by
 obtain ⟨S,hS,hcover⟩:=aRY.proof _ _ hp
 obtain ⟨hfinite,hfits⟩:=a8m _ _ hp s t hs ht hP hQ S hS
 refine ⟨S,?_,hfits,hcover⟩
 intro I hI
 obtain ⟨hprime,hdim,hrow,hcut⟩:=hS I hI
 exact ⟨hprime,hdim,bYs hp hprime hdim hrow hcut,hfinite I hI⟩
theorem caH (f :Equation) (hi:Irreducible f)
  (hd:0<f.natDegree) (hp:f.natDegree<p) :
  ∃ S:zJe (znc Ambient),aB5 S ∧
    dM S (af1 (My f) f.natDegree) ∧
    ∀ z R,yq f z R=0 → ∃ I∈S,IZ I z R:= by
 obtain ⟨S,hS,hf,hc⟩:=c2M f hi hd hp
 exact ⟨S,fun I hI=>⟨(hS I hI).1,(hS I hI).2.1,(hS I hI).2.2.1,
  (hS I hI).2.2.2.1⟩,hf,hc⟩
theorem collect {α:Type*} (D:zJe α)
   (budget:α→Fin 4→ℕ) (T:α→K→K[X]→Prop)
   (h : ∀ d∈D,∃ S:zJe (znc Ambient),aB5 S∧dM S (budget d) ∧
     ∀ z R,T d z R → ∃ I∈S,IZ I z R) :
   ∃ S:zJe (znc Ambient),aB5 S∧dM S (fun k => ∑ d∈D,budget d k) ∧
     ∀ d∈D,∀ z R,T d z R → ∃ I∈S,IZ I z R:= by
 classical
 let C (d:α) :=if hd:d∈D then Classical.choose (h d hd) else ∅
 have hC (d:α) (hd:d∈D) :
     aB5 (C d)∧dM (C d) (budget d) ∧
     ∀ z R,T d z R → ∃ I∈C d,IZ I z R:= by
   simpa only [C,dite_eq_left hd] using Classical.choose_spec (h d hd)
 refine ⟨D.biUnion C,?_,?_,?_⟩
 · intro I hI
   obtain ⟨d,hd,hi⟩:=Finset.mem_biUnion.mp hI
   exact (hC d hd).1 I hi
 · intro k
   exact (bhF D C (fun I=>pN I k)).trans
     (zQk fun d hd=>(hC d hd).2.1 k)
 · intro d hd z R hr
   obtain ⟨I,hI,hone⟩:=(hC d hd).2.2 z R hr
   exact ⟨I,Finset.mem_biUnion.mpr ⟨d,hd,hI⟩,hone⟩
end
end akZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 1500000
namespace TD
noncomputable section
open Polynomial
open scoped BigOperators Classical
def c2 :Prop :=aSt
end
end TD
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1200000
namespace akZ
noncomputable section
open P1 (p)
open TD (auN)
open cu gT pI XY Polynomial UniqueFactorizationMonoid
open atc (cN1 aW4 bv9 bHW acG bNz bri)
open bjF (view b2m bPL cvg axC)
open czF (aii cZK cZL)
open qQ (Ng)
open scoped BigOperators Classical
open private dcF b05 from ProximityPrize.SubmissionLower.T
open private cNA from ProximityPrize.SubmissionLower.T
open private b1g b0u from ProximityPrize.SubmissionLower.A3
structure aSK {P:Jet} {s :Shape} (A:NO P s) where
 content:aZ
 row:Jet
 content_ne :content≠0
 content_le :content.totalDegree≤ s.U
 aPZ:row≠0
 row_dvd:row∣P
 row_caps :oU row s
 bu2 :A.residual=C (C content)*row
 primitive : ∀ b:aZ,C (C b)∣row→ IsUnit b
 no_fixed : ∀ g:tK,Irreducible (Gw g) → ¬ Gw g∣row
 Eh : ∀ z S,rD P z S=0 →
  qD z content=0∨FW A.equation S=0∨rD row z S=0
theorem strip {P:Jet} {s :Shape} (hP:P≠0) (hc:oU P s) (A:NO P s) :
   Nonempty (aSK A) := by
 have hr :A.residual≠0:= fun hz=>hP (by rw [A.factorization,hz,mul_zero])
 have hd:A.residual∣P:=⟨_,A.factorization.trans (mul_comm _ _)⟩
 obtain ⟨a,R,he,hprim⟩:=cN1 A.residual hr
 have hm: (C (C a)*R:Jet)≠0:=he ▸ hr
 have hR:=(show R∣A.residual from ⟨_,he.trans (mul_comm _ _)⟩)
 refine ⟨⟨a,R,by simpa using left_ne_zero_of_mul hm,
   dcF hP hc ((show C (C a)∣A.residual from ⟨R,he⟩).trans hd),
   right_ne_zero_of_mul hm,hR.trans hd,b05 hP hc (hR.trans hd),
   he,hprim,fun g hg hgR=>A.Ra g hg (hgR.trans hR),?_⟩⟩
 intro z S h
 have H :=congrArg (vf z S) (A.factorization.trans (congrArg (Gw A.equation * ·) he))
 change vf z S P=0 at h
 rw [h,map_mul,map_mul] at H
 change 0=vf z S (Ng A.equation) *
   (vf z S (aii a)*vf z S R) at H
 rw [cZK,cZL,eq_comm,mul_eq_zero,mul_eq_zero] at H
 rcases H with h | h | h
 · exact Or.inr (Or.inl h)
 · exact Or.inl h
 · exact Or.inr (Or.inr h)
theorem b2H {P Q:Jet} (hP:P≠0) (hQ:Q≠0) (j:Fin 3) :
   yE (P*Q) j=yE P j+yE Q j:= by
 fin_cases j
 · exact bHW hP hQ
 · exact natDegree_mul hP hQ
 · exact acG hP hQ
private theorem cN3 (j:Fin 3) :yE 1 j=0:= by
 fin_cases j
 · exact bri (1 :Equation) |>.trans natDegree_one
 · exact natDegree_one
 · exact bNz (1 :aZ) |>.trans MvPolynomial.totalDegree_one
theorem d5L {P:Jet} (hP:P≠0) (r :ℕ) (j:Fin 3) :
   yE (P^r) j=r*yE P j:= by
 induction r with
 | zero=>simp [cN3]
 | succ r ih =>
   rw [pow_succ,b2H (pow_ne_zero _ hP) hP,ih,Nat.succ_mul]
theorem cN4 {S:zJe Jet} {f :Jet→Jet} (hf : ∀ d∈S,f d≠0) (j:Fin 3) :
   yE (∏ d∈S,f d) j = ∑ d∈S,yE (f d) j:= by
 classical
 induction S using Finset.induction_on with
 | empty=>simp [cN3]
 | insert d S hd ih =>
   have hS : ∀ e∈S,f e≠0:= fun e he=>hf e (Finset.mem_insert_of_mem he)
   rw [Finset.prod_insert hd,Finset.sum_insert hd,
    b2H (hf d (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hS),ih hS]
theorem b2I {P Q:Jet} (hQ:Q≠0) (hd:P∣Q) (j:Fin 3) :
  yE P j≤yE Q j:= by
 obtain ⟨T,rfl⟩:=hd
 rw [b2H (left_ne_zero_of_mul hQ) (right_ne_zero_of_mul hQ)]
 exact z8K _ _
theorem bCj (P:Jet) (s :Shape) :
   oU P s ↔ ∀ j,yE P j≤auN s j:= by
 rw [aW4]
 constructor
 · rintro ⟨hB,hJ,hU⟩ j
   fin_cases j <;> assumption
 · intro h
   exact ⟨h 0,h 1,h 2⟩
def btm (P:Jet) :Shape :=
 ⟨0,yE P 0,yE P 1,yE P 2⟩
theorem bKa (P:Jet) :oU P (btm P) := by
 apply (bCj _ _).mpr
 intro j
 fin_cases j <;> exact le_rfl
theorem caQ {P:Jet} (hP:P≠0) : (btm P).J≤(btm P).B:= by
 have hc: (P.coeff P.natDegree).coeff P.leadingCoeff.natDegree≠0:= by
  rw [coeff_natDegree,coeff_natDegree]
  exact leadingCoeff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP)
 exact (zmL _ _).trans ((bKa P) _ _ hc).1
theorem cN5 {D E :zJe Jet} (h:D⊆E) (j:Fin 3) :
  ajz D j≤ajz E j :=
 Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _=>zD0 _)
structure aRJ (P:Jet) (D:zJe Jet) :Prop where
 factors : ∀ f∈D,Irreducible f∧f∣P∧alm f ∧
  f∉zxp aii∧f∉zxp Ng
 pairwise : (D:Set Jet).Pairwise IsRelPrime
theorem aRJ.mono {P:Jet} {D E :zJe Jet} (h:aRJ P E) (he :D⊆E) :
   aRJ P D :=
 ⟨fun f hf=>h.factors f (he hf),h.pairwise.mono he⟩
theorem cVg {P:Jet} {s :Shape} {A:NO P s} (R:aSK A) :
    ∃ D:zJe Jet,aRJ P D ∧(∀ j,ajz D j≤auN s j) ∧
      ∀ z S,rD R.row z S=0 → ∃ f∈D,rD f z S=0:= by
  classical
  let _:StrongNormalizationMonoid Jet:=UniqueFactorizationMonoid.strongNormalizationMonoid
  let N :=normalizedFactors R.row
  let D:=N.toFinset
  have hmem (f :Jet) (hf :f∈D) :f∈N :=Multiset.mem_toFinset.mp hf
  have hirr (f :Jet) (hf :f∈D) :Irreducible f :=
    irreducible_of_normalized_factor f (hmem f hf)
  have hdvd (f :Jet) (hf :f∈D) :f∣R.row:=dvd_of_mem_normalizedFactors (hmem f hf)
  have hprod: (∏ f∈D,f)∣R.row :=
    (Multiset.toFinset_prod_dvd_prod N).trans (prod_normalizedFactors R.aPZ).dvd
  refine ⟨D,⟨?_,?_⟩,?_,?_⟩
  · intro f hf
    have hfix :f∉zxp Ng:= by
      rintro ⟨g,rfl⟩
      exact R.no_fixed g (hirr _ hf) (hdvd _ hf)
    have hseed :f∉zxp aii:= by
      rintro ⟨a,rfl⟩
      exact (hirr _ hf).not_isUnit (isUnit_C.mpr (isUnit_C.mpr (R.primitive a (hdvd _ hf))))
    exact ⟨hirr f hf,(hdvd f hf).trans R.row_dvd,
      by_contra (fun h=>hfix (by
        obtain ⟨g,hg⟩:=cNA f h
        exact ⟨g,hg.symm⟩)),hseed,hfix⟩
  · intro f hf g hg hne
    exact (hirr f hf).isRelPrime_iff_not_dvd.mpr fun hd =>
      hne (normalizedFactors_eq_of_dvd R.row f (hmem _ hf) g (hmem _ hg) hd)
  · intro j
    calc
      _=yE (∏ f∈D,id f) j :=
        (cN4 (f :=id) (fun f hf=>(hirr f hf).ne_zero) j).symm
      _≤yE R.row j:=b2I R.aPZ hprod j
      _≤_:=(bCj _ _).mp R.row_caps j
  · intro z S hz
    change vf z S R.row=0 at hz
    have hm:=map_dvd (vf z S) (prod_normalizedFactors R.aPZ).symm.dvd
    change vf z S R.row∣vf z S N.prod at hm
    rw [hz,zero_dvd_iff,map_multiset_prod,Multiset.prod_eq_zero_iff,Multiset.mem_map] at hm
    obtain ⟨f,hf,he⟩:=hm
    exact ⟨f,Multiset.mem_toFinset.mpr hf,he⟩
theorem emh {D R:Jet} {s :Shape} (hi:Irreducible D) (hseed :alm D)
    (hR:R≠0) (hcap:oU R s) (hsmall:s.U<p) {e :ℕ}
    (hall : ∀ i a,a≤e→D ∣A5 i a R) :D^(e+1)∣R:= by
  obtain ⟨i,hpos⟩:=b2m D hseed
  have hD:D ∣R:= by
    apply (map_dvd_iff (view i)).mp
    simpa only [bPL,hasseDeriv_zero'] using
      (map_dvd_iff (view i)).mpr (hall i 0 (zD0 _))
  have hbound: (view i D).natDegree<p :=
    ((natDegree_le_of_dvd ((map_dvd_iff (view i)).mpr hD)
      ((view i).map_ne_zero_iff.mpr hR)).trans
        (cvg i R s.U ((bv9 _ _).mp ((aW4 _ _).mp hcap).2.2))).trans_lt hsmall
  let:CharP FX p:=charP_of_injective_ringHom jz.injective p
  let:CharP axC p:=charP_of_injective_ringHom (MvPolynomial.C_injective (Fin 1) FX) p
  have hirr :Irreducible (view i D) :=(MulEquiv.irreducible_iff (view i)).mpr hi
  have hprime :Prime (view i D) :=UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  apply (map_dvd_iff (view i)).mp
  rw [map_pow]
  apply b1g hprime (b0u _ hpos hbound)
  intro a ha
  rw [← bPL]
  exact (map_dvd_iff (view i)).mpr (hall i a (zeh ha))
theorem bLw {P R:Jet} {D:zJe Jet} (hD:aRJ P D)
    {s :Shape} (hR:R≠0) (hcap:oU R s) (hsmall:s.U<p)
    (e :ℕ) (hall : ∀ f∈D,∀ i a,a≤e→f∣A5 i a R) (j:Fin 3) :
    ajz D j≤auN s j/(e+1) := by
  have hprod: (∏ f∈D,f^(e+1))∣R:= by
    apply Finset.prod_dvd_of_isRelPrime
    · intro f hf g hg hne
      exact (hD.pairwise hf hg hne).pow_left.pow_right
    · intro f hf
      exact emh (hD.factors f hf).1 (hD.factors f hf).2.2.1 hR hcap hsmall (hall f hf)
  apply (Nat.le_div_iff_mul_le (ztH e)).mpr
  rw [Nat.mul_comm,ajz,zxw]
  calc
    _=yE (∏ f∈D,f^(e+1)) j:= by
      rw [cN4 (fun f hf=>pow_ne_zero _ (hD.factors f hf).1.ne_zero)]
      exact zUo rfl fun f hf =>
        (d5L (hD.factors f hf).1.ne_zero _ j).symm
    _≤yE R j:=b2I hR hprod j
    _≤_:=(bCj _ _).mp hcap j
end
end akZ
end
section
namespace aZC
open TD (bf7 alN)
private theorem eu0 (v :ℚ) (f :ℕ→ℚ) (L:List ℕ) (init :ℚ)
   (hi:v≤ init) (h : ∀ j∈L,v≤f j) :
   v≤L.foldl (fun a j=>min a (f j)) init := by
 induction L generalizing init with
 | nil=>exact hi
 | cons j L ih =>
   exact ih _ (le_min hi (h j (List.mem_cons_self ..)))
     (fun i hii=>h i (List.mem_cons_of_mem _ hii))
theorem proof :TD.c2 := by
 intro s t r square P Q _ _ hsB _ hsU _ hsJ htJ hP hQ hPs hQt hno A B S hdual hpass k
 let m:=r+1
 obtain ⟨x,hx,z,hz,ht⟩ :=
   eJN s t m square P Q hsB hsU hP hQ hPs hQt hno A B S hdual hpass
 have bound (j:ℕ) (hj:j< m) :
     TD.J2 S k≤alN s t (j+1) m square k :=
   (ht (j+1) (ztH _) hj k).trans (ddN s t square k hx hz hsJ htJ)
 change _≤bf7 s t r square k
 unfold bf7
 exact eu0 _ _ _ _ (bound 0 (ztH _))
   (fun j hj=>bound j (List.mem_range.mp hj))
end aZC
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace akZ
noncomputable section
open TD (arC aIe)
open cu (Jet Shape)
open YX (aJh af1)
open scoped BigOperators Classical
def aHP (s :Shape) (k :Fin 4) (f :Jet) :ℕ :=
 ∑ j,arC s k j*yE f j
def weightedDegree (w:Fin 3→ℕ) (D:zJe Jet) :ℕ :=
 ∑ j,w j*ajz D j
theorem dl2 (w:Fin 3→ℕ) (D:zJe Jet) :
  weightedDegree w D = ∑ f∈D,∑ j,w j*yE f j:= by
 unfold weightedDegree ajz
 simp_rw [zxw]
 rw [Finset.sum_comm]
theorem cfi (f :Jet) (s :Shape) (hs :s.J≤ s.B) (k :Fin 4) :
   aJh (btm f) s k=aHP s k f := by
 fin_cases k
 · simp only [aJh,aHP,zCj,arC,btm]
   change yE f 0*s.J+s.B*yE f 1 - yE f 1*s.J =
    s.J*yE f 0+(s.B-s.J)*yE f 1+0*yE f 2
   have hm:=ztf (yE f 1) hs
   rw [Nat.mul_comm (yE f 1) s.J,Nat.add_sub_assoc hm,← Nat.sub_mul]
   ring
 · change _ = ∑ j,arC s 1 j*yE f j
   rw [zCj]
   change yE f 2*s.J+s.U*yE f 1 =
    0*yE f 0+s.U*yE f 1+s.J*yE f 2
   ring
 · change _ = ∑ j,arC s 2 j*yE f j
   rw [zCj]
   change yE f 2*s.B+s.U*yE f 0 =
    s.U*yE f 0+0*yE f 1+s.B*yE f 2
   ring
 · change _ = ∑ j,arC s 3 j*yE f j
   rw [zCj]
   change yE f 2*s.U=0*yE f 0+0*yE f 1+s.U*yE f 2
   ring
theorem cs5 {D T:zJe Jet} (hT:T⊆D) (cap old:Fin 3→ℕ)
    (s :Shape) (k :Fin 4) (hcap : ∀ j,ajz D j≤ cap j) :
    (∑ f∈D \ T,aHP s k f) +
      weightedDegree (fun j=>max (old j) (arC s k j)) T ≤
      weightedDegree old D + aIe cap old s k := by
  classical
  let w:= fun j=>max (old j) (arC s k j)
  have hadd (j:Fin 3) :old j+(w j-old j)=w j :=
    Nat.add_sub_of_le (le_max_left _ _)
  calc
    _≤weightedDegree w (D \ T)+weightedDegree w T:= by
      apply Nat.add_le_add_right
      rw [dl2]
      exact zQk fun f _ =>
        zQk fun j _=>ztf _ (le_max_right _ _)
    _=weightedDegree w D:= by
      simp only [dl2]
      exact Finset.sum_sdiff hT
    _=weightedDegree old D + ∑ j,(w j-old j)*ajz D j:= by
      unfold weightedDegree
      rw [← zfW]
      exact zUo rfl fun j _=> by rw [← Nat.add_mul,hadd]
    _≤_:=z3b
      (zQk fun j _=>zBI _ (hcap j)) _
theorem c2L (D:zJe Jet) (cap:Fin 3→ℕ)
    (hcap : ∀ j,ajz D j≤ cap j) (k :Fin 4) :
    (∑ f∈D,af1 (yE f 2) (yE f 0) k) ≤
      af1 (cap 2) (cap 0) k := by
  fin_cases k
  · exact hcap 0
  · exact hcap 2
  · change (∑ f∈D,2*yE f 2*yE f 0)≤2*cap 2*cap 0
    calc
      _ ≤ ∑ f∈D,2*yE f 2*cap 0:= by
        exact zQk fun f hf=>zBI _
          ((zfK (fun _ _=>zD0 _) hf).trans (hcap 0))
      _=(2*ajz D 2)*cap 0:= by rw [ajz,zxw,Finset.sum_mul]
      _≤_:=ztf _ (zBI _ (hcap 2))
  · change (∑ f∈D,yE f 2*yE f 2)≤ cap 2*cap 2
    calc
      _ ≤ ∑ f∈D,yE f 2*cap 2 := by
        exact zQk fun f hf=>zBI _
          ((zfK (fun _ _=>zD0 _) hf).trans (hcap 2))
      _=ajz D 2*cap 2 :=(Finset.sum_mul _ _ _).symm
      _≤_:=ztf _ (hcap 2)
end
end akZ
end
section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option maxHeartbeats 1400000
namespace akZ
noncomputable section
open P1 (p)
open cu gT pI YX XY Polynomial
open qQ (aeH)
open atc (bri bg3)
open scoped BigOperators Classical
open private c2O from ProximityPrize.SubmissionLower.K
private theorem b6z {f C:Jet} (hf :Irreducible f) (hd : ¬ f∣C) :
   ag6 f C :=
 ⟨hf.ne_zero,fun h=>hd (h ▸ dvd_zero _),fun _ hD hDf hDC =>
   hd ((hD.associated_of_dvd hf hDf).dvd'.trans hDC)⟩
private theorem dg6 {P Q:Jet} {t:Shape} {D:zJe Jet}
    (hD:aRJ P D) (hnc:aeH P Q)
    (hQc:oU Q t) (hJB:t.J≤t.B) (hB:t.B<p) (hQ:Q≠0)
    (f :Jet) (hf :f∈D) :
    ∃ S:zJe (znc Ambient),aB5 S ∧
      dM S (fun k=>aHP t k f+af1 (yE f 2) (yE f 0) k) ∧
      ∀ z R,(rD f z R=0∧rD Q z R=0) → ∃ I∈S,IZ I z R:= by
  obtain ⟨hi,hPf,_,hs,hfix⟩:=hD.factors f hf
  by_cases hd:f∣Q
  · have hv :f.natDegree=0:= by
      by_contra h
      exact hfix (hnc f hi hPf hd (zOl h))
    obtain ⟨hc,hirr,hpos⟩:=c2O hi hv hs
    have hdegrees :yE f 0=(f.coeff 0).natDegree ∧
        yE f 2=My (f.coeff 0) :=
      ⟨(congrArg atc.jetDegree hc).symm.trans (bri _),
       (congrArg atc.gY hc).symm.trans (bg3 _)⟩
    have hsmall: (f.coeff 0).natDegree<p:= by
      rw [← hdegrees.1]
      exact ((b2I hQ hd 0).trans ((bCj _ _).mp hQc 0)).trans_lt hB
    obtain ⟨S,hG,hF,hC⟩:=caH _ hirr hpos hsmall
    refine ⟨S,hG,fun k=>(hF k).trans ?_,fun z R h=>hC z R ?_⟩
    · rw [hdegrees.1,hdegrees.2]
      exact zmL _ _
    · have hz :=h.1
      rw [← hc] at hz
      simpa [rD,yq] using hz
  · obtain ⟨S,hG,hF,hC⟩ :=
      bt8 (b6z hi hd) (caQ hi.ne_zero) hJB (bKa f) hQc
    refine ⟨S,hG,fun k=>(hF k).trans ?_,fun z R h=>hC z R h.1 h.2⟩
    rw [cfi f t hJB]
    exact z8K _ _
end
end akZ
end
section
set_option backward.isDefEq.respectTransparency false
namespace akZ
def c2 :Prop :=dm2
end akZ
end
section
namespace bSf
open cu (Shape)
open YX (aL7 aJh af1)
open Ty (aof)
open TD (aps)
private theorem ddM (s t:Shape) (x z :ℕ) (k :Fin 4) :
  aps s t x z 1 1 false k =
   ((aJh (aL7 s x z) (aL7 t x z) k+af1 x z k :ℕ) :ℚ) := by
 have hscale :aof 1 k=1 := by fin_cases k <;> rfl
 have hdenom: (if false || (k == 3) then (1+1 - 1 :ℕ)^2 else 1+1 - 1)=1 := by
  split <;> rfl
 simp only [aps,hscale,hdenom,Nat.cast_one,div_one,z6H]
 exact add_comm _ _
private theorem ajB {n:ℕ} {r :ℚ} (h: (n:ℚ)≤ r) :n≤ r.floor.toNat := by
 have hi: (n:ℤ)≤ r.floor :=Rat.le_floor_iff.mpr (by exact_mod_cast h)
 simpa using Int.toNat_le_toNat hi
end bSf
end
section
set_option backward.isDefEq.respectTransparency false
namespace czY
open cu (FX aZ Jet A5)
open axj (translation Bg mapCoeffs a5F)
private theorem coV (i:Fin 2) (r :ℕ) (P:aZ) :
    (Bg i r P).totalDegree≤P.totalDegree := by
  classical
  let g:Fin 2→z3y (Option (Fin 2)) FX :=
    fun j=>z9v (some j)+if j=i then z9v none else 0
  let f :aZ →ₐ[FX] z3y (Option (Fin 2)) FX:=zIe g
  have htrans :translation i=(MvPolynomial.optionEquivLeft FX (Fin 2)).toAlgHom.comp f := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj:j=i <;> simp [translation,f,g,hj]
  have hg (j:Fin 2) : (g j).totalDegree≤1 := by
    by_cases hj:j=i
    · simpa [g,hj] using (MvPolynomial.totalDegree_add
        (z9v (some j) :z3y (Option (Fin 2)) FX)
        (z9v none))
    · simp [g,hj]
  have hf : (f P).totalDegree≤P.totalDegree := by
    conv_lhs=>rw [P.as_sum]
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    change (zIe g (MvPolynomial.monomial m (P.coeff m))).totalDegree≤_
    rw [MvPolynomial.aeval_monomial]
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.algebraMap_eq,MvPolynomial.totalDegree_C,zero_add,Finsupp.prod]
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
    refine le_trans (zQk (fun j _ => ?_)) (MvPolynomial.le_totalDegree hm)
    exact (zVs _ _).trans (by simpa using zBI (m j) (hg j))
  change ((translation i P).coeff r).totalDegree≤_
  rw [htrans]
  exact (MvPolynomial.totalDegree_coeff_optionEquivLeft_le FX (Fin 2) (f P) r).trans hf
private theorem coZ (i:Fin 2) (r :ℕ) (P:Jet) (j k :ℕ) :
  ((A5 i r P).coeff j).coeff k=Bg i r ((P.coeff j).coeff k) := by
 change ((mapCoeffs (mapCoeffs (Bg i r)) P).coeff j).coeff k= _
 rw [a5F,a5F]
theorem proof :akZ.c2 := by
 intro s P hP i r j k hc
 rw [coZ] at hc ⊢
 have hsource : (P.coeff j).coeff k≠0:= by
  intro hz
  exact hc (by rw [hz,map_zero])
 obtain ⟨hB,hJ,hU⟩:=hP j k hsource
 exact ⟨hB,hJ,(coV i r _).trans hU⟩
end czY
end
