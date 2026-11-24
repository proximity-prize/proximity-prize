import ProximityPrize.SubmissionLower.ZYEj7Fd
set_option Elab.async false
open _root_ renaming Fin.sum_univ_three → zCj, Finsupp.weight_eq_sum → z1K, Fintype.sum_option → zy6, IsFractionRing.injective → zxb, MvPolynomial.C → znf, MvPolynomial.C_dvd_iff_dvd_coeff → zXG, MvPolynomial.coeff_C_mul → z06, MvPolynomial.map → zDK, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.hasseDeriv → z75, Polynomial.map_pow → z5m, RingHom.comp_assoc → zxS
section
set_option autoImplicit true
namespace qje58fc
noncomputable section
open Finset Polynomial
open cu (L)
open jA (jK kS mA jH)
open aFN (Slot)
open P5_7_2 (TopRow)
open q7IA62d (Lq)
def restoreMap (H :L[X]) (R:kS[X]) :jK →ₐ[L] Lq :=
  MvPolynomial.aevalTower
    (((Algebra.ofId kS[X] Lq).restrictScalars L).comp
      (Polynomial.mapAlgHom (Algebra.ofId L kS)))
    (fun i:mA=>i.elim
      (znf (z1z (algebraMap L[X] kS z7y)))
      (fun j=>znf (z75 j.val R) +
        ∑ k :Fin 3,if k.val≤j.val then
          znf (z75 (j.val - k.val) (jH H)) *
            MvPolynomial.X k else 0))
def testSpace (H :L[X]) (R K:kS[X]) (n:ℕ) :Submodule L jK :=
  ((Ideal.span {((znf K:Lq)^n)}).restrictScalars L).comap
    (restoreMap H R).toLinearMap
theorem mem_testSpace {H R K n F} :
  F∈testSpace H R K n↔(znf K:Lq)^n∣restoreMap H R F:= by
 simp only [testSpace,Submodule.mem_comap,Submodule.restrictScalars_mem,
  Ideal.mem_span_singleton,AlgHom.toLinearMap_apply]
def seedValue (a b c:L) :kS :=
  algebraMap L[X] kS (z1z a*z7y) /
    algebraMap L[X] kS (z1z b+Polynomial.X*z1z c)
def box (t:TopRow) :aR.Shape :=⟨t.shape.B,t.shape.J,t.YM⟩
abbrev ModelIndex (t:TopRow) (U:ℕ) :=
 Σ q:Fin (t.shape.B+1),Slot (box t) q.val×Fin (t.shape.B+t.shape.J)×Fin (U+1)
def modelExponent {t U} (i:ModelIndex t U) :Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![i.2.2.1.val,i.2.2.2.val,i.1.val-i.2.1.1.val-i.2.1.2.val,i.2.1.2.val,i.2.1.1.val]
def modelImage {t U} (i:ModelIndex t U) :MvPolynomial (Fin 5) L :=
  let x :Fin 5→MvPolynomial (Fin 5) L:=MvPolynomial.X
  x 0^i.2.2.1.val*x 1^i.2.2.2.val *
    (x 1 + x 0*x 2)^(i.1.val-i.2.1.1.val-i.2.1.2.val) *
    (x 2 + x 0*x 3)^i.2.1.2.val*(x 3 + x 0*x 4)^i.2.1.1.val
def modelMatrix (t:TopRow) :
    Matrix (ModelIndex t (t.shape.U+t.shape.B)) (ModelIndex t t.shape.U) L :=
  fun i j=>(modelImage j).coeff (modelExponent i)
private def index {t:TopRow} {q:ℕ} (s :Slot (box t) q) :ℕ :=
 s.2.val+2*s.1.val
def vo (t:TopRow) (q g a :ℕ) :
    Matrix (Slot (box t) q) (Slot (box t) q) L :=
  fun r c =>
    if a≤ c.1.val+c.2.val∧r.1.val≤ c.1.val∧c.1.val≤ r.2.val+r.1.val ∧
      t.shape.J≤g+index c∧g+index c<t.shape.J+(t.shape.B+t.shape.J) ∧
      t.shape.J≤g+q+index r∧g+q+index r<t.shape.J+(t.shape.B+t.shape.J) then
      ((c.1.val.choose r.1.val*c.2.val.choose (r.2.val+r.1.val-c.1.val) :ℕ) :L)
    else 0
def windowDebit (t:TopRow) :ℕ :=
  ∑ q∈range (t.shape.B+1),∑ g∈range (t.shape.B+2*t.shape.J),
    ((t.shape.U+1+t.shape.B-2*q)*(vo t q g 0).rank +
      ∑ a∈range (min q t.shape.J),(vo t q g (a+1)).rank)
end
end qje58fc
end
section
set_option autoImplicit true
namespace qj6Q6Cb
noncomputable section
open Polynomial
open scoped BigOperators


open q7IA62d
open cu (L j9)
open DP (jF zG aKF Z7)
open aR (af cK)
open jA (jK kS jH ahb)
open Rk (aPU a04)


open private amA cZA c8B pO aih dcO co0 goi b77 cZw cfm aWN weight_eq_sum from ProximityPrize.SubmissionLower.C


set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
private abbrev residue {h} {D:jF h} (Crt:zG D) (z :L) :=
 jA.Tj (oneNumerator Crt) (oneDenominator Crt) z
private theorem marked_residue {h} {D:jF h} (Crt:zG D)
   {z :K1.K} {S:K1.K[X]} (hm:aKF D z S) :
   let a :=Z7 z 0
   (oneDenominator Crt).eval a≠0∧D.block 0∣j9 S - residue Crt a := by
 let a :=Z7 z 0
 let d:=(oneDenominator Crt).eval a
 let N :=(oneNumerator Crt).map (evalRingHom a)
 let U:=DP.Tj D 0 a
 have hd:d≠0:=Crt.regular 0 a (hm 0).1
 have hmap (H :L[X]) : (H.map (C:L →+* L[X])).map (evalRingHom a)=H := by
   have he : (evalRingHom a).comp (C:L →+* L[X])=RingHom.id L:= by ext c; simp
   rw [map_map,he,map_id]
 have h₀:D.block 0∣U*N+C (d*a)*D.offset 0:= by
   simpa [DP.Tj,U,N,d,hmap] using
     map_dvd (mapRingHom (evalRingHom a)) (oneNumerator_congruence Crt)
 have he : (C d⁻¹:L[X])*C (d*a)=C a := by
   rw [← map_mul,← mul_assoc,inv_mul_cancel₀ hd,one_mul]
 have h₁:D.block 0∣U*residue Crt a+C a*D.offset 0:= by
   simpa only [mul_add,← mul_assoc,mul_comm (C d⁻¹) U,he,jA.Tj,d,N] using
     h₀.mul_left (C d⁻¹)
 refine ⟨hd,(hm 0).1.symm.dvd_of_dvd_mul_left ?_⟩
 have ha :D.block 0∣U*j9 S+C a*D.offset 0:=(hm 0).2
 change D.block 0∣U*(j9 S - residue Crt a)
 simpa only [mul_sub,add_sub_add_right_eq_sub] using dvd_sub ha h₁
private theorem specialize_pole {h} {D:jF h} (Crt:zG D)
  (r :ℕ) (P:jK) (z :L) (hz : (oneDenominator Crt).eval z≠0)
  (hp:znf (jH (D.block 0))^r∣forward Crt P) :
  znf (D.block 0^r)∣aPU (D.block 0) (residue Crt z) z P:= by
 let d:=oneDenominator Crt
 let f :=(pO d).comp (C:L →+* L[X])
 let H :=(D.block 0).map f
 let Q:=amA f (pO d z7y) H (b77 (oneNumerator Crt) d) P
 let gf :L[X] →+* kS:=algebraMap _ _
 have hd:gf d≠0:=(map_ne_zero_iff gf (zxb L[X] kS)).mpr
  (Crt.denominator_ne_zero 0)
 let g:=aih gf hd
 let e :=aih (evalRingHom z) hz
 have hgf :g.comp f=algebraMap L kS:= by
  dsimp only [g,f]
  rw [← zxS,dcO]
  exact (IsScalarTower.algebraMap_eq L L[X] kS).symm
 have hef :e.comp f=RingHom.id L:= by
  dsimp only [e,f]
  rw [← zxS,dcO]
  ext c
  simp
 have hgH :H.map g=jH (D.block 0) := by
  rw [show H= _ from rfl,map_map,hgf,jH]
 have heH :H.map e=D.block 0:= by
  rw [show H= _ from rfl,map_map,hef,map_id]
 have hgQ:zDK (mapRingHom g) Q=forward Crt P:= by
  dsimp only [Q]
  rw [cZA,hgf,hgH]
  dsimp only [g]
  rw [co0,cZw]
  rfl
 have heQ:zDK (mapRingHom e) Q=aPU (D.block 0) (residue Crt z) z P:= by
  dsimp only [Q]
  rw [cZA,hef,heH]
  dsimp only [e]
  rw [co0,cZw,c8B]
  simp [jA.Tj]
 have hg:znf ((H^r).map g)∣zDK (mapRingHom g) Q:= by
  rw [hgQ,z5m,hgH,map_pow]
  exact hp
 have hinj:Function.Injective g :=
  goi _ _ (zxb L[X] kS)
 have hQ:znf (H^r)∣Q:= by
  apply (zXG _ _).mpr
  intro m
  have hc:=(zXG _ _).mp hg m
  rw [MvPolynomial.coeff_map] at hc
  exact (Polynomial.map_dvd_map g hinj ((D.monic 0).map f |>.pow r)).mp hc
 have hr :=map_dvd (zDK (mapRingHom e)) hQ
 rw [MvPolynomial.map_C,heQ] at hr
 change znf ((H^r).map e)∣ _ at hr
 rwa [z5m,heH] at hr
private theorem raw_cut {h r W:ℕ} {D:jF h} {z :L} {res :L[X]}
  {P:jK} {Q:af 3} (hres :res.natDegree≤h)
  (hP:ahb h (W+r*h) P)
  (hQ:aPU (D.block 0) res z P=znf (D.block 0^r)*Q) :
  a04 W Q:= by
 have hdeg:=D.degree 0
 have hP' : ahb (D.block 0).natDegree (W+r*h) P:= by rwa [hdeg]
 have hb:=cfm z (hres.trans_eq hdeg.symm) hP'
 rw [hQ] at hb
 intro m hm
 have hne :=MvPolynomial.mem_support_iff.mp hm
 have hp:=pow_ne_zero r (D.monic 0).ne_zero
 have hc: (znf (D.block 0^r)*Q).coeff m≠0:= by
  rw [z06]
  exact mul_ne_zero hp hne
 have hw:=MvPolynomial.mem_restrictJointDegree.mp hb m hc
 rw [z06,natDegree_mul hp hne,natDegree_pow,hdeg] at hw
 simp only [weight_eq_sum,aWN] at hw
 omega
private theorem evaluated_degree {W:ℕ} {Q:af 3} {T:L[X]}
   (hQ:a04 W Q) (hT:T.natDegree≤131071) : (cK Q T).natDegree≤W:= by
 rw [cK,MvPolynomial.eval_eq]
 apply natDegree_sum_le_of_forall_le
 intro m hm
 refine (natDegree_mul_le_of_le le_rfl ((natDegree_prod_le _ _).trans ?_)).trans (hQ m hm)
 apply Finset.sum_le_sum
 intro i _
 exact (natDegree_pow_le_of_le (m i)
   ((natDegree_hasseDeriv_le T i.val).trans (Nat.sub_le_sub_right hT i.val))).trans_eq
     (Nat.mul_comm _ _)
end
end qj6Q6Cb
end
section
set_option autoImplicit true
namespace qAzyIze
noncomputable section
open Polynomial Finset
open cu (L)
open jA (jK ko iP mA bC)

abbrev Exp:=mA →₀ ℕ
abbrev RawExp:=Fin 3 →₀ ℕ
def jetExp (a :Exp) :RawExp:=Finsupp.equivFunOnFinite.symm (fun j=>a (some j))
def aWN (a :RawExp) :ℕ:=a.sum (fun j e=>(131071 - j.val)*e)
def genericSpan (V:Submodule L jK) :Submodule iP ko :=
 Submodule.span iP (bC '' (V:Set jK))
theorem jet_total (a :Exp) :
  a.weight (fun i=>i.elim 0 (fun _=>1)) =
   a (some 0)+a (some 1)+a (some 2) := by
 simp [z1K,zy6,zCj]
theorem jet_index (a :Exp) :
  a.weight (fun i=>i.elim 0 Fin.val)=a (some 1)+2*a (some 2) := by
 simp [z1K,zy6,zCj,Nat.mul_comm]
theorem raw_weight (a :Exp) :
   aWN (jetExp a)+a (some 1)+2*a (some 2) =
     131071*(a (some 0)+a (some 1)+a (some 2)) := by
 unfold aWN
 rw [Finsupp.sum_fintype _ _ (by simp),zCj]
 change 131071*a (some 0)+131070*a (some 1)+131069*a (some 2) +
   a (some 1)+2*a (some 2)= _
 omega
end
end qAzyIze
end
