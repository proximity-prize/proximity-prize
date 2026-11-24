import ProximityPrize.SubmissionLower.Zdj6KNe
import ProximityPrize.SubmissionLower.ZjG08xb
import ProximityPrize.SubmissionLower.Zay1XCa
import ProximityPrize.SubmissionLower.Zl7U3sa
import ProximityPrize.SubmissionLower.ZEe4bHc
set_option Elab.async false
open _root_ renaming Finset.mem_range → zIR, Finset.range → z4x, Finset.range_mono → znF, Finset.sum_subset → zVG, Polynomial → zM1, Polynomial.X → z7y
section
section
set_option maxRecDepth 4000
namespace qpI7nyd
open cu (L)
open E7 (CurvePlace)
open qNu3xvc qoCymac
open private Ek bsA detect_denominator from ProximityPrize.SubmissionLower.ZjG08xb
private theorem c4Q {R K:Type} [CommSemiring R] [Field K]
   (F:Subfield K) (f :zM1 R →+* K)
   (hC : ∀ c,f (Polynomial.C c)∈F) (hX:f z7y∈F)
   (g:zM1 R) :f g∈F:= by
 induction g using Polynomial.induction_on' with
 | add a b ha hb=>exact (map_add f a b).symm ▸ F.add_mem ha hb
 | monomial n a =>
   rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow]
   exact F.mul_mem (hC a) (F.pow_mem hX _)
private theorem chart_denominator {E :Type} [Field E] [Algebra L E]
   (A:Equation E) (w:CurvePlace L E) (r :Bool) (u:EC A) :
   ∃ a b:Chart A w r,(a :EC A)≠0∧(a :EC A)*u=b:= by
 let B:=Chart A w r
 let F:=Subfield.closure (B:Set (EC A))
 have base (x :B) : (x :EC A)∈F:=Subfield.subset_closure x.property
 have hs (c:E) :seed A c∈F:= by
   rcases w.value.valuationSubring.mem_or_inv_mem c with hc | hc
   · exact base (aee A w r ⟨c,hc⟩)
   · have h:=F.inv_mem (base (aee A w r ⟨c⁻¹,hc⟩))
     change (seed A c⁻¹)⁻¹∈F at h
     rwa [map_inv₀,inv_inv] at h
 have hy :jU A r∈F :=
   Subfield.subset_closure (Algebra.subset_adjoin (Or.inr (by simp)))
 have hy' : a7W A z7y∈F:= by
   cases r
   · exact hy
   · exact inv_inv (a7W A z7y) ▸ F.inv_mem hy
 have hfull:F = ⊤ := by
   apply top_unique
   rw [← IsFractionRing.closure_range_algebraMap (AdjoinRoot A.f) (EC A)]
   apply Subfield.closure_le.mpr
   rintro _ ⟨v,rfl⟩
   obtain ⟨g,rfl⟩:=AdjoinRoot.mk_surjective v
   change a7W A g∈F
   apply c4Q F (a7W A) _ hy'
   exact c4Q F ((a7W A).comp Polynomial.C) hs (base (xAt A w r))
 have hu:u∈F:=hfull.symm ▸ Subfield.mem_top u
 obtain ⟨b,hb,a,ha,he⟩:=Subfield.mem_closure_iff.mp hu
 rw [show (B:Set (EC A))=(B.toSubring :Set (EC A)) from rfl,
   Subring.closure_eq] at hb ha
 by_cases ha0:a=0
 · rw [ha0,div_zero] at he
   exact ⟨1,0,one_ne_zero,by simp [← he]⟩
 · exact ⟨⟨a,ha⟩,⟨b,hb⟩,ha0,(mul_comm a u).trans ((div_eq_iff ha0).mp he).symm⟩
private theorem detect_normal {B K:Type} [CommRing B] [Field K] [Algebra B K]
   [IsNoetherianRing (integralClosure B K)]
   (M:Ideal B) [M.IsPrime] (u:K)
   (hu : ∀ a :B,a∉M → ¬ IsIntegral B (algebraMap B K a*u))
   (hden : ∃ a b:B,algebraMap B K a≠0∧algebraMap B K a*u=algebraMap B K b) :
   ∃ P:Ideal (integralClosure B K),P.IsPrime∧P.height = 1 ∧
     P.comap (algebraMap B (integralClosure B K))≤M ∧
     ¬ (∃ a :integralClosure B K,a∉P ∧ ∃ b:integralClosure B K,(a :K)*u=b) := by
 let R:Type :=integralClosure B K
 let f :B →+* R:=algebraMap _ _
 let D:Ideal R:=Ek (R:=R) u
 have hM:D.comap f≤M:= by
   intro a ha
   by_contra hn
   obtain ⟨b,hb⟩:=(bsA (R:=R) (x :=f a) (u:=u)).mp ha
   exact hu a hn (hb.symm ▸ b.property)
 obtain ⟨a,b,ha,hab⟩:=hden
 have hD:D ≠ ⊥ := by
   intro he
   have hm:f a∈D:=(bsA (R:=R) (u:=u)).mpr ⟨f b,hab⟩
   have hz :f a=0:=Ideal.mem_bot.mp (show f a∈(⊥ : Ideal R) from he ▸ hm)
   exact ha (congrArg (algebraMap R K) hz |>.trans (map_zero _))
 obtain ⟨P,hP,hh,hPM,hDP⟩:=detect_denominator (R:=R) f M u hM hD
 exact ⟨P,hP,hh,hPM,fun ⟨s,hs,t,ht⟩ =>
   hs (hDP ((bsA (R:=R)).mpr ⟨t,ht⟩))⟩
theorem proof :qoCymac.c5:= by
 intro E _ _ A w r hnoeth M hprime u hu
 exact @detect_normal (Chart A w r) (EC A) _ _ _ hnoeth M hprime u hu
  (chart_denominator A w r u)
end qpI7nyd
end
section
namespace qvkfeic
open Polynomial UniqueFactorizationMonoid
open private gpC from ProximityPrize.SubmissionLower.V
open private adG efd aMX from ProximityPrize.SubmissionLower.Y
theorem proof :qxPDCsa.c3:= by
  classical
  intro E _ _ g hg hd
  let R:=radical g
  let r :=R*C g.leadingCoeff
  have factor {q:E[X]} (hq:q∈primeFactors g) :
      Irreducible q∧q.Monic∧q∣g :=
    (Polynomial.mem_normalizedFactors_iff hg).mp (mem_primeFactors.mp hq)
  have hm:R.Monic:=monic_prod_of_monic _ _ fun _ hq=>(factor hq).2.1
  have hs :R.Separable := by
    apply separable_prod'
    · exact fun i hi j hj hij=>(pairwise_primeFactors_isRelPrime hi hj hij).isCoprime
    · intro q hq
      exact gpC (factor hq).1
        ((natDegree_le_of_dvd (factor hq).2.2 hg).trans_lt hd)
  have hlead:r.leadingCoeff=g.leadingCoeff := by
    change (R*C g.leadingCoeff).leadingCoeff=g.leadingCoeff
    rw [leadingCoeff_mul,hm.leadingCoeff,leadingCoeff_C,one_mul]
  have hc:=leadingCoeff_ne_zero.mpr hg
  have hu:IsUnit (C g.leadingCoeff) :=isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hr :r∣g:=hu.mul_right_dvd.mpr radical_dvd_self
  obtain ⟨n,hn⟩:=exists_dvd_radical_self_pow hg
  refine ⟨r,⟨hlead,hs.mul_unit hu,hr,
    ⟨n,hn.trans (pow_dvd_pow_of_dvd (dvd_mul_right R _) n)⟩,?_⟩⟩
  obtain ⟨q,hq⟩:=hr
  have hqm:q.Monic:= by
    have h:=congrArg leadingCoeff hq
    rw [leadingCoeff_mul,hlead] at h
    exact mul_left_cancel₀ hc (by simpa using h.symm)
  intro v b hb i
  have h1 :1≤adG v q:= by
    simpa only [coeff_natDegree,hqm.leadingCoeff,map_one] using aMX v q q.natDegree
  calc
    v (r.coeff i)≤adG v r :=aMX v r i
    _≤adG v r*adG v q:=le_mul_of_one_le_right zero_le h1
    _=adG v g:= by rw [← efd,← hq]
    _≤b:=Finset.sup_le fun j _=>hb j
end qvkfeic
end
section
namespace qqV3gre
noncomputable section
open Polynomial
open cu (L)
open qziIa4d (seedDerivative)
abbrev aQ:=LaurentSeries L
abbrev PhysicalField:=FractionRing aQ[X]
abbrev EC:=AlgebraicClosure PhysicalField
def physicalCoeff :aQ[X] →+* EC :=
 (algebraMap PhysicalField EC).comp (algebraMap aQ[X] PhysicalField)
def integralCoeff : (PowerSeries L)[X] →+* EC :=
 physicalCoeff.comp (mapRingHom (algebraMap (PowerSeries L) aQ))
def arcEquation {E :Type} [Field E] [Algebra L E] (a :E →ₐ[L] aQ)
    (f :E[X][X]) :aQ[X][X] :=
  f.map (mapRingHom a.toRingHom)
def physicalDerivative (f :aQ[X][X]) :aQ[X][X] :=
 f.sum fun i c=>monomial i c.derivative
def seedDiff (t:aQ[X]) :aQ[X] :=
 t.sum fun i c=>monomial i (LaurentSeries.derivative L c)
def constant (a :L) :EC :=
 physicalCoeff (C (algebraMap L aQ a))
def logCuts (f :aQ[X][X]) (t:aQ[X]) (u v :L) (y :EC) :
    EC×EC :=
  let ev (g:aQ[X][X]) :=g.eval₂ physicalCoeff y
  let s := -(ev (seedDerivative f)/ev f.derivative)
  let x := -(ev (physicalDerivative f)/ev f.derivative)
  let l:=(y - constant u)⁻¹-(y - constant v)⁻¹
  (physicalCoeff t*(s*l),
    physicalCoeff t.derivative*(s*l) - physicalCoeff (seedDiff t)*(x*l))
def integralLogs {R:Type} [CommRing R] (ι:R →+* EC)
    (f :aQ[X][X]) (t:aQ[X]) (u v :L) :Prop :=
  ∀ y :EC,f.eval₂ physicalCoeff y=0 →
    (∃ P:R[X],P.Monic∧P.eval₂ ι (logCuts f t u v y).1=0) ∧
    (∃ P:R[X],P.Monic∧P.eval₂ ι (logCuts f t u v y).2=0)
end
end qqV3gre
end
end
section
set_option autoImplicit true
namespace qY7pQzb
noncomputable section
open aR (ao Shape)
open aFN (Slot)
open qzLARrc (derivativeIndex)
open qmb8rCe (cutMatrix rankCut cap sumN_eq)
open Matrix Polynomial
open scoped BigOperators
private theorem cp3 {a :Shape} {q:ℕ} (s :Slot a q) :
    s.1.val≤a.t∧s.1.val+s.2.val≤q:= by
  have hc:=s.1.isLt
  have hb:=s.2.isLt
  simp only [Nat.lt_succ_iff,le_min_iff] at hc hb
  omega
private abbrev Xg:zM1 ao:=z7y
private abbrev V:zM1 ao:=1+Xg
private def amp (k j:ℕ) :ao:=(-1)^j*k.choose j
private def Fg (q n c b:ℕ) :ao:=(Xg^(n-c)*V^(q-n)).coeff b
private def dO (a :Shape) (q d h n:ℕ) :Matrix (Slot a q) (Slot a q) ao :=
  fun r s =>
    if derivativeIndex r<h∧d≤ s.1.val+s.2.val∧r.1.val≤ s.1.val∧s.1.val≤n then
      Fg q n r.1.val r.2.val*(s.1.val.choose r.1.val :ao) *
        amp (q-s.1.val-s.2.val) (n-s.1.val)
    else 0
private theorem expand {F:Type*} [CommRing F] (k b e m:ℕ) :
    ((z7y:zM1 F)^k*(1+Polynomial.X)^b).coeff m =
      ∑ j∈z4x (e+1),
        ((z7y:zM1 F)^(k+j)*(1+Polynomial.X)^(b+e-j)).coeff m *
          ((-1 :F)^j*(e.choose j:F)) := by
  let x :zM1 F:=z7y
  let v :zM1 F:=1+x
  have hu: (-x+v)^e=1 := by simp [v,add_comm]
  have hp:x^k*v^b =
      ∑ j∈z4x (e+1),(x^(k+j)*v^(b+e-j))*C ((-1 :F)^j*(e.choose j:F)) := by
    have hb:=congrArg (fun p:zM1 F=>(x^k*v^b)*p) (add_pow (-x) v e)
    change (x^k*v^b)*(-x+v)^e =
      (x^k*v^b) * ∑ j∈z4x (e+1),(-x)^j*v^(e-j)*e.choose j at hb
    rw [hu,mul_one,Finset.mul_sum] at hb
    refine hb.trans (Finset.sum_congr rfl ?_)
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have he :b+e-j=b+(e-j) := by omega
    simp only [neg_pow x j,C_mul,C_pow,C_neg,C_1,C_eq_natCast,he,pow_add]
    ac_rfl
  have hh:=congrArg (fun f :zM1 F=>f.coeff m) hp
  simpa only [finsetSum_coeff,coeff_mul_C] using hh
private theorem expand_geom (k b e m:ℕ) :
    (Xg^k*V^b).coeff m =
      ∑ j∈z4x (e+1),(Xg^(k+j)*V^(b+e-j)).coeff m*amp e j :=
  expand (F:=ao) k b e m
private theorem pieces_full (a :Shape) (q d h:ℕ) :
    cutMatrix a q d h = ∑ n∈z4x (q+1),dO a q d h n:= by
  classical
  ext r s
  rw [Matrix.sum_apply]
  by_cases hr :derivativeIndex r<h
  · by_cases hs :d≤ s.1.val+s.2.val
    · by_cases hc:r.1.val≤ s.1.val
      · let c:=s.1.val
        let e :=q - c - s.2.val
        have hq:=(cp3 s).2
        have hcq:q+1=c+(q-c+1) := by dsimp [c]; omega
        have hbe :s.2.val+e=q-c:= by dsimp [e,c]; omega
        have hc' : r.1.val≤ c:=hc
        calc
          _=(Xg^(c-r.1.val)*V^s.2.val).coeff r.2.val *
              (c.choose r.1.val :ao) := by
            simp only [cutMatrix,hs,hr,hc,true_and,coeff_X_pow_mul',
              coeff_one_add_X_pow,c]
            split_ifs <;> simp [mul_comm]
          _ = ∑ j∈z4x (e+1),dO a q d h (c+j) r s := by
            rw [expand_geom (e :=e),Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j hj
            have hj' := Finset.mem_range.mp hj
            have hij:c+j-r.1.val=c-r.1.val+j:= by omega
            have hqj:q-(c+j)=s.2.val+e-j:= by omega
            have hcs :s.1.val≤ c+j:= by dsimp [c]; omega
            simp only [dO,hr,hs,hc,hcs,and_self,ite_true,Fg,hij,hqj,
              show c+j-s.1.val=j by dsimp [c]; omega]
            change _ = _ *(c.choose r.1.val :ao)*amp e j
            ac_rfl
          _ = _:= by
            have hz : (∑ n∈z4x c,dO a q d h n r s)=0:= by
              apply Finset.sum_eq_zero
              intro n hn
              exact ite_eq_right (fun hx=>(Nat.not_le_of_lt (Finset.mem_range.mp hn)) hx.2.2.2)
            rw [hcq,Finset.sum_range_add (fun n=>dO a q d h n r s) c (q-c+1),hz,zero_add]
            apply zVG (znF (by dsimp [e]; omega))
            intro j _ hj
            have hj' : e<j:= by simp only [zIR] at hj; omega
            simp [dO,amp,show c+j-s.1.val=j by dsimp [c]; omega,
              show q-s.1.val-s.2.val=e from rfl,Nat.choose_eq_zero_of_lt hj']
      · simp [cutMatrix,dO,hc]
    · simp [cutMatrix,dO,hs]
  · simp [cutMatrix,dO,hr]
private theorem coeff_zero {q n c b:ℕ} (h:b<n-c) :Fg q n c b=0:= by
  simp [Fg,coeff_X_pow_mul',Nat.not_le_of_lt h]
private theorem pieces_truncated (a :Shape) (q d h:ℕ)
    (hq:q+a.t≤a.j) (hd:d≤q) :
    cutMatrix a q d h =
      ∑ n∈z4x (min (q+1) (min (a.j+1-d) h)),dO a q d h n:= by
  rw [pieces_full]
  symm
  apply zVG (znF (min_le_left _ _))
  intro n hn hn'
  have hnq:=Finset.mem_range.mp hn
  simp only [zIR,lt_min_iff] at hn'
  ext r s
  by_cases hx :derivativeIndex r<h∧d≤ s.1.val+s.2.val ∧
      r.1.val≤ s.1.val∧s.1.val≤n
  · rw [dO,ite_eq_left hx,Matrix.zero_apply]
    by_cases hnh:h≤n
    · have hr :=hx.1
      unfold derivativeIndex at hr
      rw [coeff_zero (by omega),zero_mul,zero_mul]
    · have hs :=(cp3 s).1
      have ha :q-s.1.val-s.2.val<n-s.1.val := by omega
      simp [amp,Nat.choose_eq_zero_of_lt ha]
  · exact ite_eq_right hx
private def cols (a :Shape) (q d n:ℕ) :=min a.t n+1-(n-(q-d))
private def rows (a :Shape) (h n:ℕ) :=min a.t (min n (h-1-n))+1
private theorem pick (N k :ℕ) (p:Prop) [Decidable p] (f :ℕ→ao) :
    (∑ i:Fin N,if p∧i.val=k then f i.val else 0) =
      if p∧k<N then f k else 0:= by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i=>if p∧i=k then f i else 0)]
  by_cases hp:p <;> simp [hp,Finset.sum_ite_eq',zIR]
private theorem rank_piece (a :Shape) (q d h n:ℕ) :
    (dO a q d h n).rank≤ min (cols a q d n) (rows a h n) := by
  classical
  let l:=n-(q-d)
  let A:Matrix (Slot a q) (Fin (rows a h n)) ao:= fun r j =>
    if derivativeIndex r<h∧j.val=r.1.val then Fg q n r.1.val r.2.val else 0
  let B:Matrix (Fin (rows a h n)) (Fin (cols a q d n)) ao:= fun j i =>
    ((l+i.val).choose j.val :ao)
  let D:Matrix (Fin (cols a q d n)) (Slot a q) ao:= fun i s =>
    if (d≤ s.1.val+s.2.val∧l≤ s.1.val)∧i.val=s.1.val-l then
      amp (q-s.1.val-s.2.val) (n-s.1.val)
    else 0
  have he :dO a q d h n=A*(B*D) := by
    ext r s
    have hmul (j:Fin (rows a h n)) : (B*D) j s =
        if (d≤ s.1.val+s.2.val∧l≤ s.1.val)∧s.1.val-l<cols a q d n then
          ((l+(s.1.val-l)).choose j.val :ao) *
            amp (q-s.1.val-s.2.val) (n-s.1.val)
        else 0:= by
      rw [Matrix.mul_apply]
      simp only [B,D,mul_ite,mul_zero]
      exact pick (cols a q d n) (s.1.val-l) (d≤ s.1.val+s.2.val∧l≤ s.1.val)
        (fun i=>((l+i).choose j.val :ao)*amp (q-s.1.val-s.2.val) (n-s.1.val))
    have hr :=(cp3 r).1
    have hs :=cp3 s
    have hx : (d≤ s.1.val+s.2.val∧l≤ s.1.val)∧s.1.val-l<cols a q d n ↔
        d≤ s.1.val+s.2.val∧l≤ s.1.val∧s.1.val≤n:= by dsimp [cols]; omega
    rw [Matrix.mul_apply]
    simp only [A,ite_mul,zero_mul,hmul]
    rw [pick _ _ _ (fun j=>Fg q n r.1.val r.2.val *
      (if (d≤ s.1.val+s.2.val∧l≤ s.1.val)∧s.1.val-l<cols a q d n then
        ((l+(s.1.val-l)).choose j:ao)*amp (q-s.1.val-s.2.val) (n-s.1.val) else 0))]
    · simp only [hx,dO]
      by_cases hd:derivativeIndex r<h
      · by_cases hw:d≤ s.1.val+s.2.val
        · by_cases hn:s.1.val≤n
          · by_cases hl:l≤ s.1.val
            · have hl' : l+(s.1.val-l)=s.1.val := by omega
              by_cases hc:r.1.val≤ s.1.val
              · by_cases ht:r.1.val< rows a h n
                · simp [hd,hw,hn,hl,hl',hc,ht,mul_assoc]
                · have hb:r.2.val<n-r.1.val := by
                    unfold derivativeIndex at hd
                    dsimp [rows] at ht
                    omega
                  simp [hd,hw,hn,hc,ht,coeff_zero hb]
              · simp [hd,hw,hn,hl,hl',hc,Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hc)]
            · have ha :q-s.1.val-s.2.val<n-s.1.val := by dsimp [l] at hl; omega
              simp [hd,hw,hn,hl,amp,Nat.choose_eq_zero_of_lt ha]
          · simp [hd,hw,hn]
        · simp [hd,hw]
      · simp [hd]
  rw [he]
  apply le_min
  · exact (rank_mul_le_right _ _).trans ((rank_mul_le_left _ _).trans (rank_le_width _))
  · exact (rank_mul_le_left _ _).trans (by simpa using rank_le_card_width A)
private theorem rank_sum {ι:Type} {m:Type} [Fintype m]
    (S:Finset ι) (M:ι→Matrix m m ao) :
    (∑ i∈S,M i).rank ≤ ∑ i∈S,(M i).rank := by
  classical
  let P (i:ι) :=LinearMap.range (M i).mulVecLin
  have hr :LinearMap.range (∑ i∈S,M i).mulVecLin≤S.sup P:= by
    rintro v ⟨x,rfl⟩
    simp only [Matrix.mulVecLin_apply,Matrix.sum_mulVec]
    exact Submodule.sum_mem _ (fun i hi=>Finset.le_sup (f :=P) hi ⟨x,rfl⟩)
  exact (Submodule.finrank_mono hr).trans (qA0rFHd.b3b S P)
theorem rankCut_le_cap (a :Shape) (q d h:ℕ) (hq:q+a.t≤a.j) (hd:d≤q) :
    rankCut a q d h≤ cap a q d h:= by
  rw [rankCut,pieces_truncated a q d h hq hd,cap,sumN_eq]
  refine (rank_sum _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn' := (lt_min_iff.mp (Finset.mem_range.mp hn)).1
  have htop:min a.t (min n (a.j-n))=min a.t n:= by omega
  simpa only [htop,cols,rows] using rank_piece a q d h n
end
end qY7pQzb
end
