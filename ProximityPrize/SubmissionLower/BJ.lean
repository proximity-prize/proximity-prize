import ProximityPrize.SubmissionLower.ZNc0LBb
set_option Elab.async false
set_option maxRecDepth 4000
open _root_ renaming AddMonoidAlgebra.coeff_zero→ oq,AlgEquiv.apply_symm_apply→qy,AlgEquiv.symm_apply_apply→qx,Algebra.algebraMap→cy,Finsupp.optionElim_apply_none→qm,Finsupp.some_optionElim→sS,Finsupp.sumFinsuppAddEquivProdFinsupp→lz,Finsupp.zero_apply→ oj,FractionRing→pQ,IsFractionRing.injective→nI,Module.finrank→ oY,MvPolynomial→ ox,MvPolynomial.C→mD,MvPolynomial.coeff_C_mul→p9,MvPolynomial.coeff_map→qM,MvPolynomial.eval→ oy,MvPolynomial.map→pL,MvPolynomial.map_C→th,MvPolynomial.map_injective→qJ,MvPolynomial.mem_support_iff→t3,MvPolynomial.optionEquivLeft→lV,MvPolynomial.optionEquivLeft_coeff_some_coeff_none→qz,MvPolynomial.optionEquivRight→pz,MvPolynomial.sumRingEquiv→p5,MvPolynomial.totalDegree→sI,MvPolynomial.totalDegree_finsetSum_le→qU,MvPolynomial.uniqueAlgEquiv→p6,Nat.le_of_not_gt→p7,Polynomial→aU,Polynomial.X→c9,Polynomial.coeff_eq_zero_of_natDegree_lt→ oK,Polynomial.coeff_zero→nX,Polynomial.ext→pU,Polynomial.mapRingHom→sH,Polynomial.sum_def→pC,RingHom.comp_apply→ oD,congrArg→n5,cu.Equation→lI,cu.triangle→lJ,map_mul→nq,map_ne_zero_iff→ oZ,map_pow→ oz,map_zero→ ov,mem_nonZeroDivisors_iff_ne_zero→t4,mul_ne_zero→pG
set_option autoImplicit true
section
namespace bAr
noncomputable section
open cu (L triangle)
open MvPolynomial (restrictBidegree mem_restrictBidegree)
abbrev i5:=ox (Fin 2) L
abbrev ax4 :=aU i5
private abbrev atZ (u:ℕ) := {m:Fin 2 →₀ ℕ // m.degree≤u}
private theorem cFD (u:ℕ) : (u+Nat.card (Fin 2)).choose (Nat.card (Fin 2)) =
  triangle u:= by
 simp [Nat.choose_two_right,lJ,Nat.mul_comm (u+2)]
private theorem dMu (H F:ax4) {r v :ℕ}
  (hH : ∀ a,(H.coeff a).totalDegree≤ r)
  (hF : ∀ a,(F.coeff a).totalDegree≤v) (a :ℕ) :
  ((H*F).coeff a).totalDegree≤v+r := by
 rw [Polynomial.coeff_mul]
 apply qU
 intro ij _
 exact (MvPolynomial.totalDegree_mul _ _).trans (by
  simpa only [Nat.add_comm v r] using Nat.add_le_add (hH ij.1) (hF ij.2))
theorem d4u (e n t v r :ℕ) (ht:t<n)
    (hs : (e+1)*t*lJ (v+r)<n*lJ r)
    (F:ℕ→ax4) (hF : ∀ j a,((F j).coeff a).totalDegree≤v) :
    ∃ H :ax4,H≠0∧H.natDegree<n ∧
      (∀ j a,((H*F j).coeff a).totalDegree≤v+r) ∧
      ∀ j≤e,∀ a,n-t≤a→a<n→(H*F j).coeff a=0:= by
  classical
  let V:=restrictBidegree (Fin 2) L (n-1) r
  let I:=Fin (e+1)×Fin t×atZ (v+r)
  let:Finite (atZ (v+r)) :=(Finsupp.finite_of_degree_le (v+r)).to_subtype
  let:Fintype I:=Fintype.ofFinite I
  let view:V →ₗ[L] ax4 :=(lV L (Fin 2)).toLinearMap.comp V.subtype
  let M:V →ₗ[L] (I→L) :=LinearMap.pi fun i =>
    (MvPolynomial.lcoeff L i.2.2.val).comp
      (((Polynomial.lcoeff (R:=i5) (n-t+i.2.1.val)).restrictScalars L).comp
        ((LinearMap.mulRight L (F i.1.val)).comp view))
  have hV:oY L V=n*lJ r := by
    dsimp only [V]
    rw [MvPolynomial.finrank_restrictBidegree,cFD,show n-1+1=n by omega]
  have hIndex :Nat.card (atZ (v+r))=lJ (v+r) := calc
    _ = {m:Fin 2 →₀ ℕ | m.degree≤v+r}.ncard:=rfl
    _ = _:=(Finsupp.ncard_setOf_degree_le _ _).trans (cFD _)
  have hI:oY L (I→L)=(e+1)*t*lJ (v+r) := by
    rw [Module.finrank_fintype_fun_eq_card,← Nat.card_eq_fintype_card]
    dsimp only [I]
    rw [Nat.card_prod,Nat.card_prod,Nat.card_fin,Nat.card_fin,hIndex,Nat.mul_assoc]
  have hd:oY L (I→L)<oY L V:= by rwa [hI,hV]
  obtain ⟨h,hker,hn⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (M.ker_ne_bot_of_finrank_lt hd)
  let H :=view h
  have hH0:H≠0:= by
    intro hz
    apply hn
    apply Subtype.ext
    apply (lV L (Fin 2)).injective
    change H=(lV L (Fin 2)) 0
    rwa [ov]
  have hbox :=mem_restrictBidegree.mp h.property
  have hcoeff (a :ℕ) (m:Fin 2 →₀ ℕ) (hm:m∈(H.coeff a).support) :
      a≤n-1∧m.degree≤ r := by
    have hb:=hbox _ ((MvPolynomial.mem_support_coeff_optionEquivLeft L).mp hm)
    simpa only [qm,sS] using hb
  have hdH :H.natDegree<n:= by
    suffices H.natDegree≤n-1 by omega
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro a ha
    by_contra hna
    obtain ⟨m,hm⟩:=MvPolynomial.support_nonempty.mpr hna
    exact ha.not_ge (hcoeff a m hm).1
  have hsH (a :ℕ) : (H.coeff a).totalDegree≤ r := by
    exact Finset.sup_le fun m hm=>(hcoeff a m hm).2
  have hdeg (j a :ℕ) :=dMu H (F j) hsH (hF j) a
  refine ⟨H,hH0,hdH,hdeg,?_⟩
  intro j hj a hlow hhigh
  by_contra hz
  obtain ⟨m,hm⟩:=MvPolynomial.support_nonempty.mpr hz
  have hmdeg:m.degree≤v+r :=(MvPolynomial.le_totalDegree hm).trans (hdeg j a)
  let i:I:=(⟨j,by omega⟩,⟨a-(n-t),by omega⟩,⟨m,hmdeg⟩)
  have hv :=congrFun (LinearMap.mem_ker.mp hker) i
  change ((H*F j).coeff (n-t+(a-(n-t)))).coeff m=0 at hv
  rw [show n-t+(a-(n-t))=a by omega] at hv
  exact MvPolynomial.mem_support_iff.mp hm hv
end
end bAr
end
section
namespace Y3
noncomputable section
open Polynomial

open cu (L FX aZ Equation)
abbrev JS:=ox (Fin 2) (aU L)
abbrev Dg:=aU JS
def embed:Dg →+* Equation :=
 sH (pL (cy (aU L) FX))
def constant:FX →+* Equation :=Polynomial.C.comp mD
def aka :aU L →+* Dg:=Polynomial.C.comp mD
def ek :lI →+* aU (pQ aZ) :=
 sH (cy aZ (pQ aZ))
def aLS (Q:Dg) (v :ℕ) :Prop :=
 ∀ j,(Q.coeff j).totalDegree≤v
def bjn (Q:Dg) :Prop :=
 ∃ (j:ℕ) (m:Fin 2 →₀ ℕ),((Q.coeff j).coeff m).coeff 0≠0
@[simp] theorem b1t (h:aU L) :
   embed (aka h)=constant (cy (aU L) FX h) := by
  simp [embed,aka,constant,Polynomial.map_C,th]
end
end Y3
end
section
namespace Y3
noncomputable section
open Polynomial
open cu (L FX aZ vm)
open scoped nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem dLr (f :lI) :
  ∃ (Q:Dg) (a :FX),a≠0∧embed Q=constant a*f := by
 let Ek :=(aU L)⁰.map (mD:aU L →+* JS)
 let Q:Dg:=IsLocalization.integerNormalization Ek f
 obtain ⟨b,hb,hQ⟩:=IsLocalization.integerNormalization_spec Ek f
 obtain ⟨a,ha,rfl⟩:=hb
 let a' := cy (aU L) FX a
 refine ⟨Q,a',(oZ _ (nI _ _)).mpr (nonZeroDivisors.ne_zero ha),?_⟩
 rw [← algebraMap_smul aZ,MvPolynomial.algebraMap_def,th] at hQ
 change embed Q=(mD a' : aZ)•f at hQ
 simpa only [constant,oD,Polynomial.smul_eq_C_mul] using hQ
private theorem fWf (Q:Dg) (hQ:Q≠0) :
  ∃ (n:ℕ) (F:Dg),Q=aka (c9 ^n)*F∧bjn F:= by
 classical
 let occupied (n:ℕ) :Prop := ∃ (j:ℕ) (m:Fin 2 →₀ ℕ),
  ((Q.coeff j).coeff m).coeff n≠0
 have hex : ∃ n,occupied n:= by
  by_contra! h
  apply hQ
  apply pU
  intro j
  apply MvPolynomial.ext
  intro m
  apply pU
  intro n
  simp only [nX ,oq,oj]
  by_contra hn
  exact h n ⟨j,m,hn⟩
 let n:=Nat.find hex
 have hdiv :aka (c9 ^n)∣Q:= by
  change C (mD (c9 ^n))∣Q
  rw [C_dvd_iff_dvd_coeff]
  intro j
  rw [MvPolynomial.C_dvd_iff_dvd_coeff]
  intro m
  apply X_pow_dvd_iff.mpr
  intro k hk
  by_contra h
  exact (Nat.find_min hex hk) ⟨j,m,h⟩
 obtain ⟨F,hF⟩:=hdiv
 obtain ⟨j,m,hcoeff⟩:=Nat.find_spec hex
 refine ⟨n,F,hF,j,m,?_⟩
 change ((Q.coeff j).coeff m).coeff n≠0 at hcoeff
 rw [hF] at hcoeff
 simpa only [aka,oD,coeff_C_mul,p9,
  coeff_X_pow_mul',le_refl,ite_true,Nat.sub_self] using hcoeff
private theorem fTY {f :lI} {a :FX} {Q:Dg} {e v :ℕ}
   (he :f.natDegree≤e) (hs :vm f v) (hQ:embed Q=constant a*f) :
   Q.natDegree≤e∧aLS Q v := by
 have hsupp (j:ℕ) (m:Fin 2 →₀ ℕ) (h: (Q.coeff j).coeff m≠0) :
     (f.coeff j).coeff m≠0:= by
   have hcoeff :=n5 (fun U:lI=>(U.coeff j).coeff m) hQ
   simp only [embed,coe_mapRingHom,coeff_map,qM,constant,
     oD,coeff_C_mul,p9] at hcoeff
   intro hz
   rw [hz,mul_zero] at hcoeff
   exact h ((nI (aU L) FX) (hcoeff.trans (ov _).symm))
 refine ⟨natDegree_le_iff_coeff_eq_zero.mpr ?_,?_⟩
 · intro j hj
   apply MvPolynomial.ext
   intro m
   simp only [oq,oj]
   by_contra h
   exact hsupp j m h (by simp [oK (lt_of_le_of_lt he hj)])
 · intro j
   rw [sI]
   exact Finset.sup_le fun m hm=>(Finset.le_sup (f := fun n=>n.sum fun _ j=>j)
     (MvPolynomial.mem_support_iff.mpr (hsupp j m (MvPolynomial.mem_support_iff.mp hm)))).trans (hs j)
theorem normalize (f :lI) (e v :ℕ) (hf :f≠0)
   (he :f.natDegree≤e) (hv :vm f v) :
   ∃ (Q:Dg) (a :FX),a≠0∧embed Q=constant a*f ∧
     Q.natDegree≤e∧aLS Q v∧bjn Q:= by
 obtain ⟨D,a,ha,hD⟩:=dLr f
 have hconst:constant a≠0:= by simpa [constant] using ha
 have hD0:D ≠0:= by
   intro h
   rw [h,ov] at hD
   exact pG hconst hf hD.symm
 obtain ⟨n,Q,hQ,hterm⟩:=fWf D hD0
 let s :=cy (aU L) FX (c9 ^n)
 have hs :s≠0:=(oZ _ (nI _ _)).mpr
   (pow_ne_zero _ X_ne_zero)
 rw [hQ,nq,b1t] at hD
 change constant s*embed Q=constant a*f at hD
 have h' : embed Q=constant (s⁻¹*a)*f := calc
   embed Q=constant s⁻¹*(constant s*embed Q) := by
     rw [← mul_assoc,← nq,inv_mul_cancel₀ hs,map_one,one_mul]
   _=constant (s⁻¹*a)*f := by rw [hD,nq,mul_assoc]
 obtain ⟨he',hv'⟩:=fTY he hv h'
 exact ⟨Q,s⁻¹*a,pG (inv_ne_zero hs) ha,h',he',hv',hterm⟩
end
end Y3
end
section
namespace Y3
noncomputable section
open Polynomial
open P2 (K p)
open cu (L FX yq kr j9 jz)
open scoped BigOperators
private def azZ (t:Fin 2→L) (S:K[X]) :Dg →+* aU L :=
 eval₂RingHom (oy (C ∘ t)) (j9 S)
private theorem eza (t:Fin 2→L) (S:K[X]) (Q:Dg) :
  let ι:=cy (aU L) FX
  ι (azZ t S Q)=(embed Q).eval₂ (oy (ι ∘ (C ∘ t))) (kr S) := by
 let ι:=cy (aU L) FX
 change ι (Q.eval₂ (oy (C ∘ t)) (j9 S)) =
  (Q.map (pL ι)).eval₂ (oy (ι ∘ (C ∘ t))) (ι (j9 S))
 rw [eval₂_map,eval₂_eq_sum,eval₂_eq_sum,pC,pC,map_sum]
 apply Finset.sum_congr rfl
 intro j _
 rw [nq,oz ,MvPolynomial.map_eval]
 rfl
private def abn (z :K) (n:ℕ) :Fin 2→L :=
 ![cy K L z,(cy K L z)^n]
private theorem eze (z :K) (n:ℕ) :
   cy (aU L) FX ∘ (C ∘ abn z n) =
    ![jz z,(jz z)^n] := by
 funext i
 fin_cases i
 · rfl
 · exact oz ((cy (aU L) FX).comp (C:L →+* aU L))
    (cy K L z) n
private theorem cZx (z :K) (S:K[X]) (Q:Dg) :
  cy (aU L) FX (azZ (abn z p) S Q)=yq (embed Q) z S:= by
 have h:=eza (abn z p) S Q
 dsimp only at h
 rwa [eze] at h
private theorem fTI (t:Fin 2→L) (S:K[X]) (D:aU L) :
  azZ t S (aka D)=D:= by
 simp [azZ,aka]
private theorem gK4 {n:ℕ} {Q G B:Dg} {H :JS}
  (t:Fin 2→L) (S:K[X]) (hq:azZ t S Q=0)
  (heq :C H*Q=G+aka (c9 ^n)*B)
  (hdeg: (azZ t S G).natDegree<n) :azZ t S G=0:= by
 have hrel :=n5 (azZ t S) heq
 rw [nq,map_add,nq,fTI,hq,mul_zero] at hrel
 have hdvd: (c9:aU L)^n∣azZ t S G :=
  ⟨-azZ t S B,by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hrel.symm⟩
 by_contra hn
 have hle :=natDegree_le_of_dvd hdvd hn
 rw [natDegree_X_pow] at hle
 exact hdeg.not_ge hle
end
end Y3
end
section
namespace Y3
noncomputable section
open Polynomial


open cu (vm)
open scoped BigOperators
private theorem fXn {f g:lI} {u v :ℕ}
    (hf :vm f u) (hg:vm g v) :
    (f.resultant g).totalDegree≤f.natDegree*v+g.natDegree*u:= by
  classical
  let m:=f.natDegree
  let n:=g.natDegree
  let A:=sylvester f g m n
  let cap:Fin (m+n)→ℕ:= fun i=>i.addCases (fun _=>v) (fun _=>u)
  have hentry (i j:Fin (m+n)) : (A i j).totalDegree≤ cap j:= by
    refine Fin.addCases ?_ ?_ j
    · intro a
      simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_left]
      split
      · apply hg
      · simp
    · intro a
      simp only [A,cap,sylvester,Matrix.of_apply,Fin.addCases_right]
      split
      · apply hf
      · simp
  change A.det.totalDegree≤ m*v+n*u
  rw [Matrix.det_apply]
  apply qU
  intro π _
  have hp: (∏ i,A (π i) i).totalDegree≤ m*v+n*u:= by
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    calc
      _ ≤ ∑ i,cap i:=Finset.sum_le_sum fun i _=>hentry (π i) i
      _ = _:= by
        rw [Fin.sum_univ_add]
        simp [cap]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hh | hh <;> simpa [hh] using hp
end
end Y3
end
section
namespace ba5
noncomputable section
open Polynomial
open cu (L FX aZ)
open Y3 (JS Dg embed ek)
open scoped nonZeroDivisors
private abbrev aQ:=pQ aZ
attribute [local instance] MvPolynomial.algebraMvPolynomial
local instance :IsFractionRing JS aQ:= by
  let M:Submonoid JS :=
    (aU L)⁰.map (mD:aU L →+* JS)
  have :IsLocalization M aZ:=MvPolynomial.isLocalization (aU L)⁰ FX
  have hinj:Function.Injective (cy JS aZ) :=
    qJ _ (nI _ _)
  have heq : (aZ⁰).comap (cy JS aZ)=JS⁰:= by
    ext q
    rw [Submonoid.mem_comap,t4 ,
      t4 ,oZ _ hinj]
  rw [IsFractionRing,← heq]
  exact IsLocalization.localization_localization_isLocalization_of_has_all_units M
    (aZ⁰) aQ (fun _ h=>h.mem_nonZeroDivisors)
local instance :StrongNormalizationMonoid JS :=
 UniqueFactorizationMonoid.strongNormalizationMonoid
local instance :IsGCDMonoid JS :=
 nonempty_normalizedGCDMonoid_iff_isGCDMonoid.mp
  ⟨UniqueFactorizationMonoid.toNormalizedGCDMonoid JS⟩
private theorem bIV (Q:Dg) :
  Q.map (cy JS aQ)=ek (embed Q) := by
 rw [IsScalarTower.algebraMap_eq JS aZ aQ]
 exact (Polynomial.map_map _ _ _).symm
theorem efR {Q:Dg} (hi:Irreducible Q)
  (hpos :0<Q.natDegree) :Irreducible (ek (embed Q)) := by
 rw [← bIV]
 exact ((hi.isPrimitive hpos.ne').irreducible_iff_irreducible_map_fraction_map
  (K:=aQ)).mp hi
theorem efO {Q G:Dg} (hp:Q.IsPrimitive)
  (hd:ek (embed Q)∣ek (embed G)) :Q∣G:= by
 rw [← bIV,← bIV] at hd
 exact hp.dvd_of_fraction_map_dvd_fraction_map hd
theorem egd {Q:Dg} (hQ:Q≠0)
  (hz :Q.natDegree=0) :IsUnit (ek (embed Q)) := by
 have he :=eq_C_of_natDegree_eq_zero hz
 have hc:Q.coeff 0≠0:= by
  intro h
  apply hQ
  rwa [h,C_0] at he
 have hu:IsUnit (cy JS aQ (Q.coeff 0)) :=
  ((oZ _ (nI JS aQ)).mpr hc).isUnit
 rw [← bIV,he,map_C]
 exact hu.map Polynomial.C
theorem d09 (Q:Dg) : (embed Q).natDegree= Q.natDegree :=
 natDegree_map_eq_of_injective (qJ _ (nI _ _)) Q
end
end ba5
end
section
namespace ba5
noncomputable section
open Polynomial
open cu (L)
open Y3 (JS Dg)
private abbrev Vars :=Option (Fin 2 ⊕ Unit)
private def bg6:ox (Fin 2 ⊕ Unit) L ≃+* JS :=
 (p5 L (Fin 2) Unit).trans
   (MvPolynomial.mapEquiv _ (p6 L Unit).toRingEquiv)
private def expand:Dg ≃+* ox Vars L :=
 (Polynomial.mapEquiv bg6.symm).trans
   (lV L (Fin 2 ⊕ Unit)).toRingEquiv.symm
private theorem dMz (F:ox (Fin 2 ⊕ Unit) L)
    (v : (Fin 2 ⊕ Unit) →₀ ℕ) :
    ((bg6 F).coeff (lz v).1).coeff
        ((lz v).2 ())=F.coeff v := by
  rw [show bg6 F=pL (p6 L Unit).toRingHom
      (p5 L (Fin 2) Unit F) from rfl,
    qM]
  change ((p6 L Unit)
    ((p5 L (Fin 2) Unit F).coeff
      (lz v).1)).coeff _ = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv,
    ← Finsupp.unique_single (lz v).2]
  change ((AddMonoidAlgebra.mapDomainRingEquiv L lz F).coeff)
      (lz v)= _
  simp [Finsupp.equivMapDomain_apply]
private theorem coeff_expand (F:Dg) (v :Vars →₀ ℕ) :
    (expand F).coeff v =
      ((F.coeff (v none)).coeff (lz v.some).1).coeff
        ((lz v.some).2 ()) := by
  have he : (lV L (Fin 2 ⊕ Unit)) (expand F) =
      F.map bg6.symm.toRingHom :=
    (lV L (Fin 2 ⊕ Unit)).toRingEquiv.apply_symm_apply _
  rw [← qz L (Fin 2 ⊕ Unit),he,
    Polynomial.coeff_map]
  change (bg6.symm (F.coeff (v none))).coeff v.some= _
  simpa only [RingEquiv.apply_symm_apply] using
    (dMz (bg6.symm (F.coeff (v none))) v.some).symm
private def weights (d:ℕ) :Vars→ℕ
 | none=>d
 | some (.inl _)=>0
 | some (.inr _)=>1
private theorem c0Q (d:ℕ) (v :Vars →₀ ℕ) :
  Finsupp.weight (weights d) v=v (some (.inr ()))+v none*d:= by
 rw [Finsupp.weight_eq_sum,Fintype.sum_option,Fintype.sum_sum_type]
 simp [weights,smul_eq_mul,Nat.add_comm]
end
end ba5
end
section
namespace Y3
noncomputable section
open Polynomial


open cu (vm)
open Qt (Qc acG)
private theorem cN9 {g k f :lI} {v :ℕ}
  (hf :f≠0) (hv :vm f v) (heq :f=g*k) :vm g v∧vm k v := by
 have hne :g*k≠0:=heq ▸ hf
 have h:=(Qc f v).mpr hv
 rw [heq,acG (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne)] at h
 exact ⟨(Qc g v).mp ((Nat.le_add_right _ _).trans h),
  (Qc k v).mp ((Nat.le_add_left _ _).trans h)⟩
end
end Y3
end
section
namespace bAr
noncomputable section
open Polynomial

open Y3 (JS Dg aLS bjn aka)
open cu (L)

private def swap:JS ≃ₐ[L] ax4 :=
 (pz L (Fin 2)).symm.trans (lV L (Fin 2))
private theorem bOH (P:JS) (a :ℕ) (m:Fin 2 →₀ ℕ) :
  ((swap P).coeff a).coeff m=(P.coeff m).coeff a := by
 obtain ⟨q,rfl⟩:=(pz L (Fin 2)).surjective P
 simp only [swap,AlgEquiv.trans_apply,qx ,
  MvPolynomial.optionEquivRight_coeff_coeff]
 simpa only [qm,sS] using
  (qz L (Fin 2) (m.optionElim a) q)
private theorem gxQ (n:ℕ) :
   swap (mD ((c9:aU L)^n))=(c9:ax4)^n:= by
 rw [oz ,oz]
 congr 1
 rw [← MvPolynomial.optionEquivRight_X_none]
 change lV L (Fin 2)
   ((pz L (Fin 2)).symm (pz L (Fin 2) (MvPolynomial.X none))) =
     c9
 rw [qx ,MvPolynomial.optionEquivLeft_X_none]
private theorem dcB (P:JS) (u:ℕ) :
   P.totalDegree≤u ↔ ∀ a,((swap P).coeff a).totalDegree≤u:= by
 simp only [sI,Finset.sup_le_iff]
 constructor
 · intro h a m hm
   apply h m
   rw [t3] at hm ⊢
   intro hz
   exact hm (by rw [bOH,hz,nX])
 · intro h m hm
   obtain ⟨a,ha⟩:=Polynomial.support_nonempty.mpr (MvPolynomial.mem_support_iff.mp hm)
   apply h a m
   rwa [t3 ,bOH,← Polynomial.mem_support_iff]
private def assemble (e :ℕ) (F:ℕ→ax4) :Dg :=
 ∑ j∈Finset.range (e+1),monomial j (swap.symm (F j))
private theorem bnj (e :ℕ) (F:ℕ→ax4) (j:ℕ) :
  (assemble e F).coeff j=if j≤e then swap.symm (F j) else 0:= by
 classical
 simp only [assemble,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq',Finset.mem_range,
  Nat.lt_succ_iff]
private theorem bXU {n a :ℕ} (F:ax4) (ha :a<n) :
  (F %ₘ (c9^n)).coeff a=F.coeff a := by
 have h:=n5 (fun P:ax4=>P.coeff a) (modByMonic_add_div F (c9^n))
 simpa only [coeff_add,coeff_X_pow_mul',ite_eq_right (Nat.not_le_of_gt ha),add_zero] using h
private theorem fV9 {n:ℕ} {H F:ax4} (hH :H≠0)
  (hd:H.natDegree<n) (hF:F.coeff 0≠0) :
  H*F %ₘ (c9^n)≠0:= by
 have hF0:F≠0:= by intro h; exact hF (by rw [h,nX])
 have htrail: (H*F).natTrailingDegree=H.natTrailingDegree := by
  rw [natTrailingDegree_mul hH hF0,natTrailingDegree_eq_zero.mpr (Or.inr hF),Nat.add_zero]
 have ha : (H*F).natTrailingDegree<n:= by
  rw [htrail]
  exact H.natTrailingDegree_le_natDegree.trans_lt hd
 intro h
 have hs :=bXU (H*F) ha
 rw [h,nX] at hs
 exact (pG hH hF0) (coeff_natTrailingDegree_eq_zero.mp hs.symm)
private theorem compress (e d v r n:ℕ) (hed:e*d<n)
    (hs : (e+1)*e*d*lJ (v+r)<n*lJ r) (Q:Dg)
    (hQe :Q.natDegree≤e) (hQv :aLS Q v) (hQ0:bjn Q) :
    ∃ (H :JS) (G B:Dg),
      C H*Q=G+aka (c9 ^n)*B∧G≠0 ∧
        G.natDegree≤e∧aLS G (v+r) ∧
        ∀ j m,(G.coeff j).coeff m≠0→((G.coeff j).coeff m).natDegree+j*d<n:= by
  classical
  let F:= fun j=>swap (Q.coeff j)
  have hF (j a :ℕ) : ((F j).coeff a).totalDegree≤v :=
    (dcB (Q.coeff j) v).mp (hQv j) a
  obtain ⟨H,hH,hHdeg,hprod,htop⟩:=d4u e n (e*d) v r hed
    (by simpa only [Nat.mul_assoc] using hs) F hF
  let T:= fun j=>H*F j %ₘ (c9^n)
  let J:= fun j=>H*F j /ₘ (c9^n)
  have hT (j:ℕ) : (T j).natDegree<n:= by
    have hx : ((c9:ax4)^n)≠1 := by
      intro h
      have hn:=n5 Polynomial.natDegree h
      rw [natDegree_X_pow,natDegree_one] at hn
      omega
    simpa only [natDegree_X_pow] using natDegree_modByMonic_lt (H*F j) (monic_X_pow n) hx
  have hT0 (j a :ℕ) (hj:j≤e) (ha :n-e*d≤a) : (T j).coeff a=0:= by
    by_cases han:a<n
    · exact (bXU (H*F j) han).trans (htop j hj a ha han)
    · exact oK ((hT j).trans_le (p7 han))
  refine ⟨swap.symm H,assemble e T,assemble e J,?_,?_,?_,?_,?_⟩
  · apply pU
    intro j
    simp only [aka,oD,coeff_add,coeff_C_mul,bnj]
    by_cases hj:j≤e
    · simp only [hj,ite_true]
      apply swap.injective
      simp only [map_add,nq,qy ,gxQ]
      exact (modByMonic_add_div (H*F j) (c9^n)).symm
    · simp only [hj,ite_false,oK (hQe.trans_lt (Nat.lt_of_not_ge hj)),
        mul_zero,add_zero]
  · obtain ⟨j,m,hm⟩:=hQ0
    have hj:j≤e := by
      apply le_trans (le_natDegree_of_ne_zero ?_) hQe
      intro hz
      exact hm (by simp only [hz,oq,oj,nX])
    have hf0: (F j).coeff 0≠0:= by
      intro hz
      apply hm
      rw [← bOH,show swap (Q.coeff j)=F j from rfl,hz]
      simp only [oq,oj]
    intro hz
    have h:=n5 (fun G:Dg=>G.coeff j) hz
    rw [bnj,ite_eq_left hj,nX] at h
    exact fV9 hH hHdeg hf0 (swap.symm.injective (by rwa [ov]))
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun j hj=> by rw [bnj,ite_eq_right hj.not_ge]
  · intro j
    rw [bnj]
    split_ifs with hj
    · apply (dcB _ _).mpr
      rw [qy]
      intro a
      by_cases ha :a<n
      · exact (bXU (H*F j) ha).symm ▸ hprod j a
      · rw [oK ((hT j).trans_le (p7 ha))]
        simp
    · simp
  · intro j m hm
    rw [bnj] at hm ⊢
    split_ifs at hm ⊢ with hj
    · let D:=(swap.symm (T j)).coeff m
      have ha :D.natDegree<n-e*d:= by
        by_contra hn
        have hz :=hT0 j D.natDegree hj (p7 hn)
        have hc:=n5 (fun s :i5=>s.coeff m) hz
        rw [← show swap (swap.symm (T j))=T j from swap.apply_symm_apply _,bOH,
          oq,oj] at hc
        exact hm (leadingCoeff_eq_zero.mp hc)
      have hle :=Nat.mul_le_mul_right d hj
      change D.natDegree+j*d<n
      omega
    · exact (hm (by simp only [oq,oj])).elim
end
end bAr
end
