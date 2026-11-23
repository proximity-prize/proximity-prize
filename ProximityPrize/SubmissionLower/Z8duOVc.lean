import ProximityPrize.SubmissionLower.Zgvu91a
set_option Elab.async false
open _root_ renaming Algebra → zZE, Module.Finite → zAa, Module.finrank → zsE, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.ext → zXJ, Polynomial.mapRingHom → zhd, Submodule → zpI
section
namespace qX9S3Pd
open cu (L FX)
open Cu
open akS (tu)
open scoped BigOperators
noncomputable abbrev gRK (C₀:sQ) :
 zZE L (oO C₀) :=(zT C₀).toAlgebra
noncomputable def sectionValue {n:ℕ} (B:Ideal (Gc n)) (a :Fin n→FX) :
   tu B :=
 ∑ i,a i•Ideal.Quotient.mk B (MvPolynomial.X (Sum.inr i))
def IndependentPowers {n r :ℕ} (B:Ideal (Gc n)) (a :Fin n→FX)
    (w:Fin r→tu B) :Prop :=
  ∀ m:ℕ,LinearIndependent FX
    (fun ij:Fin (m+1)×Fin r=>sectionValue B a^(ij.1 :ℕ)*w ij.2)
end qX9S3Pd
end
section
namespace qMAQGbd
noncomputable section
open Polynomial
open cu (L)
open quN7Z4a (compressionWidth)
open qBajpRb (aia)
variable {B:Type} [CommRing B] [zZE L B]
private def aIF (n:ℕ) (V:zpI L B) : (Fin n→V) →ₗ[L] B[X] where
 toFun h := ∑ i:Fin n,monomial i.val (h i:B)
 map_add' h k := by
  simp only [Pi.add_apply,Submodule.coe_add,map_add,Finset.sum_add_distrib]
 map_smul' r h:= by
  simp only [Pi.smul_apply,Submodule.coe_smul,RingHom.id_apply,Finset.smul_sum,smul_monomial]
private theorem coeff_multiplier {n:ℕ} {V:zpI L B} (h:Fin n→V) (a :ℕ) :
   (aIF n V h).coeff a=if ha :a<n then (h ⟨a,ha⟩:B) else 0:= by
 classical
 change (∑ i:Fin n,monomial i.val (h i:B)).coeff a= _
 rw [finsetSum_coeff]
 by_cases ha :a<n
 · rw [dite_eq_left ha,Finset.sum_eq_single (⟨a,ha⟩:Fin n)]
   · exact coeff_monomial_same _ _
   · intro i _ hi
     exact coeff_monomial_of_ne _ (fun e=>hi (Fin.ext e.symm))
   · simp
 · rw [dite_eq_right ha]
   exact Finset.sum_eq_zero fun i _=>coeff_monomial_of_ne _ (by
     have hi:=i.isLt
     omega)
private theorem finrank_fun (ι:Type) [Fintype ι] (V:zpI L B) [zAa L V] :
  zsE L (ι→V)=Fintype.card ι*zsE L V:= by
 rw [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
 rfl
private theorem d4u (V W:zpI L B) [zAa L V] [zAa L W]
   (n D g:ℕ) (F:B[X][X])
   (hF : ∀ i a,(F.coeff i).coeff a∈W)
   (hs :aia D g*zsE L (V*W)<n*zsE L V) :
   ∃ H :B[X],H≠0∧H.natDegree<n ∧
     (∀ i a,(H*F.coeff i).coeff a∈V*W) ∧
     ∀ i≤g,∀ a,n-i*D ≤a→a<n→(H*F.coeff i).coeff a=0:= by
 classical
 let:zAa L (V*W:zpI L B) :=
   Module.Finite.of_fg ((Submodule.FG.of_finite (N :=V)).mul (Submodule.FG.of_finite (N :=W)))
 let I:=(i:Fin (g+1))×Fin (i.val*D)
 let view:=aIF n V
 have hV (h:Fin n→V) (a :ℕ) : (view h).coeff a∈V:= by
   rw [coeff_multiplier]
   split_ifs with ha
   · exact (h ⟨a,ha⟩).property
   · exact V.zero_mem
 have hprod (h:Fin n→V) (i a :ℕ) : (view h*F.coeff i).coeff a∈V*W:= by
   rw [coeff_mul]
   exact (V*W).sum_mem fun ij _=>Submodule.mul_mem_mul (hV h ij.1) (hF i ij.2)
 let row (i:I) :=n-i.1.val*D+i.2.val
 let M: (Fin n→V) →ₗ[L] (I→(V*W:zpI L B)) :=LinearMap.pi fun i =>
   (((Polynomial.lcoeff B (row i)).restrictScalars L).comp
     ((LinearMap.mulRight L (F.coeff i.1.val)).comp view)).codRestrict _ (fun h=>hprod h _ _)
 have hI:Fintype.card I=aia D g:= by
   simp [I,aia,Fintype.card_sigma]
 have hd:zsE L (I→(V*W:zpI L B))<zsE L (Fin n→V) := by
   rw [finrank_fun,finrank_fun,hI,Fintype.card_fin]
   exact hs
 obtain ⟨h,hk,hne⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (M.ker_ne_bot_of_finrank_lt hd)
 let H :=view h
 have hH :H≠0:= by
   intro hz
   apply hne
   funext i
   apply Subtype.ext
   change (h i:B)=0
   have hc:=congrArg (fun p:B[X]=>p.coeff i.val) hz
   simpa only [H,view,coeff_multiplier,dite_eq_left i.isLt,coeff_zero] using hc
 have hHdeg:H.natDegree<n:= by
   by_contra! hh
   have hc:H.coeff H.natDegree=0:= by
     simp only [H,view,coeff_multiplier,dite_eq_right hh.not_gt]
   exact hH (leadingCoeff_eq_zero.mp hc)
 refine ⟨H,hH,hHdeg,hprod h,?_⟩
 intro i hi a ha han
 let ix :I:=⟨⟨i,Nat.lt_succ_of_le hi⟩,⟨a-(n-i*D),show a-(n-i*D)< i*D by omega⟩⟩
 have hv :=congrArg (fun x : (V*W:zpI L B)=>(x :B))
   (congrFun (LinearMap.mem_ker.mp hk) ix)
 change (H*F.coeff i).coeff (n-i*D+(a-(n-i*D)))=0 at hv
 rwa [show n-i*D+(a-(n-i*D))=a by omega] at hv
private def assemble (g:ℕ) (F:ℕ→B[X]) :B[X][X] :=
 ∑ j∈Finset.range (g+1),monomial j (F j)
omit [zZE L B] in
private theorem bnj (g:ℕ) (F:ℕ→B[X]) (j:ℕ) :
  (assemble g F).coeff j=if j≤g then F j else 0:= by
 simp only [assemble,finsetSum_coeff,coeff_monomial,Finset.sum_ite_eq',Finset.mem_range,
  Nat.lt_succ_iff]
omit [zZE L B] in
private theorem bXU {n a :ℕ} (P:B[X]) (ha :a<n) :
  (P %ₘ (z7y^n)).coeff a=P.coeff a := by
 have h:=congrArg (fun Q:B[X]=>Q.coeff a) (modByMonic_add_div P (z7y^n))
 simpa only [coeff_add,coeff_X_pow_mul',ite_eq_right (Nat.not_le_of_gt ha),add_zero] using h
private theorem fV9 [IsDomain B] {n:ℕ} {H F:B[X]} (hH :H≠0)
  (hd:H.natDegree<n) (hF:F.coeff 0≠0) :H*F %ₘ (z7y^n)≠0:= by
 have hF0:F≠0:= by intro h; exact hF (by rw [h,coeff_zero])
 have htrail: (H*F).natTrailingDegree=H.natTrailingDegree := by
  rw [natTrailingDegree_mul hH hF0,natTrailingDegree_eq_zero.mpr (Or.inr hF),Nat.add_zero]
 have ha : (H*F).natTrailingDegree<n:= by
  rw [htrail]
  exact H.natTrailingDegree_le_natDegree.trans_lt hd
 intro h
 have hs :=bXU (H*F) ha
 rw [h,coeff_zero] at hs
 exact (mul_ne_zero hH hF0) (coeff_natTrailingDegree_eq_zero.mp hs.symm)
private theorem compress [IsDomain B] (V W:zpI L B) [zAa L V] [zAa L W]
    {n D g:ℕ} (hn:0<n) (F:B[X][X]) (hFdeg:F.natDegree≤g)
    (hF : ∀ i a,(F.coeff i).coeff a∈W) (hF0 : ∃ i,(F.coeff i).coeff 0≠0)
    (hs :aia D g*zsE L (V*W)<n*zsE L V) :
    ∃ (H :B[X]) (G J:B[X][X]),
      z1z H*F=G+Polynomial.C (z7y^n)*J∧G≠0∧G.natDegree≤g ∧
      (∀ i a,(G.coeff i).coeff a∈V*W) ∧
      ∀ i a,(G.coeff i).coeff a≠0→a+i*D <n:= by
  obtain ⟨H,hH,hHdeg,hprod,htop⟩:=d4u V W n D g F hF hs
  let T:= fun i=>H*F.coeff i %ₘ (z7y^n)
  let Q:= fun i=>H*F.coeff i /ₘ (z7y^n)
  have hx : ((z7y:B[X])^n)≠1 := by
    intro h
    have hd:=congrArg Polynomial.natDegree h
    rw [natDegree_X_pow,natDegree_one] at hd
    exact hn.ne' hd
  have hT (i:ℕ) : (T i).natDegree<n:= by
    simpa only [natDegree_X_pow] using natDegree_modByMonic_lt (H*F.coeff i) (monic_X_pow n) hx
  have hT0 (i a :ℕ) (ha :n≤a) : (T i).coeff a=0 :=
    coeff_eq_zero_of_natDegree_lt ((hT i).trans_le ha)
  refine ⟨H,assemble g T,assemble g Q,?_,?_,?_,?_,?_⟩
  · apply zXJ
    intro i
    simp only [coeff_add,coeff_C_mul,bnj]
    by_cases hi:i≤g
    · simpa only [hi,ite_true,T,Q] using (modByMonic_add_div (H*F.coeff i) (z7y^n)).symm
    · simp only [ite_eq_right hi,coeff_eq_zero_of_natDegree_lt (hFdeg.trans_lt (Nat.lt_of_not_ge hi)),
        mul_zero,add_zero]
  · obtain ⟨i,hi⟩:=hF0
    have hig:i≤g:=(le_natDegree_of_ne_zero (p:=F) (n:=i) (by
      intro hz
      exact hi (hz ▸ coeff_zero 0))).trans hFdeg
    intro hz
    have hv :=congrArg (fun P:B[X][X]=>P.coeff i) hz
    rw [bnj,ite_eq_left hig,coeff_zero] at hv
    exact fV9 hH hHdeg hi hv
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun i hi=> by rw [bnj,ite_eq_right hi.not_ge]
  · intro i a
    rw [bnj]
    split_ifs with hi
    · by_cases ha :a<n
      · exact (bXU (H*F.coeff i) ha).symm ▸ hprod i a
      · rw [hT0 i a (Nat.le_of_not_gt ha)]
        exact (V*W).zero_mem
    · rw [coeff_zero]
      exact (V*W).zero_mem
  · intro i a hne
    rw [bnj] at hne
    split_ifs at hne with hi
    · have ha :a<n:= by
        by_contra! hh
        exact hne (hT0 i a hh)
      by_contra! hh
      apply hne
      change (H*F.coeff i %ₘ (z7y^n)).coeff a=0
      rw [bXU (H*F.coeff i) ha]
      exact htop i hi a (by omega) ha
    · exact (hne (coeff_zero _)).elim
omit [zZE L B] in
private theorem fWf (F:B[X][X]) (hF:F≠0) :
   ∃ (s :ℕ) (Q:B[X][X]),F=z1z (z7y^s)*Q ∧ ∃ i,(Q.coeff i).coeff 0≠0:= by
 classical
 have hex : ∃ a :ℕ,∃ i:ℕ,(F.coeff i).coeff a≠0:= by
   by_contra! h
   exact hF (zXJ fun i=>zXJ fun a=> by simpa only [coeff_zero] using h a i)
 let s :=Nat.find hex
 have hdvd:z1z ((z7y:B[X])^s)∣F:= by
   rw [C_dvd_iff_dvd_coeff]
   intro i
   exact X_pow_dvd_iff.mpr fun a ha=> by
     by_contra h
     exact (Nat.find_min hex ha) ⟨i,h⟩
 obtain ⟨Q,hQ⟩:=hdvd
 obtain ⟨i,hi⟩:=Nat.find_spec hex
 refine ⟨s,Q,hQ,i,?_⟩
 change (F.coeff i).coeff s≠0 at hi
 simpa only [hQ,coeff_C_mul,coeff_X_pow_mul',le_refl,ite_true,Nat.sub_self] using hi
private def specializeAt (φ:B →ₐ[L] L) (u:L[X]) :B[X][X] →+* L[X] :=
 eval₂RingHom (zhd φ.toRingHom) u
private theorem specializeAt_X_pow (φ:B →ₐ[L] L) (u:L[X]) (n:ℕ) :
  specializeAt φ u (z1z (z7y^n))=z7y^n:= by
 change (z1z _).eval₂ (zhd φ.toRingHom) u= _
 rw [eval₂_C,map_pow]
 simp only [coe_mapRingHom,map_X]
private theorem specializeAt_degree {n D:ℕ} (hn:0<n) {G:B[X][X]}
  (hG : ∀ i a,(G.coeff i).coeff a≠0→a+i*D <n)
  (φ:B →ₐ[L] L) {u:L[X]} (hu:u.natDegree≤D) :
  (specializeAt φ u G).natDegree<n:= by
 apply Nat.lt_of_le_pred hn
 change (G.eval₂ (zhd φ.toRingHom) u).natDegree≤n-1
 rw [eval₂_eq_sum,Polynomial.sum_def]
 apply natDegree_sum_le_of_forall_le
 intro i hi
 have hne :G.coeff i≠0:=mem_support_iff.mp hi
 have hbound:=hG i (G.coeff i).natDegree (leadingCoeff_ne_zero.mpr hne)
 have hm: ((G.coeff i).map φ.toRingHom).natDegree≤(G.coeff i).natDegree :=natDegree_map_le
 exact (natDegree_mul_le_of_le hm (natDegree_pow_le_of_le i hu)).trans (Nat.le_pred_of_lt hbound)
private theorem gK4 {n:ℕ} {F G J:B[X][X]} {H :B[X]}
  (φ:B →ₐ[L] L) (u:L[X]) (hF:specializeAt φ u F=0)
  (hEq:z1z H*F=G+Polynomial.C (z7y^n)*J) (hdeg: (specializeAt φ u G).natDegree<n) :
  specializeAt φ u G=0:= by
 have hrel :=congrArg (specializeAt φ u) hEq
 rw [map_mul,map_add,map_mul,specializeAt_X_pow,hF,mul_zero] at hrel
 have hdvd: (z7y:L[X])^n∣specializeAt φ u G :=
  ⟨-specializeAt φ u J,by rw [mul_neg]; exact eq_neg_of_add_eq_zero_left hrel.symm⟩
 by_contra hn
 have hle :=natDegree_le_of_dvd hdvd hn
 rw [natDegree_X_pow] at hle
 exact hdeg.not_ge hle
theorem proof :qBajpRb.c2 := by
 intro B _ _ _ V W _ _ D g F hD hg hF hFdeg hcoeff hs
 let n:=compressionWidth D g
 have hn:0<n:= by unfold n compressionWidth; positivity
 obtain ⟨s,Q,hQ,hQ0⟩:=fWf F hF
 have hqc (i a :ℕ) : (Q.coeff i).coeff a=(F.coeff i).coeff (a+s) := by
  rw [hQ,coeff_C_mul,coeff_X_pow_mul]
 have hqd:Q.natDegree≤g:= by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  apply zXJ
  intro a
  rw [hqc,coeff_eq_zero_of_natDegree_lt (hFdeg.trans_lt hi),coeff_zero,coeff_zero]
 obtain ⟨H,G,J,hEq,hG0,hGd,hG,hsmall⟩ :=
  compress V W hn Q hqd (fun i a=> by rw [hqc]; exact hcoeff i (a+s)) hQ0 hs
 refine ⟨G,hG0,hGd,hG,hsmall,?_⟩
 intro φ u hu hf
 rw [eval_map] at hf ⊢
 change specializeAt φ u F=0 at hf
 change specializeAt φ u G=0
 have hq0:specializeAt φ u Q=0:= by
  rw [hQ,map_mul,specializeAt_X_pow] at hf
  exact (mul_eq_zero.mp hf).resolve_left (pow_ne_zero _ X_ne_zero)
 exact gK4 φ u hq0 hEq (specializeAt_degree hn hsmall φ hu)
end
end qMAQGbd
end
