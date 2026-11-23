import ProximityPrize.SubmissionLower.Z9w0Rrc
set_option Elab.async false
open _root_ renaming DFunLike.congr_fun → zmU, Finset.prod_congr → zX3, Function.Injective → zq4, Function.comp_def → zQM, IsFractionRing.injective → zxb, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_X' → zrD, MvPolynomial.ringHom_ext → zXT, Polynomial.C → z1z, Polynomial.X → z7y, Polynomial.evalRingHom → zhy, Polynomial.eval_C → zFf, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.map_prod → zeg, Polynomial.map_sub → z3A, PowerSeries → zpm, PowerSeries.C → zMG, PowerSeries.X → zWv, PowerSeries.coeff → z2o, PowerSeries.constantCoeff → zbO
set_option backward.isDefEq.respectTransparency false
namespace qVAMdHe
noncomputable section
open cu (L)
open qfbIfsd (form Detects)
open q2tSkEc (bzm orders)
open qEAs6me (Coeff topPoly topRes tie tied)
open scoped BigOperators Classical
open private tied_map from ProximityPrize.SubmissionLower.ZPRNTid
def c1 :Prop :=
  ∀ s b d:ℕ,2≤d →
    ∃ a :Fin (b+s+1)→Ext s b d,zq4 a ∧
      (topPoly (ek s b d) 1).natDegree=b+s+1 ∧
      (∀ i,(topPoly (ek s b d) 1).eval (a i)=0 ∧
        (topPoly (ek s b d) 1).derivative.eval (a i)≠0 ∧
        delta (ek s b d) (a i)≠0) ∧
      (0<b→zq4 (fun i=>(topPoly (ek s b d) 0).eval (a i))) ∧
      (b=0→zq4
        (fun i=>jet (ek s b d) 0 (a i)/delta (ek s b d) (a i)))
def c2 :Prop :=
  ∀ {E :Type} [Field E] (s b d:ℕ),2≤d → ∀ (a :bzm s b d→E) (α:E),
    a (first s b d)=0 →
    (topPoly a 1).eval α=0→(topPoly a 1).derivative.eval α≠0 →
    delta a α≠0 →
    ∃ x u v :zpm E,zbO x= α ∧
      zbO u = -(topPoly a 0).eval α ∧
      zbO v=0∧v≠0 ∧
      (b=0→z2o 1 u=jet a 0 α/delta a α) ∧
      ∀ t,rev (deformArg (zMG ∘ a) u zWv) t x v=0
private theorem deformArg_map {M N :Type} [CommSemiring M] [CommSemiring N]
  (f :M →+* N) {s b d:ℕ} (a :bzm s b d→M) (u e :M) (r :bzm s b d) :
  f (deformArg a u e r)=deformArg (f ∘ a) (f u) (f e) r := by
 have h:f ∘ insertU a u=insertU (f ∘ a) (f u) := by
  funext i
  by_cases hi:i=first s b d <;> simp [insertU,hi]
 unfold deformArg
 rw [map_add,tied_map,h]
 split_ifs <;> simp
private theorem reduce_deform {s b d:ℕ} (R:Coeff s b d) :
    (deform R).map zbO=(view s b d (tie R)).map (emb s b d) := by
  let f :=zhd (zbO (R:=Ext s b d))
  let e :=zOD
    (Polynomial.C.comp (PowerSeries.C.comp ((emb s b d).comp MvPolynomial.C)))
    (deformArg (z1z ∘ zMG ∘ ek s b d) z7y
      (z1z zWv))
  let v :=(zhd (emb s b d)).comp (view s b d).toRingHom
  have h:f.comp e=v.comp tie := by
    have hv :v ∘ z9v =
        insertU (z1z ∘ ek s b d) Polynomial.X:= by
      funext r
      change (view s b d (z9v r)).map (emb s b d)= _
      exact view_generic r
    apply zXT
    · intro k
      simp [e,f,v,tie,view_const]
    · intro r
      change f (e (z9v r))=v (tie (z9v r))
      rw [show e (z9v r)= _ from zrD _ _ _,
        deformArg_map,show tie (z9v r)=tied z9v r from
          zrD _ _ _,tied_map,hv]
      simp [f,deformArg,zQM,zrL]
  exact zmU h R
private theorem rev_affine {E :Type} [Field E] {s b d:ℕ}
   (a :bzm s b d→E) (x v :E) (hv :v≠0) (t:Fin 3)
   (h:rev a t x v=0) :form a t x v⁻¹=0:= by
 have hi (i:ℕ) (hle :i≤orders d t) :
     (v⁻¹)^i*v^orders d t=v^(orders d t - i) := by
   calc
     _=(v⁻¹)^i*(v^(orders d t - i)*v^i) := by rw [← pow_add,Nat.sub_add_cancel hle]
     _=v^(orders d t - i)*((v⁻¹)^i*v^i) := by ac_rfl
     _ = _:= by rw [inv_pow,inv_mul_cancel₀ (pow_ne_zero _ hv),mul_one]
 apply (mul_eq_zero.mp (show form a t x v⁻¹*v^orders d t=0 from ?_)).resolve_right
   (pow_ne_zero _ hv)
 rw [form,Finset.sum_mul,← h]
 unfold rev
 exact Finset.sum_congr rfl fun i _=> by
   rw [mul_assoc,hi _ (Nat.le_of_lt_succ i.1.isLt)]
private theorem detect_arc {s b d:ℕ} {R:Coeff s b d} (hR:Detects R)
    (x u v :zpm (Ext s b d)) (hv :v≠0)
    (h : ∀ t,rev (deformArg (zMG ∘ ek s b d) u zWv) t x v=0) :
    (deform R).eval u=0:= by
  let A:=zpm (Ext s b d)
  let F:=FractionRing A
  let ι:A →+* F:=algebraMap A F
  let m:=PowerSeries.C.comp ((emb s b d).comp MvPolynomial.C)
  let a :=deformArg (zMG ∘ ek s b d) u zWv
  have he : (zhy u).comp (zOD (Polynomial.C.comp m)
      (deformArg (z1z ∘ zMG ∘ ek s b d) z7y
        (z1z zWv)))=zOD m a := by
    apply zXT
    · intro k
      simp [zFf]
    · intro i
      simp only [RingHom.comp_apply,zrD]
      rw [deformArg_map]
      simp [a,zQM,zFf]
  change (zhy u) (deform R)=0
  rw [show (zhy u) (deform R)=R.eval₂ m a from zmU he R]
  apply (zxb A F).eq_iff.mp
  rw [map_zero,MvPolynomial.eval₂_comp_left]
  apply hR (ι.comp m) (ι ∘ a) (ι x) (ι v)⁻¹
  intro t
  apply rev_affine _ _ _ (by simpa only [map_zero] using (zxb A F).ne hv) t
  have hh:=congrArg ι (h t)
  simpa [a,rev,zQM] using hh
private theorem roots_reduce {E :Type} [Field E] {n:ℕ}
   (p:Polynomial (zpm E)) (u:Fin n→zpm E)
   (hu:zq4 u) (hp : ∀ i,p.eval (u i)=0) :
   (∏ i,(z7y-Polynomial.C (zbO (u i)))) ∣
     p.map PowerSeries.constantCoeff := by
 let A:=zpm E
 let F:=FractionRing A
 let ι:A →+* F:=algebraMap A F
 let q:Polynomial A := ∏ i,(z7y-Polynomial.C (u i))
 have hq:q.Monic:=Polynomial.monic_prod_of_monic _ _ fun _ _=>Polynomial.monic_X_sub_C _
 have hι:=zxb A F
 have hr (i:Fin n) : (p.map ι).IsRoot (ι (u i)) := by
   rw [Polynomial.IsRoot,Polynomial.eval_map_apply,hp i,map_zero]
 have hd' : (∏ i,(z7y-Polynomial.C (ι (u i))))∣p.map ι :=
   Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C
     (s := fun i=>ι (u i)) (hι.comp hu)) fun i=>Polynomial.dvd_iff_isRoot.mpr (hr i)
 have hd:q∣p:= by
   apply (Polynomial.map_dvd_map ι hι hq).mp
   have hm:q.map ι = ∏ i,(z7y-Polynomial.C (ι (u i))) := by
     change (∏ i,(z7y-Polynomial.C (u i))).map ι= _
     rw [zeg]
     apply zX3 rfl
     intro i _
     rw [z3A,Polynomial.map_X,zrL ι]
   rwa [hm]
 simpa [q,zeg,z3A,Polynomial.map_X,zrL] using
   Polynomial.map_dvd (zbO (R:=E)) hd
private theorem bKQ (lift:c2) {s b d:ℕ} (hd:2≤d)
   {R:Coeff s b d} (hR:Detects R) (a :Fin (b+s+1)→Ext s b d)
   (hz : ∀ i,(topPoly (ek s b d) 1).eval (a i)=0 ∧
     (topPoly (ek s b d) 1).derivative.eval (a i)≠0 ∧
     delta (ek s b d) (a i)≠0)
   (hsep:0<b→zq4 (fun i=>(topPoly (ek s b d) 0).eval (a i)))
   (hjet:b=0→zq4
     (fun i=>jet (ek s b d) 0 (a i)/delta (ek s b d) (a i))) :
   (∏ i,(z7y-Polynomial.C (-(topPoly (ek s b d) 0).eval (a i)))) ∣
     (view s b d (tie R)).map (emb s b d) := by
 have ha₀:ek s b d (first s b d)=0:= by simp [ek]
 choose x u v hx hu hv₀ hv hcoeff hform using fun i =>
   lift s b d hd (ek s b d) (a i) ha₀ (hz i).1 (hz i).2.1 (hz i).2.2
 have hui:zq4 u:= by
   intro i j hij
   by_cases hb:b=0
   · apply hjet hb
     simpa only [hcoeff i hb,hcoeff j hb] using congrArg (z2o 1) hij
   · apply hsep (Nat.pos_of_ne_zero hb)
     apply neg_injective
     rw [← hu i,← hu j,hij]
 have hprod:=roots_reduce (E :=Ext s b d) (deform R) u hui
   (fun i=>detect_arc hR (x i) (u i) (v i) (hv i) (hform i))
 rw [← reduce_deform]
 refine (show (∏ i,(z7y-Polynomial.C (zbO (u i))))= _
   from zX3 rfl fun i _ =>
     congrArg (fun z=>z7y-Polynomial.C z) (hu i)) ▸ hprod
private theorem mv_gcd (I F:Type) [Field F] :IsGCDMonoid (MvPolynomial I F) := by
 let _:UniqueFactorizationMonoid F:=PrincipalIdealRing.to_uniqueFactorizationMonoid
 let _:UniqueFactorizationMonoid (MvPolynomial I F) :=MvPolynomial.uniqueFactorizationMonoid I
 exact ⟨UniqueFactorizationMonoid.toGCDMonoid _⟩
theorem of_children (roots :c1) (lift:c2) :qEAs6me.c3:= by
 intro s b d hd R hR
 obtain ⟨a,ha,hg,hz,hsep,hjet⟩:=roots s b d hd
 have hprod:=bKQ lift hd hR a hz hsep hjet
 have hroot (i:Fin (b+s+1)) :=(hz i).1
 have hprim:=primitive a ha hg hroot
 have hne : (topPoly (ek s b d) 1).leadingCoeff≠0:= by
   apply Polynomial.leadingCoeff_ne_zero.mpr
   intro h
   rw [h,Polynomial.natDegree_zero] at hg
   omega
 have he : (view s b d (topRes :Coeff s b d)).map (emb s b d) ∣
     (view s b d (tie R)).map (emb s b d) := by
   rw [resultant_factor a ha hg hroot]
   exact (Polynomial.C_mul_dvd (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
     (pow_ne_zero _ hne))).mpr hprod
 let _:IsGCDMonoid (tu s b d) :=mv_gcd (E8 s b d) L
 have hdiv :view s b d topRes∣view s b d (tie R) := by
   apply hprim.dvd_of_fraction_map_dvd_fraction_map (K:=kB s b d)
   apply (Polynomial.map_dvd_map' (algebraMap (kB s b d) (Ext s b d))).mp
   simpa only [Polynomial.map_map,emb] using he
 obtain ⟨Q,hQ⟩:=hdiv
 refine ⟨(view s b d).symm Q,(view s b d).injective ?_⟩
 simpa only [map_mul,AlgEquiv.apply_symm_apply] using hQ
end
end qVAMdHe
