import ProximityPrize.SubmissionLower.ZzQsYjc
set_option Elab.async false
open _root_ renaming Algebra.algebraMap→lz,E7.CurvePlace→c9,E7.poleOrder→lJ,Field→cy,Finset.mul_sum→nX,Finset.sum_congr→nq,Function.support→lI,MvPolynomial.C→nI,MvPolynomial.X→mD,MvPolynomial.eval₂Hom_X'→ oj,Nat.mul_le_mul_right→ oq,Set.finite_iUnion→ ov,dN.GeoField→aU,finsum_eq_finsetSum_of_support_subset→n5,mul_assoc→lV
set_option maxHeartbeats 1000000
set_option maxRecDepth 1600
namespace E7
noncomputable section
open aR dN rW MJ MvPolynomial
open scoped Polynomial WithZero
attribute [local instance] MvPolynomial.gradedAlgebra
private theorem bqP {k L σ:Type}
  [cy k] [cy L] [Algebra k L] [Fintype σ]
  (h:axV k L) (u:σ→L) :
  (fun v :c9 k L=>Tq v.value u).HasFiniteSupport:= by
 have hf : (⋃ i:σ,lI (fun v :c9 k L =>
    lJ v.value (u i))).Finite :=ov fun i=>(h (u i)).1
 apply hf.subset
 intro v hv
 simp only [Set.mem_iUnion,Function.mem_support] at hv ⊢
 by_contra! hz
 exact hv (Finset.sup_eq_bot_iff _ _ |>.mpr fun i _=>hz i)
private theorem bya {k L σ τ:Type}
  [cy k] [cy L] [Algebra k L] [Fintype σ] [Fintype τ]
  (h:axV k L) (u:σ→L) (w:τ→L) (e :σ→τ)
  (he : ∀ i,u i=w (e i)) :
  Gb k L u≤Gb k L w:= by
 apply finsum_le_finsum (bqP h u) (bqP h w)
 intro v
 unfold Tq
 apply Finset.sup_le
 intro i _
 rw [he i]
 exact Finset.le_sup (s :=Finset.univ) (f := fun j=>lJ v.value (w j))
  (Finset.mem_univ (e i))
private theorem a4c {α σ:Type} [Fintype σ] (c:σ→ℕ) (f :σ→α→ℕ)
    (hf : ∀ i,(f i).HasFiniteSupport) :
    (∑ᶠ v,∑ i,c i*f i v) = ∑ i,c i * ∑ᶠ v,f i v := by
  classical
  let s :Set α := ⋃ i,lI (f i)
  have hs :s.Finite :=ov hf
  have hi (i:σ) :lI (f i)⊆(hs.toFinset :Set α) := by
    rw [Set.Finite.coe_toFinset]
    exact Set.subset_iUnion (fun j=>lI (f j)) i
  have ha :lI (fun v => ∑ i,c i*f i v)⊆(hs.toFinset :Set α) := by
    intro v hv
    by_contra h
    exact hv (Finset.sum_eq_zero fun i _=> by
      have hz :f i v=0:= by
        by_contra hn
        exact h (hi i hn)
      simp [hz])
  rw [n5 _ ha,Finset.sum_comm]
  apply nq rfl
  intro i _
  rw [n5 _ (hi i),nX]
private theorem b6Q {F L:Type} [cy F] [cy L]
   (j:F →+* L) (a :L) (f :F[X]) {N :ℕ} (hn:f.natDegree<N) (i:ℕ) :
   (Polynomial.hasseDeriv i f).eval₂ j a =
     ∑ x :Fin N,((x.val.choose i:L)*a^(x.val - i))*j (f.coeff x.val) := by
 rw [Polynomial.hasseDeriv_apply,f.sum_over_range' (fun _=> by simp) _ hn,
   Polynomial.eval₂_finsetSum,Fin.sum_univ_eq_sum_range (fun x =>
     ((x.choose i:L)*a^(x - i))*j (f.coeff x))]
 apply nq rfl
 intro x _
 simp only [Polynomial.eval₂_monomial,map_mul,map_natCast]
 ring
private theorem bDe {k F L:Type} [cy k] [cy F] [cy L] [Algebra k L]
    (j:F →+* L) (a :k) (f :F[X]) {N n:ℕ} (hdeg:f.natDegree<N) :
    (wL k (OX (N :=N) j f)).comp
      (MvPolynomial.eval₂Hom nI (fun i:Fin n =>
        ∑ r :Fin N,nI ((r.val.choose i.val :k)*a^(r.val - i.val)) *
          mD r)) =
      wL k (avg (n:=n) j (lz k L a) f) := by
  let u:Fin N→L:=OX j f
  let v :Fin n→L:=avg j (lz k L a) f
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [wL]
  · intro i
    rw [RingHom.comp_apply,oj]
    have he (r :Fin N) :
        (wL k u)
          (nI ((r.val.choose i.val :k)*a^(r.val - i.val)) *
            mD r) =
          Polynomial.C (((r.val.choose i.val :L)*(lz k L a)^(r.val - i.val)) *
            u r)*Polynomial.X:= by
      simp [wL,lV]
    rw [show (wL k v) (mD i) =
      Polynomial.C (v i)*Polynomial.X from oj _ _ _]
    rw [show v i =
      ∑ r :Fin N,((r.val.choose i.val :L)*(lz k L a)^(r.val - i.val)) *
        u r from b6Q j _ f hdeg i.val]
    rw [map_sum,map_sum,Finset.sum_mul]
    exact nq rfl fun r _=>he r
private theorem bcM {R:kT} (D:KD R) :
  (wL aU D.coefficients).comp mS=wL aU (D.Bo (n:=4)) :=
 bDe D.Fl rI D.polynomial (Nat.lt_succ_iff.mpr D.degree_le)
private theorem bH3 {R:kT} (D:KD R) {n:ℕ} (i:Fin n)
  (hi:i.val=0) :D.Bo i≠0:= by
 unfold KD.Bo avg
 rw [hi,Polynomial.hasseDeriv_zero']
 change (Polynomial.eval₂RingHom D.Fl D.center) D.polynomial≠0
 exact fun h=>D.monic.ne_zero (D.independent (h.trans (map_zero _).symm))
private theorem b5U (h5:c5) (h6:c6) {R:kT} (D:KD R)
    (hdiv :axV aU D.Fresh) :
    2*Gb aU D.Fresh D.coefficients ≤
      133671*Gb aU D.Fresh (F8 (D.Bo (n:=4)) 0) := by
  let:CharP D.Old K1.p:=charP_of_injective_ringHom
    ((lz ao D.Old).comp aR.embed).injective K1.p
  have hdeg:D.polynomial.natDegree<bf :=Nat.lt_succ_iff.mpr D.degree_le
  have hchar :D.polynomial.natDegree<K1.p:= by
    exact D.degree_le.trans_lt (by decide)
  let B:=bFT D.monic hchar (by decide :2<K1.p)
  let z := fun i=>(B.factor i).eval₂ D.Fl D.center
  let r₃:=F8 (D.Bo (n:=3)) 0
  let r₄:=F8 (D.Bo (n:=4)) 0
  have hc₀:rI≠0:= by
    have hinj:Function.Injective j8 :=
      (lz lN aU).injective.comp
        (IsFractionRing.injective ao[X] lN)
    simpa only [rI,map_zero] using
      hinj.ne (show (Polynomial.X:ao[X])≠0 from Polynomial.X_ne_zero)
  have hv (v :c9 aU D.Fresh) :=
    h6 D.Old D.Fresh D.Fl D.center D.polynomial B v.value bf
      hdeg (v.on_constants _ hc₀) D.independent (h5 R D v)
  have hcoeff :Gb aU D.Fresh D.coefficients =
      ∑ i,B.multiplicity i * ∑ᶠ v :c9 aU D.Fresh,lJ v.value (z i) := by
    have hp (v :c9 aU D.Fresh) :
        Tq v.value D.coefficients = ∑ i,B.multiplicity i*lJ v.value (z i) :=
      (hv v).1
    unfold Gb
    simp_rw [hp]
    exact a4c _ _ (fun i=>(hdiv (z i)).1)
  have hjet:Gb aU D.Fresh r₃ =
      ∑ i,min (B.multiplicity i) 2 * ∑ᶠ v :c9 aU D.Fresh,KB v.value (z i) := by
    have hp (v :c9 aU D.Fresh) :
        Tq v.value r₃ = ∑ i,min (B.multiplicity i) 2*KB v.value (z i) :=
      (hv v).2
    unfold Gb
    simp_rw [hp]
    exact a4c _ _ (fun i=>(hdiv (z i)).2.1)
  have hmore :Gb aU D.Fresh r₃≤Gb aU D.Fresh r₄:= by
    apply bya hdiv r₃ r₄ (Fin.castLE (by decide :3≤4))
    intro i
    rfl
  suffices hh:2*Gb aU D.Fresh D.coefficients ≤
      133671*Gb aU D.Fresh r₃ from
    hh.trans (Nat.mul_le_mul_left _ hmore)
  rw [hcoeff,hjet,nX ,nX]
  apply Finset.sum_le_sum
  intro i _
  rw [(hdiv (z i)).2.2.1,← lV,← lV]
  apply oq
  have hm:=(B.le_degree i).trans D.degree_le
  by_cases hi:B.multiplicity i≤2
  · rw [min_eq_left hi]
    exact oq _ (by decide)
  · rw [min_eq_right (by omega)]
    omega
theorem of_children (h1 :c1) (h2 :c2) (h3:c3) (h4 :c4) (h5:c5) (h6:c6) :
   MJ.c3:= by
 intro R hR hprime hhom hdim
 obtain ⟨D⟩:=h1 R hR hprime hhom hdim
 have hdiv :=h2 aU D.Fresh D.aDk
 let u:=D.coefficients
 let v :=D.Bo (n:=4)
 have hcone :gN R=SQ aU u:=D.equation
 let i:Fin bf :=⟨D.polynomial.natDegree,Nat.lt_succ_iff.mpr D.degree_le⟩
 have hi:u i=1 := by
   simp [u,i,KD.coefficients,OX,Polynomial.coeff_natDegree,
     D.monic.leadingCoeff]
 have hu:F8 u i=u:= by funext j; simp [F8,hi]
 have hv₀:v 0≠0:=bH3 D 0 rfl
 have hgen:YC aU u i = ⊤ := by
   rw [YC,hu]
   exact D.generates
 obtain ⟨hpositive,hsource⟩ :=
   h3 aU D.Fresh _ D.aDk hdiv u i (by simp [hi])
 have hpos :0<Gb aU D.Fresh u:= by
   rw [← hu]
   exact hpositive.mp (by rw [hu]; exact D.nonconstant)
 have hs : (Gb aU D.Fresh u:ℚ)=affineDegree (gN R) := by
   have h:=(hsource (by simpa only [hu] using hpos)).2
   rwa [hu,hgen,IntermediateField.finrank_top,Nat.cast_one,one_mul,← hcone] at h
 have hcmp:=b5U h5 h6 D hdiv
 have hjpos :0<Gb aU D.Fresh (F8 v 0) := by
   change 2*Gb aU D.Fresh u≤133671*Gb aU D.Fresh
     (F8 v 0) at hcmp
   omega
 have himage :SQ aU v=lA R:= by
   rw [lA,D.equation]
   change RingHom.ker (wL aU v) =
     (RingHom.ker (wL aU u)).comap mS
   rw [RingHom.comap_ker,bcM D]
 have hrank :=h4 GeoField D.Fresh _ _ u i v 0 mS (by simp [hi]) hv₀ hgen
   (bcM D)
 rw [← hcone] at hrank
 obtain ⟨hdim',ht⟩:=(h3 aU D.Fresh _ D.aDk hdiv v 0 hv₀).2 hjpos
 rw [himage,← hrank] at ht
 refine ⟨himage ▸ hdim',?_⟩
 have hcmp' : 2*(Gb aU D.Fresh u:ℚ) ≤
     133671*(Gb aU D.Fresh (F8 v 0) :ℚ) := by exact_mod_cast hcmp
 rw [hs,ht] at hcmp'
 simpa only [lV] using hcmp'
end
end E7
