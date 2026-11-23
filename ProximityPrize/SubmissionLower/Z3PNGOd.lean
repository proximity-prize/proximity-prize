import ProximityPrize.SubmissionLower.ZgoWlLc
set_option Elab.async false
set_option maxRecDepth 3500
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
namespace qnyP9Da
noncomputable section
open Polynomial
open P5 (K p)
open cu (L)
open qziIa4d (SeedSeries)
def c1 :Prop :=SeedExpansion
def c2 :Prop :=FrobeniusRootData
def c3:Prop :=FrobeniusOrthogonal
private def diff {A:Type} [Semiring A] (d:A→A) (g:A[X]) :A[X] :=
 g.sum fun j a=>monomial j (d a)
private theorem coeff_diff {A:Type} [Semiring A] (d:A→A) (h0:d 0=0)
  (g:A[X]) (j:ℕ) : (diff d g).coeff j=d (g.coeff j) :=
 coeff_by d h0 g j
private theorem derive_sum {n:ℕ} {F E :Type} [Field F] [Field E] [Algebra F E]
   (D:Derivation F E E) (s :E) (hs :D s=1) (b:Fin n→F) :
   D (∑ i,algebraMap F E (b i)*s^(i:ℕ)) =
     ∑ i,algebraMap F E (b i)*(i:ℕ)*s^((i:ℕ)-1) := by
 rw [map_sum]
 apply Finset.sum_congr rfl
 intro i _
 rw [D.leibniz,D.leibniz_pow,hs,D.map_algebraMap]
 simp only [smul_eq_mul,nsmul_eq_mul,mul_one,mul_zero,add_zero]
 ring
private theorem lift_poly {k :ℕ} {A M:Type} [Field A] [Field M]
    (F:Subfield M) (ι:A[X] →+* M) (π:A) (d:A→A) (h0:d 0=0)
    (hexp:PowerExpansion k π d)
    (hpow : ∀ a :A,ι (C (a^k))∈F) (hphys :ι Polynomial.X∈F)
    (E :IntermediateField F M) (t:E) (ht: (t:M)=ι (C π))
    (D:Derivation F E E) (hDt:D t=1) :
    ∃ j:A[X] →+* E,E.val.toRingHom.comp j=ι ∧ ∀ q,D (j q)=j (diff d q) := by
  classical
  let m:A →+* M:=ι.comp C
  let s :=ι (C π)
  let σ:E →+* M:=E.val.toRingHom
  let f :F →+* E :=algebraMap F E
  let bPow (a :A) :F:=⟨_,hpow a⟩
  have hσpow (a :A) :σ (f (bPow a))=m (a^k) :=rfl
  have hσt:σ t=s :=ht
  have hExp (a :A) (c:Fin k→A) (h:a = ∑ i,c i^k*π^(i:ℕ)) :
      m a=σ (∑ i,f (bPow (c i))*t^(i:ℕ)) := by
    rw [h,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_mul,map_pow,hσpow,hσt,s,m,RingHom.comp_apply]
  have hXm:ι Polynomial.X∈E :=E.algebraMap_mem (⟨ι Polynomial.X,hphys⟩:F)
  have hCm (a :A) :m a∈E := by
    obtain ⟨c,ha,_⟩:=hexp a
    let b:E := ∑ i,f (bPow (c i))*t^(i:ℕ)
    rw [show m a=σ b from hExp a c ha]
    change (b:M)∈E
    exact b.property
  have hmem (q:A[X]) :ι q∈E := by
    induction q using Polynomial.induction_on' with
    | add a b ha hb=>rw [map_add]; exact E.add_mem ha hb
    | monomial n a =>
      rw [← C_mul_X_pow_eq_monomial,map_mul,map_pow]
      exact E.mul_mem (hCm a) (pow_mem hXm n)
  let j:A[X] →+* E :=ι.codRestrict E.toSubring hmem
  have hC (a :A) :D (j (C a))=j (C (d a)) := by
    obtain ⟨c,ha,hd⟩:=hexp a
    have he :j (C a) = ∑ i,f (bPow (c i))*t^(i:ℕ) :=
      σ.injective (hExp a c ha)
    rw [he,derive_sum D t hDt]
    apply σ.injective
    change σ (∑ i,f (bPow (c i))*(i:ℕ)*t^((i:ℕ) - 1))=m (d a)
    rw [hd,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_mul,map_pow,map_natCast,hσpow,hσt,s,m,RingHom.comp_apply]
  have hX:D (j Polynomial.X)=0:=D.map_algebraMap (⟨_,hphys⟩:F)
  have hej (g:A[X]) :g.eval₂ (j.comp C) (j Polynomial.X)=j g:= by
    have h:eval₂RingHom (j.comp C) (j Polynomial.X)=j:= by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    exact RingHom.congr_fun h g
  refine ⟨j,rfl,fun g => ?_⟩
  have h:=aNu D (j.comp C) (j Polynomial.X) g (diff d g) (fun i=> by
    rw [coeff_diff d h0]
    exact hC _)
  simpa only [hej,hX,mul_zero,add_zero] using h
private theorem implicit_eq {A F E M:Type} [CommRing A] [Field F] [Field E] [Field M]
  [Algebra F E] (D:Derivation F E E) (σ:E →+* M) (j:A →+* E)
  (a :E) (G Q:A[X]) (r :M) (ι:A →+* M)
  (hj:σ.comp j=ι) (ha :σ a=r)
  (hroot :G.eval₂ ι r=0) (hder :G.derivative.eval₂ ι r≠0)
  (hcoeff : ∀ i,D (j (G.coeff i))=j (Q.coeff i)) :
  σ (D a) = -Q.eval₂ ι r/G.derivative.eval₂ ι r := by
 have hev (g:A[X]) :σ (g.eval₂ j a)=g.eval₂ ι r := by
  rw [hom_eval₂,hj,ha]
 have hr :G.eval₂ j a=0:=σ.injective (by rw [hev,hroot,map_zero])
 have hz :G.derivative.eval₂ j a≠0:= fun h=>hder (by rw [← hev,h,map_zero])
 have hchain:=aNu D j a G Q hcoeff
 rw [hr,map_zero] at hchain
 have hquot:D a = -Q.eval₂ j a/G.derivative.eval₂ j a := by
  apply (eq_div_iff hz).2
  linear_combination -hchain
 simpa only [map_div₀,map_neg,hev] using congrArg σ hquot
private theorem derive_le {k :ℕ} {F E M Γ:Type} [Field F] [Field E] [Field M]
   [Algebra F E] [LinearOrderedCommGroupWithZero Γ]
   (D:Derivation F E E) (σ:E →+* M) (v :Valuation M Γ) (t:E) (b:Fin k→F)
   (hDt:D t=1) (ht:v (σ t)=1)
   (hb : ∀ i,v (σ (algebraMap F E (b i)))≤1) :
   v (σ (D (∑ i,algebraMap F E (b i)*t^(i:ℕ))))≤1 := by
 rw [derive_sum D t hDt,map_sum]
 have hnat (n:ℕ) :v (n:M)≤1 := by
   induction n with
   | zero=>simp
   | succ n ih =>
     rw [Nat.cast_succ]
     exact v.map_add_le ih (by rw [map_one])
 apply v.map_sum_le
 intro i _
 simp only [map_mul,map_pow,map_natCast,ht,one_pow,mul_one]
 exact (mul_le_mul' (hb i) (hnat i)).trans_eq (mul_one 1)
private theorem finish_tame {k :ℕ} (hp:k.Prime) {A M Γ:Type} [Field A] [Field M]
  [CharP M k] [LinearOrderedCommGroupWithZero Γ] (v :Valuation M Γ)
  (ι:A[X] →+* M) (F:Subfield M) (π:A) (d:A→A) (hd0:d 0=0)
  (hexp:PowerExpansion k π d)
  (hpow : ∀ a :A,ι (C (a^k))∈F) (hphys :ι Polynomial.X∈F)
  (hnot:ι (C π)∉F) (hs₁:v (ι (C π))=1)
  (G:A[X][X]) (r :M) (hroot :G.eval₂ ι r=0) (hder :G.derivative.eval₂ ι r≠0)
  (b:Fin k→F) (hb:r = ∑ i,(b i:M)*(ι (C π))^(i:ℕ))
  (hcoeff : ∀ i,v (b i:M)≤1) :
  v (-(diff (diff d) G).eval₂ ι r/G.derivative.eval₂ ι r)≤1 := by
 let s :=ι (C π)
 let E :=seedField F s
 let t:E :=a8p F s
 let σ:E →+* M:=E.val.toRingHom
 let f :F →+* E :=algebraMap F E
 have hsp:s^k∈F:= by simpa only [s,map_pow] using hpow π
 obtain ⟨D,hDt⟩:=seed_derivation hp F s hnot hsp
 have hσf (a :F) :σ (f a)=(a :M) :=rfl
 have hσt:σ t=s :=rfl
 obtain ⟨j,hj,hdiff⟩:=lift_poly F ι π d hd0 hexp hpow hphys E t hσt D hDt
 let a :E := ∑ i,f (b i)*t^(i:ℕ)
 have ha :σ a=r := by
  simpa only [a,map_sum,map_mul,map_pow,hσf,hσt] using hb.symm
 have hq:=implicit_eq D σ j a G (diff (diff d) G) r ι hj ha hroot hder (fun i=> by
  rw [coeff_diff (diff d) (by simp [diff])]
  exact hdiff _)
 rw [← hq]
 exact derive_le D σ v t b hDt (hσt.symm ▸ hs₁) hcoeff
theorem of_children (Kw:c1) (roots :c2) (orthogonal:c3) :
  qziIa4d.c3:= by
 intro M Γ _ _ v ι hι hc hx G r hpos hdeg hlead hroot hder
 have hG:G≠0:= by
  intro h
  simp [h] at hpos
 obtain ⟨hfin,hdim,b,hb⟩:=roots Kw ι hι G r hG hdeg hroot
 obtain ⟨hnot,horth⟩:=orthogonal v ι hι hc hx Kw.1 (frobRoot ι r) hfin
  (hdim.trans_lt hdeg)
 let F:=(frobRoot ι r).toSubfield
 have hpow (a :SeedSeries) :ι (C (a^p))∈F :=
  (frobRoot ι r).algebraMap_mem ⟨_,Subfield.subset_closure (Or.inl ⟨a,rfl⟩)⟩
 have hphys :ι Polynomial.X∈F :=
  (frobRoot ι r).algebraMap_mem ⟨_,Subfield.subset_closure (Or.inr rfl)⟩
 let:CharP L p:=charP_of_injective_ringHom (algebraMap K L).injective p
 let:CharP M p :=
  charP_of_injective_ringHom ((ι.comp C).comp (algebraMap L SeedSeries)).injective p
 have hv :=root_integral v ι hc hx G r hlead hroot
 have hs₁:v (ι (C LX))=1 :=hc _ (HahnSeries.single_ne_zero one_ne_zero)
 have hd0:LaurentSeries.derivative L (0:SeedSeries)=0:=map_zero _
 exact finish_tame (show Nat.Prime p from KoalaBear.is_prime) v ι F LX
  (LaurentSeries.derivative L) hd0 Kw.2 hpow hphys hnot hs₁ G r hroot hder b hb
  (fun i=>(horth b i).trans (hb ▸ hv))
end
end qnyP9Da
