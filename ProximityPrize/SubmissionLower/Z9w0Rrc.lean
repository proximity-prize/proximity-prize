import ProximityPrize.SubmissionLower.Z877yta
import ProximityPrize.SubmissionLower.ZtdrOue
import ProximityPrize.SubmissionLower.ZStcUwb
import ProximityPrize.SubmissionLower.ZKdh4ve
set_option Elab.async false
open _root_ renaming Equiv.optionSubtypeNe → zk4, Equiv.optionSubtypeNe_symm_of_ne → zFr, Finsupp.sum_fintype → z9d, Finsupp.weight_apply → zDM, Fintype.card_sigma → zTU, Function.Injective → zq4, Ideal.span → zye, Ideal.subset_span → zCn, IsFractionRing.injective → zxb, LinearMap.range → zWl, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.eval₂Hom → zOD, MvPolynomial.renameEquiv_apply → zyk, Nat.add_mul → zNE, Nat.sub_add_cancel → zxt, Polynomial → zM1, Polynomial.C → z1z, Polynomial.C_injective → zmy, Polynomial.X → z7y, Polynomial.coeff_natDegree → zkZ, Polynomial.leadingCoeff_map_of_injective → z0W, Polynomial.mapRingHom → zhd, RingHom.id → zz4, Set.image_singleton → zyl
section
set_option autoImplicit true
section
namespace qVEB2pd
noncomputable section
open MvPolynomial
def weights (s :ℕ) :Fin 2→Fin 2→ℕ := ![![1,s],![0,1]]
def caps (s b d:ℕ) :Fin 2→ℕ := ![b+d*s,d]
abbrev Box (K:Type) [Field K] (s b d:ℕ) :=
 wT.filtered (F:=K) (weights s) (caps s b d)
def exponent (x y :ℕ) :Fin 2 →₀ ℕ:=Finsupp.equivFunOnFinite.symm ![x,y]
@[simp] theorem exponent_zero (x y :ℕ) :exponent x y 0=x := by simp [exponent]
@[simp] theorem bpQ (x y :ℕ) :exponent x y 1=y := by simp [exponent]
theorem exponent_eta (m:Fin 2 →₀ ℕ) :exponent (m 0) (m 1)=m:= by
 ext i
 fin_cases i <;> simp
theorem weight_zero (s :ℕ) (m:Fin 2 →₀ ℕ) :
  m.weight (weights s 0)=m 0+m 1*s := by
 simp [weights,zDM,z9d,Fin.sum_univ_two,smul_eq_mul]
theorem weight_one (s :ℕ) (m:Fin 2 →₀ ℕ) :
  m.weight (weights s 1)=m 1 := by
 simp [weights,zDM,z9d,Fin.sum_univ_two,smul_eq_mul]
theorem caps_add (s b d c e :ℕ) :
  caps s (b+c) (d+e)=caps s b d+caps s c e := by
 funext i
 fin_cases i <;> simp [caps,zNE] <;> omega
end
end qVEB2pd
end
section
namespace qVEB2pd
noncomputable section
open MvPolynomial
open qfbIfsd (Slot)
open qj0Yp9c (PieceIndex twiceCount)
open private count from ProximityPrize.SubmissionLower.ZtdrOue
private def cV (s b d:ℕ) :Set (Fin 2 →₀ ℕ) :=
 {m | ∀ i,m.weight (weights s i)≤ caps s b d i}
private theorem mem_grade {s b d:ℕ} (m:Fin 2 →₀ ℕ) :
   m∈cV s b d↔m 0+m 1*s≤b+d*s∧m 1≤d:= by
 constructor
 · intro h
   exact ⟨by simpa [weight_zero,caps] using h 0,by simpa [weight_one,caps] using h 1⟩
 · intro h i
   fin_cases i
   · simpa [weight_zero,caps] using h.1
   · simpa [weight_one,caps] using h.2
private def gradeEquiv (s b d:ℕ) :cV s b d ≃ Slot s b d where
 toFun m:= by
  have h:=(mem_grade m.val).mp m.property
  have hx :=h.1
  have hy :=h.2
  have he :d*s=(d-m.val 1)*s+m.val 1*s := by
   rw [← zNE,zxt hy]
  exact ⟨⟨m.val 1,by omega⟩,⟨m.val 0,by change m.val 0<b+(d-m.val 1)*s+1; omega⟩⟩
 invFun i:= by
  have hy :i.1.val≤d:=Nat.le_of_lt_succ i.1.isLt
  have hx :=i.2.isLt
  have he :d*s=(d-i.1.val)*s+i.1.val*s := by
   rw [← zNE,zxt hy]
  refine ⟨exponent i.2.val i.1.val,?_⟩
  rw [mem_grade,exponent_zero,bpQ]
  exact ⟨by omega,hy⟩
 left_inv m:=Subtype.ext (exponent_eta m.val)
 right_inv i:= by
  rcases i with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
  simp
  exact (Fin.heq_ext_iff rfl).mpr rfl
private instance (s b d:ℕ) :Fintype (cV s b d) :=
 Fintype.ofEquiv _ (gradeEquiv s b d).symm
private theorem box_eq (K:Type) [Field K] (s b d:ℕ) :
  Box K s b d=restrictSupport K (cV s b d) := by
 ext p
 rw [wT.Wb,mem_restrictSupport_iff]
 simp only [weightedTotalDegree,Finset.sup_le_iff]
 exact ⟨fun h _ hm i=>h i _ hm,fun h i _ hm=>h hm i⟩
theorem slot_le {s b d:ℕ} (i:Slot s b d) (j:Fin 2) :
   (exponent i.2.val i.1.val).weight (weights s j)≤ caps s b d j :=
 ((gradeEquiv s b d).symm i).property j
theorem slot_inj {s b d:ℕ} :
  zq4 (fun i:Slot s b d=>exponent i.2.val i.1.val) :=
 fun _ _ h=>(gradeEquiv s b d).symm.injective (Subtype.ext h)
instance boxFinite (K:Type) [Field K] (s b d:ℕ) :zAa K (Box K s b d) := by
 rw [box_eq]
 exact Module.Finite.of_basis (basisRestrictSupport K (cV s b d))
theorem twice_finrank (K:Type) [Field K] (s b d:ℕ) :
  2*(zsE K (Box K s b d) :ℤ)=(d+1)*(2*((b:ℤ)+1)+s*(d:ℤ)) := by
 rw [box_eq,Module.finrank_eq_card_basis (basisRestrictSupport K (cV s b d)),
  Fintype.card_congr (gradeEquiv s b d)]
 have h:=count s d b 0
 simp only [PieceIndex,zTU,Fintype.card_prod,Fintype.card_fin,
  Nat.zero_add,Nat.mul_one,twiceCount,Nat.cast_zero,zero_add,one_mul] at h
 rw [show Fintype.card (Slot s b d) = ∑ i:Fin (d+1),(b+(d-i.val)*s+1) by
  simp [Slot,zTU]]
 linear_combination h
end
end qVEB2pd
end
end
section
set_option autoImplicit true
section
open Module renaming finrank→qz0
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace qVEB2pd
noncomputable section
open MvPolynomial wT
open P5_7_1_7_4_3_4 (pairDegree)
variable {K:Type} [Field K]
abbrev ke (f g:z3y (Fin 2) K) :=zye {f,g}
abbrev Cut (f g:z3y (Fin 2) K) :=z3y (Fin 2) K ⧸ ke f g
private def stage (f g:z3y (Fin 2) K) (s B D:ℕ) :
   Box K s B D →ₗ[K] Cut f g :=
 (Ideal.Quotient.mkₐ K (ke f g)).toLinearMap.domRestrict (Box K s B D)
private theorem subtract_caps (s B D b d:ℕ) (hb:b≤B) (hd:d≤D) :
  (fun i=>caps s B D i - caps s b d i)=caps s (B-b) (D-d) := by
 have he :=caps_add s (B-b) (D-d) b d
 rw [zxt hb,zxt hd] at he
 funext i
 rw [he,Pi.add_apply,Nat.add_sub_cancel]
private theorem multiples (s B D b d:ℕ) (hb:b≤B) (hd:d≤D)
   (p:z3y (Fin 2) K) (hp:p≠0)
   (hdeg : ∀ i,p.weightedTotalDegree (weights s i)=caps s b d i) :
   ∃ U:Submodule K (Box K s B D),(∀ x,x∈U↔p∣x.val) ∧
     qz0 K U=qz0 K (Box K s (B-b) (D-d)) := by
 have q0 (i:Fin 2) :caps s b d i≤ caps s B D i:= by
   have hh:=Nat.mul_le_mul_right s hd
   fin_cases i <;> simp [caps] <;> omega
 let m:=aNQ (weights s) (caps s B D) (caps s b d) p hp hdeg q0
 refine ⟨zWl m,a5K _ _ _ p hp hdeg q0,?_⟩
 dsimp only [m]
 rw [LinearMap.finrank_range_of_inj (a3Z _ _ _ p hp hdeg q0),
   subtract_caps s B D b d hb hd]
private theorem stage_bound (s B D b d c e :ℕ) (hb:b+c≤B) (hd:d+e≤D)
   {f g:z3y (Fin 2) K} (hf :Prime f) (hg:g≠0) (hc : ¬ f∣g)
   (hfdeg : ∀ i,f.weightedTotalDegree (weights s i)=caps s b d i)
   (hgdeg : ∀ i,g.weightedTotalDegree (weights s i)=caps s c e i) :
   qz0 K (zWl (stage f g s B D))≤pairDegree s b d c e := by
 have hfgdeg (i:Fin 2) :
     (f*g).weightedTotalDegree (weights s i)=caps s (b+c) (d+e) i:= by
   rw [weightedTotalDegree_mul _ _ _ hf.ne_zero hg,hfdeg i,hgdeg i,caps_add,Pi.add_apply]
 obtain ⟨U,hU,rU⟩:=multiples s B D b d (by omega) (by omega) f hf.ne_zero hfdeg
 obtain ⟨V,hV,rV⟩:=multiples s B D c e (by omega) (by omega) g hg hgdeg
 obtain ⟨W,hW,rW⟩:=multiples s B D (b+c) (d+e) hb hd (f*g) (mul_ne_zero hf.ne_zero hg) hfgdeg
 have hi:U ⊓ V=W:= by
   ext x
   change (x∈U∧x∈V)↔x∈W
   rw [hU,hV,hW]
   constructor
   · rintro ⟨hx,z,hz⟩
     rw [hz] at hx
     obtain ⟨a,ha⟩:=(hf.dvd_mul.mp hx).resolve_left hc
     exact ⟨a,by rw [hz,ha,← mul_assoc,mul_comm g f]⟩
   · exact fun h=>⟨(dvd_mul_right f g).trans h,(dvd_mul_left g f).trans h⟩
 let q:=stage f g s B D
 have hk (p:z3y (Fin 2) K) (hp:p∈ke f g)
     (x :Box K s B D) (hx :p∣x.val) :x∈LinearMap.ker q:= by
   obtain ⟨a,ha⟩:=hx
   apply LinearMap.mem_ker.mpr
   change Ideal.Quotient.mk (ke f g) x.val=0
   apply Ideal.Quotient.eq_zero_iff_mem.mpr
   rw [ha]
   exact Ideal.mul_mem_right a (ke f g) hp
 have hsup:U ⊔ V≤LinearMap.ker q:=sup_le
   (fun x hx=>hk f (zCn (by simp)) x ((hU x).mp hx))
   (fun x hx=>hk g (zCn (by simp)) x ((hV x).mp hx))
 have hr :=Submodule.finrank_sup_add_finrank_inf_eq U V
 rw [hi,rU,rV,rW] at hr
 have hle :=Submodule.finrank_mono hsup
 have hq:=q.finrank_range_add_finrank_ker
 have h:qz0 K (zWl q)+qz0 K (Box K s (B-b) (D-d)) +
     qz0 K (Box K s (B-c) (D-e)) ≤
     qz0 K (Box K s B D)+qz0 K (Box K s (B-(b+c)) (D-(d+e))) := by
   omega
 have hz :=(Nat.cast_le (α:=ℤ)).mpr h
 push_cast at hz
 have hz' := mul_le_mul_of_nonneg_left hz (by decide : (0:ℤ)≤2)
 simp only [mul_add,twice_finrank] at hz'
 push_cast [Nat.cast_sub (show b≤B by omega),Nat.cast_sub (show c≤B by omega),
   Nat.cast_sub (show d≤D by omega),Nat.cast_sub (show e≤D by omega),Nat.cast_sub hb,
   Nat.cast_sub hd] at hz'
 change qz0 K (zWl q)≤_
 rw [← Nat.cast_le (α:=ℤ)]
 push_cast [pairDegree]
 nlinarith only [hz']
theorem eJB (s b d c e :ℕ)
   {f g:z3y (Fin 2) K} (hf :Prime f) (hg:g≠0) (hc : ¬ f∣g)
   (hfdeg : ∀ i,f.weightedTotalDegree (weights s i)=caps s b d i)
   (hgdeg : ∀ i,g.weightedTotalDegree (weights s i)=caps s c e i) :
   zAa K (Cut f g)∧qz0 K (Cut f g)≤pairDegree s b d c e := by
 classical
 have hr :Module.rank K (Cut f g)≤(pairDegree s b d c e :Cardinal) := by
   apply rank_le
   intro T hT
   choose p hp using fun z :T=>Ideal.Quotient.mk_surjective (I:=ke f g) z.val
   let q0 (z :T) :=(p z).weightedTotalDegree (weights s 0)+(p z).weightedTotalDegree (weights s 1)
   let N :=Finset.univ.sup q0
   let q:=stage f g s (b+c+N) (d+e+N)
   have hmem (z :T) : (z :Cut f g)∈zWl q:= by
     refine ⟨⟨p z,(wT.Wb _ _ _).mpr ?_⟩,hp z⟩
     intro i
     have hz : (p z).weightedTotalDegree (weights s 0) +
         (p z).weightedTotalDegree (weights s 1)≤N :=Finset.le_sup (f :=q0) (Finset.mem_univ z)
     fin_cases i <;> simp [caps] <;> omega
   have hli:LinearIndependent K (fun z :T=>(⟨z.val,hmem z⟩:zWl q)) :=
     LinearIndependent.of_comp (zWl q).subtype hT
   have hcard:T.card≤qz0 K (zWl q) := by
     simpa using hli.fintype_card_le_finrank
   exact hcard.trans (stage_bound s _ _ b d c e (by omega) (by omega) hf hg hc hfdeg hgdeg)
 exact ⟨Module.rank_lt_aleph0_iff.mp (hr.trans_lt Cardinal.natCast_lt_aleph0),
   Module.finrank_le_of_rank_le hr⟩
end
end qVEB2pd
end
section
set_option backward.isDefEq.respectTransparency false
namespace qVEB2pd
noncomputable section
open MvPolynomial
open cu (L)
open qfbIfsd (Slot form)
open qBl3Pad
open scoped nonZeroDivisors
private def term {K:Type} [CommSemiring K] {s b d:ℕ} (a :Slot s b d→K)
   (i:Slot s b d) :z3y (Fin 2) K :=
 C (a i)*z9v 0^i.2.val*z9v 1^i.1.val
private theorem term_eq {K:Type} [CommSemiring K] {s b d:ℕ} (a :Slot s b d→K)
  (i:Slot s b d) :term a i=monomial (exponent i.2.val i.1.val) (a i) := by
 have he :exponent i.2.val i.1.val=Finsupp.single 0 i.2.val+Finsupp.single 1 i.1.val := by
  ext j
  fin_cases j <;> simp
 rw [he,monomial_add_single,← zero_add (Finsupp.single 0 i.2.val),monomial_add_single,← C_apply]
 rfl
private theorem term_sum_caps {K:Type} [CommSemiring K] {s b d:ℕ}
   (a :Slot s b d→K) (ha : ∀ i,a i≠0) :
   (∑ i,term a i)≠0 ∧
     ∀ j,(∑ i,term a i).weightedTotalDegree (weights s j)=caps s b d j:= by
 classical
 let i₀:Slot s b d:=⟨Fin.last d,⟨b,by simp⟩⟩
 let m:=exponent b d
 have hm:m=exponent i₀.2.val i₀.1.val :=rfl
 have q0: (∑ i,term a i).coeff m=a i₀:= by
   rw [coeff_sum,Finset.sum_eq_single i₀]
   · simp [term_eq,hm]
   · intro i _ hi
     rw [term_eq,hm,coeff_monomial,ite_eq_right (fun h=>hi (slot_inj h))]
   · simp
 have hn:=ha i₀
 have hmem:m∈(∑ i,term a i).support :=mem_support_iff.mpr (q0.symm ▸ hn)
 refine ⟨fun h=>hn (q0.symm.trans (by simp [h])),fun j=>le_antisymm ?_ ?_⟩
 · rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
   apply Submodule.sum_mem
   intro i _
   rw [term_eq,monomial_mem_restrictWeightedDegree]
   exact Or.inl (slot_le i j)
 · have h:=le_weightedTotalDegree (weights s j) hmem
   fin_cases j
   · simpa [m,weight_zero,caps] using h
   · simpa [m,weight_one,caps] using h
variable {s :ℕ} {b e :Fin 3→ℕ} {k :Fin 3}
private def liftSlot (t:Fin 3) (ht:t≠k) (i:Slot s (b t) (e t)) :OtherVars s b e k :=
 ⟨⟨t,i⟩,ht⟩
private abbrev Raw (s :ℕ) (b e :Fin 3→ℕ) (k :Fin 3) :=
 z3y (Fin 2) (PairCoeffs s b e k)
private def raw (t:Fin 3) (ht:t≠k) :Raw s b e k :=
 ∑ i,term (fun j=>z9v (liftSlot t ht j:OtherVars s b e k)) i
private theorem fTY (t:Fin 3) (ht:t≠k) :
  (raw t ht:Raw s b e k)≠0 ∧
    ∀ i,(raw t ht:Raw s b e k).weightedTotalDegree (weights s i)=caps s (b t) (e t) i :=
 term_sum_caps _ (fun _=>X_ne_zero _)
attribute [local instance] MvPolynomial.algebraMvPolynomial
private theorem bIV (t:Fin 3) (ht:t≠k) :
  algebraMap (Raw s b e k) (lK s b e k) (raw t ht)=pairForm s b e k t:= by
 simp [raw,term,liftSlot,pairForm,pairCoeff,form,ht]
theorem pair_caps (t:Fin 3) (ht:t≠k) :
    pairForm s b e k t≠0 ∧
      ∀ i,(pairForm s b e k t).weightedTotalDegree (weights s i)=caps s (b t) (e t) i:= by
  have hC:=zxb (PairCoeffs s b e k) (MY s b e k)
  simpa [pairForm,form,term,pairCoeff,ht,liftSlot] using
    (term_sum_caps (fun i:Slot s (b t) (e t) =>
      algebraMap (PairCoeffs s b e k) (MY s b e k)
        (z9v (liftSlot t ht i:OtherVars s b e k)))
      (fun _=>(map_ne_zero_iff _ hC).mpr (X_ne_zero _)))
private theorem raw_prime (t u:Fin 3) (ht:t≠k) (hu:u≠k) (htu:t≠u) :
    Prime (raw t ht:Raw s b e k) ∧ ¬ (raw t ht:Raw s b e k)∣raw u hu:= by
  classical
  let S:=Fin 2 ⊕ OtherVars s b e k
  let i₀:=zeroSlot s (b t) (e t)
  let v :S := .inr (liftSlot t ht i₀)
  let E :=(sumAlgEquiv L (Fin 2) (OtherVars s b e k)).symm.trans
    ((renameEquiv L (zk4 v).symm).trans (optionEquivLeft L _))
  let w (a :S) :z3y {x :S // x≠v} L:=if h:a≠v then z9v ⟨a,h⟩ else 0
  have hX (a :S) (ha :a≠v) :
      (optionEquivLeft L _) (renameEquiv L (zk4 v).symm (z9v a)) =
        z1z (w a) := by
    simp [w,ha,zFr ha]
  have hr (a :Fin 3) (ha :a≠k) (T:Finset (Slot s (b a) (e a)))
      (h : ∀ i∈T,(Sum.inr (liftSlot a ha i) :S)≠v) :
      E (∑ i∈T,term (fun j=>z9v (liftSlot a ha j:OtherVars s b e k)) i) =
        z1z (∑ i∈T,w (.inr (liftSlot a ha i)) *
          w (.inl 0)^i.2.val*w (.inl 1)^i.1.val) := by
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [E,term,AlgEquiv.trans_apply,map_mul,map_pow,sumAlgEquiv_symm_C_X,sumAlgEquiv_symm_X]
    rw [hX _ (h i hi),hX _ (by simp [v] : (Sum.inl 0:S)≠v),
      hX _ (by simp [v] : (Sum.inl 1 :S)≠v)]
  have hv :E (term (fun j=>z9v (liftSlot t ht j:OtherVars s b e k)) i₀) =
      Polynomial.X:= by
    change E (C (z9v (liftSlot t ht i₀)) *
      z9v 0^0*z9v 1^0)= _
    simp only [pow_zero,mul_one,E,AlgEquiv.trans_apply,sumAlgEquiv_symm_C_X]
    change (optionEquivLeft L _) (renameEquiv L (zk4 v).symm (z9v v))= _
    rw [renameEquiv_apply,rename_X,Equiv.optionSubtypeNe_symm_self,optionEquivLeft_X_none]
  have ht' : ∃ r,E (raw t ht:Raw s b e k)=z7y+Polynomial.C r := by
    rw [raw,← Finset.sum_erase_add _ _ (Finset.mem_univ i₀),map_add,hr]
    · rw [hv]
      exact ⟨_,add_comm _ _⟩
    · intro i hi h
      apply (Finset.ne_of_mem_erase hi)
      have he :=congrArg (fun a :OtherVars s b e k=>a.val) (Sum.inr.inj h)
      simpa [liftSlot,v] using he
  have hu' : ∃ r,E (raw u hu:Raw s b e k)=z1z r := by
    rw [raw,hr]
    · exact ⟨_,rfl⟩
    · intro i _ h
      apply htu.symm
      exact congrArg (fun a :OtherVars s b e k=>a.val.1) (Sum.inr.inj h)
  obtain ⟨r,htr⟩:=ht'
  obtain ⟨q,hqu⟩:=hu'
  refine ⟨(MulEquiv.prime_iff E.toRingEquiv.toMulEquiv).mp ?_,fun h => ?_⟩
  · change Prime (E (raw t ht:Raw s b e k))
    rw [htr]
    simpa [sub_eq_add_neg] using Polynomial.prime_X_sub_C (-r)
  · have hd:=Polynomial.natDegree_le_of_dvd (_root_.map_dvd E h)
      ((map_ne_zero_iff _ E.injective).mpr (fTY u hu).1)
    simp [htr,hqu] at hd
theorem pair_prime (t u:Fin 3) (ht:t≠k) (hu:u≠k) (htu:t≠u)
   (he :0<e t) :Prime (pairForm s b e k t) ∧
     ¬ pairForm s b e k t∣pairForm s b e k u:= by
 let R:=PairCoeffs s b e k
 let P:=Raw s b e k
 let Q:=lK s b e k
 let M:Submonoid P:=(nonZeroDivisors R).map znf
 let f :P:=raw t ht
 let g:P:=raw u hu
 let J:Ideal P:=zye {f}
 have ⟨hp,hg⟩:=raw_prime (s :=s) (b:=b) (e :=e) t u ht hu htu
 have hJ:J.IsPrime :=Ideal.isPrime_span_singleton_of_prime hp
 have q1 :Disjoint (M:Set P) (J:Set P) := by
   refine Set.disjoint_left.mpr ?_
   rintro _ ⟨r,hr,rfl⟩ hm
   obtain ⟨p,hp'⟩:=Ideal.mem_span_singleton.mp hm
   have h0: (C r :P)≠0:=(map_ne_zero_iff _ (C_injective _ _)).mpr
     (mem_nonZeroDivisors_iff_ne_zero.mp hr)
   have hp0:p≠0:= by
     intro hz
     apply h0
     rw [hp',hz,mul_zero]
   have hd:=congrArg (weightedTotalDegree (weights s 1)) hp'
   rw [weightedTotalDegree_C,weightedTotalDegree_mul _ _ _ hp.ne_zero hp0,
     (fTY (s :=s) (b:=b) (e :=e) t ht).2 1] at hd
   simp [caps] at hd
   omega
 have q2 :J.map (algebraMap P Q)=zye {pairForm s b e k t} := by
   rw [Ideal.map_span,zyl,bIV]
 have q0:=IsLocalization.isPrime_of_isPrime_disjoint M Q J hJ q1
 rw [q2] at q0
 refine ⟨(Ideal.span_singleton_prime (pair_caps t ht).1).mp q0,?_⟩
 intro hd
 apply hg
 apply Ideal.mem_span_singleton.mp
 have hm:g∈(J.map (algebraMap P Q)).under P:= by
   change algebraMap P Q g∈J.map (algebraMap P Q)
   rw [q2,bIV]
   exact Ideal.mem_span_singleton.mpr hd
 rwa [IsLocalization.under_map_of_isPrime_disjoint M Q hJ q1] at hm
end
end qVEB2pd
end
section
namespace qVEB2pd
noncomputable section
open P5_7_1_7_4_3_4 (pairDegree)
open qBl3Pad (PairAlgebra MY lK Ib pairForm ng)
private theorem finish {s :ℕ} {b e :Fin 3→ℕ} {k j l:Fin 3}
   (hj:j≠k) (hl:l≠k) (hjl:j≠l) (he :0<e j)
   (h : {t:Fin 3 | t≠k} = {j,l})
   (ha :ng s b e k=pairDegree s (b j) (e j) (b l) (e l)) :
   zAa (MY s b e k) (PairAlgebra s b e k) ∧
     zsE (MY s b e k) (PairAlgebra s b e k)≤ng s b e k := by
 have hi:Ib s b e k=ke (pairForm s b e k j) (pairForm s b e k l) := by
   rw [Ib,h,Set.image_insert_eq,zyl]
 obtain ⟨_,hdj⟩:=pair_caps (s :=s) (b:=b) (e :=e) j hj
 obtain ⟨hnl,hdl⟩:=pair_caps (s :=s) (b:=b) (e :=e) l hl
 change zAa _ (lK s b e k ⧸ Ib s b e k) ∧
   zsE _ (lK s b e k ⧸ Ib s b e k)≤_
 rw [hi,ha]
 obtain ⟨hp,hc⟩:=pair_prime (s :=s) (b:=b) (e :=e) j l hj hl hjl he
 exact eJB _ _ _ _ _ hp hnl hc hdj hdl
theorem proof :qBl3Pad.c1 := by
 intro s b e he _ k
 fin_cases k
 · exact finish (j:=1) (l:=2) (by decide) (by decide) (by decide) (he _)
    (by ext t; fin_cases t <;> decide) rfl
 · exact finish (j:=0) (l:=2) (by decide) (by decide) (by decide) (he _)
    (by ext t; fin_cases t <;> decide) rfl
 · exact finish (j:=0) (l:=1) (by decide) (by decide) (by decide) (he _)
    (by ext t; fin_cases t <;> decide) rfl
end
end qVEB2pd
end
end
section
namespace qLXGHAd
open qBl3Pad
open q2tSkEc (caps orders)
open private ags from ProximityPrize.SubmissionLower.Z877yta
theorem proof :qEAs6me.c1 := by
 intro s b d hd
 have he : ∀ t,0<orders d t:= by
  intro t
  fin_cases t <;> simp [orders] <;> omega
 have hb:0<caps b s 1 := by simp [caps]
 have hpair :=qVEB2pd.proof s (caps b s) (orders d) he hb
 have hnorm:=qDttdYd.proof s (caps b s) (orders d) he hb
 obtain ⟨Q,hQ,hQ0,_⟩:=hnorm 0 (hpair 0).1
 obtain ⟨R,_,hR0,hdiv⟩ :=
  qOuTtVa.proof s (caps b s) (orders d) he hb ⟨Q,hQ,hQ0⟩
 refine ⟨R,ags R (fun k => ?_),hR0,hdiv⟩
 obtain ⟨Qk,hQk,hk0,hdeg⟩:=hnorm k (hpair k).1
 exact (MvPolynomial.weightedTotalDegree_le_of_dvd _ (hdiv _ hk0) hQk).trans
  (hdeg.trans (hpair k).2)
end qLXGHAd
end
section
namespace qVAMdHe
noncomputable section
open cu (L)
open q2tSkEc (bzm caps orders)
open qEAs6me (Coeff topSlot tied)
open qfbIfsd (Slot)
open scoped BigOperators Classical
def first (s b d:ℕ) :bzm s b d :=
 ⟨0,topSlot s b d 0 ⟨0,Nat.zero_lt_succ _⟩⟩
def rL (s b d:ℕ) :bzm s b d :=
 ⟨2,topSlot s b d 2 ⟨0,Nat.zero_lt_succ _⟩⟩
abbrev E8 (s b d:ℕ) := {r :bzm s b d // r≠first s b d}
abbrev tu (s b d:ℕ) :=z3y (E8 s b d) L
abbrev kB (s b d:ℕ) :=FractionRing (tu s b d)
abbrev Ext (s b d:ℕ) :=AlgebraicClosure (kB s b d)
def view (s b d:ℕ) :Coeff s b d ≃ₐ[L] zM1 (tu s b d) :=
  (MvPolynomial.renameEquiv L (zk4 (first s b d)).symm).trans
    (MvPolynomial.optionEquivLeft L (E8 s b d))
theorem view_var {s b d:ℕ} (r :bzm s b d) :
   view s b d (z9v r) =
    if h:r≠first s b d then z1z (z9v ⟨r,h⟩)
    else Polynomial.X:= by
 by_cases hr :r≠first s b d
 · simp [view,zyk,zFr hr,hr,
    MvPolynomial.optionEquivLeft_X_some]
 · have he :r=first s b d:=not_ne_iff.mp hr
   subst r
   simp [view,zyk,MvPolynomial.optionEquivLeft_X_none]
theorem view_const {s b d:ℕ} (k :L) :
  view s b d (znf k)=z1z (znf k) := by
 simp [view,zyk,MvPolynomial.optionEquivLeft_C]
def emb (s b d:ℕ) :tu s b d →+* Ext s b d :=
 (algebraMap (kB s b d) (Ext s b d)).comp (algebraMap (tu s b d) (kB s b d))
def ek (s b d:ℕ) (r :bzm s b d) :Ext s b d :=
 if h:r≠first s b d then emb s b d (z9v ⟨r,h⟩) else 0
def insertU {M:Type} {s b d:ℕ} (a :bzm s b d→M) (u:M)
    (r :bzm s b d) :M :=
  if r=first s b d then u else a r
theorem view_generic {s b d:ℕ} (r :bzm s b d) :
   (view s b d (z9v r)).map (emb s b d) =
     insertU (z1z ∘ ek s b d) z7y r := by
 rw [view_var]
 by_cases hr :r=first s b d <;> simp [hr,ek,insertU]
def deformArg {M:Type} [CommSemiring M] {s b d:ℕ}
    (a :bzm s b d→M) (u e :M) (r :bzm s b d) :M :=
  tied (insertU a u) r+if r=rL s b d then e else 0
def rev {M:Type} [CommSemiring M] {s b d:ℕ} (a :bzm s b d→M)
    (t:Fin 3) (x v :M) :M :=
  ∑ i:Slot s (caps b s t) (orders d t),
    a ⟨t,i⟩*x^i.2.val*v^(orders d t - i.1.val)
def jet {M:Type} [CommSemiring M] {s b d:ℕ} (a :bzm s b d→M)
    (t:Fin 3) (x :M) :M :=
  ∑ i:Slot s (caps b s t) (orders d t),
    if orders d t - i.1.val=1 then a ⟨t,i⟩*x^i.2.val else 0
def delta {M:Type} [CommRing M] {s b d:ℕ}
    (a :bzm s b d→M) (x :M) :M :=
  jet a 2 x-(d:M)*jet a 0 x
def deform {s b d:ℕ} (R:Coeff s b d) :zM1 (PowerSeries (Ext s b d)) :=
  MvPolynomial.eval₂ (Polynomial.C.comp (PowerSeries.C.comp ((emb s b d).comp znf)))
    (deformArg (z1z ∘ PowerSeries.C ∘ ek s b d) z7y
      (z1z PowerSeries.X)) R
end
end qVAMdHe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qVAMdHe
noncomputable section

open q2tSkEc (bzm caps)
open qEAs6me (Coeff topSlot topPoly topRes topPoly_map coeff_topPoly topPoly_degree)
open scoped BigOperators Classical
variable {s b d:ℕ}
private theorem top_first :
    topPoly (insertU (z1z ∘ ek s b d) z7y) 0 =
      z1z z7y+(topPoly (ek s b d) 0).map Polynomial.C:= by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_add,Polynomial.coeff_C,Polynomial.coeff_map,coeff_topPoly,coeff_topPoly]
  by_cases h:i<caps b s 0+1
  · simp only [dite_eq_left h]
    by_cases hi:i=0
    · subst i
      simp [first,insertU,ek]
    · have hj: (⟨0,topSlot s b d 0 ⟨i,h⟩⟩:bzm s b d)≠first s b d :=
        fun he=>hi (congrArg (fun v :bzm s b d=>v.2.2.val) he)
      simp [insertU,hi,hj]
  · simp only [dite_eq_right h]
    change ¬ i<b+1 at h
    have hi:i≠0:= by omega
    simp [hi]
private theorem top_second :
   topPoly (insertU (z1z ∘ ek s b d) z7y) 1 =
     (topPoly (ek s b d) 1).map Polynomial.C:= by
 rw [topPoly_map]
 unfold topPoly
 apply Finset.sum_congr rfl
 intro j _
 have hj: (⟨1,topSlot s b d 1 j⟩:bzm s b d)≠first s b d:= by
   intro he
   have hh:=congrArg Sigma.fst he
   change (1 :Fin 3)=0 at hh
   exact (by decide : (1 :Fin 3)≠0) hh
 rw [insertU,ite_eq_right hj]
theorem resultant_factor (a :Fin (b+s+1)→Ext s b d) (ha :zq4 a)
    (hg: (topPoly (ek s b d) 1).natDegree=b+s+1)
    (hz : ∀ i,(topPoly (ek s b d) 1).eval (a i)=0) :
    (view s b d (topRes :Coeff s b d)).map (emb s b d) =
      z1z ((-1)^(b*(b+s+1))*(topPoly (ek s b d) 1).leadingCoeff^b) *
        ∏ i,(z7y-Polynomial.C (-(topPoly (ek s b d) 0).eval (a i))) := by
  let E :=Ext s b d
  let f :zM1 E :=topPoly (ek s b d) 0
  let g:zM1 E :=topPoly (ek s b d) 1
  let c:E →+* zM1 E :=z1z
  let f' : zM1 (zM1 E) :=z1z z7y+f.map c
  let g' : zM1 (zM1 E) :=g.map c
  let φ:=(zhd (emb s b d)).comp (view s b d).toRingHom
  have hv :φ ∘ z9v=insertU (z1z ∘ ek s b d) Polynomial.X :=
    funext view_generic
  have hm: (view s b d (topRes :Coeff s b d)).map (emb s b d)=f'.resultant g' b (b+s+1) := by
    change φ topRes= _
    rw [topRes,← Polynomial.resultant_map_map _ _ _ _ φ,topPoly_map,topPoly_map,hv,
      top_first,top_second]
  have hf' : f'.natDegree≤b:= by
    simpa [f',f] using (topPoly_degree (ek s b d) 0)
  have hg' : g'.natDegree=b+s+1 :=
    (Polynomial.natDegree_map_eq_of_injective zmy g).trans hg
  have hne :g≠0:= by
    intro h
    change g.natDegree= _ at hg
    simp [h] at hg
  have hsplit :g.Splits :=IsAlgClosed.splits g
  let r :Multiset E :=Finset.univ.val.map a
  have hr :r=g.roots := by
    apply Multiset.eq_of_le_of_card_le
    · apply (Multiset.le_iff_subset (Finset.univ.nodup.map ha)).mpr
      intro x hx
      obtain ⟨i,_,rfl⟩:=Multiset.mem_map.mp hx
      exact (Polynomial.mem_roots hne).mpr (hz i)
    · rw [hsplit.natDegree_eq_card_roots.symm,hg]
      simp [r]
  have hresult :g'.resultant f' (b+s+1) b=g'.leadingCoeff^b*(g'.roots.map f'.eval).prod:= by
    simpa only [hg'] using Polynomial.resultant_eq_prod_eval g' f' b hf' (hsplit.map c)
  rw [hm,Polynomial.resultant_comm,hresult]
  rw [show g'.roots=r.map c from hr ▸ hsplit.roots_map_of_injective zmy]
  rw [show g'.leadingCoeff=z1z g.leadingCoeff from
    z0W zmy g]
  simp only [r,Multiset.map_map,Function.comp_apply,Finset.prod_map_val,f',Polynomial.eval_add,
    Polynomial.eval_C,Polynomial.eval_map_apply,c,map_neg,sub_neg_eq_add,map_mul,map_pow,
    map_one,mul_assoc,f,g]
  rfl
end
end qVAMdHe
end
section
set_option backward.isDefEq.respectTransparency false
namespace qVAMdHe
noncomputable section
open cu (L)
open q2tSkEc (bzm caps)
open qEAs6me (Coeff topSlot topPoly topRes coeff_topPoly)
open private witness topRes_witness from ProximityPrize.SubmissionLower.ZEMNtxd
open scoped BigOperators Classical
variable {s b d:ℕ}
private def lead (s b d:ℕ) :E8 s b d :=
 ⟨⟨1,topSlot s b d 1 ⟨b+s+1,Nat.lt_succ_self _⟩⟩,by
   intro h
   exact (by decide : (1 :Fin 3)≠0) (congrArg Sigma.fst h)⟩
private theorem lead_witness :
  witness (1 :L) (lead s b d).val=0:= by
 simp [witness,lead,topSlot,show (1 :Fin 3)≠0 by decide]
private theorem no_lead_factor :
    ¬ z1z (z9v (lead s b d))∣view s b d (topRes :Coeff s b d) := by
  let a :bzm s b d→L:=witness 1
  let ψ:tu s b d →+* L:=zOD (zz4 L) (a ∘ Subtype.val)
  let φ:=(Polynomial.evalRingHom (a (first s b d))).comp (zhd ψ)
  let e :=zOD (zz4 L) a
  have hφ:φ.comp (view s b d).toRingHom=e := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [φ,ψ,e,view_const]
    · intro r
      change φ (view s b d (z9v r))=e (z9v r)
      rw [view_var]
      by_cases hr :r≠first s b d
      · simp [φ,ψ,e,hr]
      · have he :=not_ne_iff.mp hr
        subst r
        simp [φ,e]
  have h0:φ (z1z (z9v (lead s b d)))=0:= by
    simpa [φ,ψ,a] using (lead_witness (s :=s) (b:=b) (d:=d))
  have h1 :φ (view s b d (topRes :Coeff s b d))=1 := by
    rw [show φ (view s b d (topRes :Coeff s b d))=e topRes from DFunLike.congr_fun hφ _]
    change (topRes :Coeff s b d).eval₂ (zz4 L) (witness 1)=1
    rw [topRes_witness,one_pow]
  intro h
  have hh:=map_dvd φ h
  rw [h0,h1] at hh
  exact one_ne_zero (zero_dvd_iff.mp hh)
theorem primitive (a :Fin (b+s+1)→Ext s b d) (ha :zq4 a)
   (hg: (topPoly (ek s b d) 1).natDegree=b+s+1)
   (hz : ∀ i,(topPoly (ek s b d) 1).eval (a i)=0) :
   (view s b d (topRes :Coeff s b d)).IsPrimitive := by
 let p:=view s b d (topRes :Coeff s b d)
 let z :=z9v (lead s b d) (R:=L)
 let n:=b*(b+s+1)
 have ht: (topPoly (ek s b d) 1).leadingCoeff=emb s b d z := by
   have hm:b+s+1<caps b s 1+1 :=Nat.lt_succ_self _
   rw [← zkZ,hg,coeff_topPoly,dite_eq_left hm]
   change ek s b d (lead s b d).val= _
   exact dite_eq_left (lead s b d).property
 have hι:zq4 (emb s b d) :=
   (RingHom.injective (algebraMap (kB s b d) (Ext s b d))).comp
     (zxb (tu s b d) (kB s b d))
 have hlead:p.leadingCoeff=(-1)^n*z^b:= by
   let q:zM1 (Ext s b d) :=
     ∏ i,(z7y-Polynomial.C (-(topPoly (ek s b d) 0).eval (a i)))
   have hq:q.Monic:=Polynomial.monic_prod_of_monic _ _ fun _ _=>Polynomial.monic_X_sub_C _
   apply hι
   rw [← z0W hι,show p.map (emb s b d)= _ from
     resultant_factor a ha hg hz]
   change (z1z ((-1)^n*(topPoly (ek s b d) 1).leadingCoeff^b)*q).leadingCoeff= _
   rw [Polynomial.leadingCoeff_mul,Polynomial.leadingCoeff_C,hq.leadingCoeff,mul_one,ht]
   simp
 apply Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
 intro r hr
 have hh:=(Polynomial.C_dvd_iff_dvd_coeff r p).mp hr p.natDegree
 rw [zkZ,hlead] at hh
 have hrz :r∣z^b:=((isUnit_neg_one (α:=tu s b d)).pow n).dvd_mul_left.mp hh
 obtain ⟨i,_,hi⟩:=(dvd_prime_pow (show Prime z from MvPolynomial.X_prime) b).mp hrz
 by_cases h:i=0
 · exact hi.symm.isUnit (by rw [h,pow_zero]; exact isUnit_one)
 · have hzpow:z∣z^i:= by simpa only [pow_one] using pow_dvd_pow z (Nat.pos_of_ne_zero h)
   have hz' := hzpow.trans hi.symm.dvd
   exact (no_lead_factor ((map_dvd Polynomial.C hz').trans hr)).elim
end
end qVAMdHe
end
