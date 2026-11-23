import ProximityPrize.SubmissionLower.ZpTf9za
import ProximityPrize.SubmissionLower.ZaLaX1b
import ProximityPrize.SubmissionLower.BE
import ProximityPrize.SubmissionLower.DG
import ProximityPrize.SubmissionLower.E2
import ProximityPrize.SubmissionLower.E5
import ProximityPrize.SubmissionLower.ZYswgKc
import ProximityPrize.SubmissionLower.ZCvigsb
import ProximityPrize.SubmissionLower.ZskDvCd
import ProximityPrize.SubmissionLower.P6Defs
set_option Elab.async false
section
open _root_ renaming CommRing→ ov,Function.Injective→ oy,Ideal→c9,Ideal.Quotient.eq_zero_iff_mem→ oj,Ideal.Quotient.mk→aU,Ideal.Quotient.mk_eq_mk_iff_sub_mem→pU,Ideal.Quotient.mk_surjective→pz,Ideal.comap_mono→ oK,Ideal.map_mono→ oZ,Ideal.mem_map_of_mem→ oD,Ideal.span_singleton_le_iff_mem→p6,IsLeftRegular→nq,Localization.Away→pG,MvPolynomial→cy,MvPolynomial.C→ ox,MvPolynomial.X→lV,MvPolynomial.affineDegree→lz,MvPolynomial.affineHilbertFunction→ oz,MvPolynomial.eventually_eval_affineHilbertPolynomial→pL,MvPolynomial.quotientDegreeLE→lI,MvPolynomial.quotientDegreeLE_mono→n5,Submodule.add_mem→pQ,Submodule.map_mono→p7,Submodule.smul_mem→ oY,Submodule.sum_mem→p5,aRU.saturate→nX,congrArg→ oq,dN.GeoJets→nI,map_mul→lJ,mul_le_mul_of_nonneg_left→pC,rW.dimension→mD
section
namespace aRU
noncomputable section
open aR dN rW wH Rl ap9 MvPolynomial
theorem Yq {R:Type*} [ov R] (I:c9 R) (d:R) :I≤ nX I d :=
 fun _ hx ↦ oD (algebraMap R (pG d)) hx
theorem saturate_mono {R:Type*} [ov R] {I J:c9 R} (h:I≤J) (d:R) :
  nX I d≤ nX J d :=
 oK (oZ h)
private theorem mem_saturate_iff {R:Type*} [ov R] (I:c9 R) (d x :R) :
   x∈nX I d ↔ ∃ n:ℕ,d^n*x∈I:= by
 change algebraMap R (pG d) x∈I.map _↔_
 rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers d)]
 simp only [Submonoid.mem_powers_iff]
 constructor
 · rintro ⟨_,⟨n,rfl⟩,hn⟩
   exact ⟨n,hn⟩
 · rintro ⟨n,hn⟩
   exact ⟨d^n,⟨n,rfl⟩,hn⟩
theorem regular_saturate {R:Type*} [ov R] (I:c9 R) (d:R) :
  nq (aU (nX I d) d) := by
 apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
 intro x hx
 obtain ⟨p,rfl⟩:=pz x
 rw [← lJ,oj,mem_saturate_iff] at hx
 obtain ⟨n,hn⟩:=hx
 rw [oj,mem_saturate_iff]
 exact ⟨n+1,by rwa [pow_succ,mul_assoc]⟩
def adP {f :af 4} (T:Li f) (H :UF) :GeoJets :=
  ox (ni H.offset)*bC T.denom +
    ∑ i,ox (ni (H.slope i))*bC (T.Fr i)
theorem epE {f :af 4} (T:Li f) (H :UF) :
   (adP T H).totalDegree≤(rH (shape f)).b:= by
 let b:=(rH (shape f)).b
 have hmap (p:af 4) (hp:p.totalDegree≤b) :
     bC p∈restrictTotalDegree (Fin 4) GeoField b:= by
   rw [mem_restrictTotalDegree]
   exact (Finset.sup_mono (support_map_subset j8 p)).trans hp
 rw [← mem_restrictTotalDegree]
 apply pQ
 · rw [← smul_eq_C_mul]
   exact oY _ _ (hmap T.denom T.denom_box.1)
 · apply p5
   intro i _
   rw [← smul_eq_C_mul]
   exact oY _ _ (hmap (T.Fr i) (T.numer_box i).1)
theorem cVN {f :af 4} {T:Li f} {A:kT} (hA:XP f T A)
    {B:c9 mK} (hAB:gN A≤B) (H :UF) :
    aU B (mS (adP T H)) =
      aU B (mS (bC T.denom)) *
        aU B H.aoc:= by
  let e :=aU B
  let d:=mS (bC T.denom)
  have hC (a :GeoField) :mS (ox a)=ox a :=
    eval₂Hom_C _ _ a
  have hre (i:Fin bf) :
      e (mS (bC (T.Fr i)))=e d*e (lV i) := by
    rw [← lJ,mul_comm,eq_comm]
    exact (pU _ _).mpr (hAB (hA.ar5 i))
  change e (mS (adP T H))=e d*e H.aoc
  simp only [adP,UF.aoc,UF.form,map_add,lJ,
    map_sum,MvPolynomial.map_C,MvPolynomial.map_X,hC,hre,d]
  rw [mul_add,Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    ac_rfl
theorem jetCut_mem {f :af 4} {T:Li f} {A:kT} (hA:XP f T A)
  {B:c9 mK} (hAB:gN A≤B) {H :UF}
  (hH :H.aoc∈B) :adP T H∈B.comap mS:= by
 change mS (adP T H)∈B
 rw [← oj,cVN hA hAB,
  Ideal.Quotient.eq_zero_iff_mem.mpr hH,mul_zero]
theorem jetCut_regular {f :af 4} {T:Li f} {A:kT} (hA:XP f T A)
   {B:c9 mK} (hAB:gN A≤B) {H :UF}
   (hD:nq (aU B (mS (bC T.denom))))
   (hH :nq (aU B H.aoc)) :
   nq (aU (B.comap mS) (adP T H)) := by
 let φ: (nI ⧸ B.comap mS) →+* (mK ⧸ B) :=
   Ideal.quotientMap B mS le_rfl
 have hφ:oy φ:=Ideal.quotientMap_injective
 have hmap :φ (aU _ (adP T H)) =
     aU B (mS (bC T.denom))* aU B H.aoc :=
   cVN hA hAB H
 intro x y hxy
 apply hφ
 apply hD.mul hH
 simpa only [lJ,hmap] using oq φ hxy
end
end aRU
end
section
namespace aRU
noncomputable section
open aR dN rW NS wH Rl ap9 MvPolynomial
def c1 :Prop :=
  ∀ (A:kT),A.IsPrime→(gN A).IsPrime→mD A=3 →
    ∀ (d:mK),d∉gN A→Nonempty (gOO A d)
def c2 :Prop :=
  ∀ (I:c9 mK) (D:nI),
    nq (aU I (mS D)) →
    (∀ i:Fin bf,∃ n:nI,
      lV i*mS D - mS n∈I) →
    mD I=1→ahc I (J1 rI 0) →
    mD (I.comap mS)=1∧lz I≤lz (I.comap mS)
private theorem boundary_mono {I J:c9 mK} (h:I≤J) :
  lW I≤lW J:= by
 apply Ideal.span_mono
 rintro _ ⟨p,n,hp,hdeg,rfl⟩
 exact ⟨p,n,h hp,hdeg,rfl⟩
private theorem retained_value_reduction {A:kT} {d:mK}
  (S:gOO A d) :
  ahc (c8I A d S.first S.second) (J1 rI 0) := by
 apply cyz.proof
 intro x hx hvalue
 apply eEP _ S.boundary_finite x _ hvalue
 exact zeroLocus_anti_mono
  (boundary_mono (Yq (gN (cGr A S.first S.second)) d)) hx
private theorem fVF {B:c9 mK} (hB:B.IsPrime)
  {p:mK} (hp:p∉B) :nq (aU B p) := by
 let _:=hB
 exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
  (mt Ideal.Quotient.eq_zero_iff_mem.mp hp)
set_option maxHeartbeats 800000 in
theorem of_children (h1 :c1) (h2 :c2) :ap9.c4 := by
 intro f T A hA hChart hdim
 let D:=bC T.denom
 let d:=mS D
 have hd:d∉gN A:=hChart.denom
 obtain ⟨S⟩:=h1 A hA.prime hChart.extended_prime hdim d hd
 let B:=fXp A d S.first
 let C:=c8I A d S.first S.second
 let Q:=B.comap mS
 let R:=C.comap mS
 let b:=(rH (shape f)).b
 have hAB:gN A≤B :=
   (oZ (brD A S.first.form)).trans (Yq _ d)
 have hBC:B≤C:=saturate_mono (oZ (brD _ S.second.form)) d
 have hfirst:S.first.aoc∈B :=
   Yq _ d (oD _ (cZ2 A S.first.form))
 have hsecond:S.second.aoc∈C :=
   Yq _ d (oD _ (cZ2 _ S.second.form))
 have hJQ:cut (lA A) (adP T S.first)≤Q :=
   sup_le (oK hAB) ((p6 _).mpr
     (jetCut_mem hChart hAB hfirst))
 have hQR:cut Q (adP T S.second)≤R :=
   sup_le (oK hBC) ((p6 _).mpr
     (jetCut_mem hChart (hAB.trans hBC) hsecond))
 have hU:=c7S hJQ
   (jetCut_regular hChart le_rfl (fVF hChart.extended_prime hd)
     (fVF hChart.extended_prime S.first_proper))
   (epE T S.first)
 have hV:=c7S hQR
   (jetCut_regular hChart hAB (regular_saturate _ d) S.second_regular)
   (epE T S.second)
 have hR:mD R=1∧lz C≤lz R :=
   h2 C D (regular_saturate _ d)
     (fun i ↦ ⟨bC (T.Fr i),(hAB.trans hBC) (hChart.ar5 i)⟩)
     S.cIP (retained_value_reduction S)
 have hthree :mD (lA A)=3:=hChart.dimension_eq.trans hdim
 have htwo:mD Q=2 := by
   have hu:=hU.1
   have hv :=hV.1
   omega
 have hfirstDegree :=hU.2 (by omega)
 have hsecondDegree :=hV.2 (by have :=hR.1; omega)
 calc
   lz A=lz C:=S.cIO.symm
   _≤lz R:=hR.2
   _≤(b:ℚ)*lz Q:=hsecondDegree
   _≤(b:ℚ)*((b:ℚ)*lz (lA A)) :=
     pC hfirstDegree (by positivity)
   _=lz (lA A)*(b:ℚ)^2 := by ring
end
end aRU
end
section
namespace dnh
noncomputable section
open Filter MvPolynomial Polynomial
open aR dN rW NS
section Filtration
variable {k σ τ:Type*} [Field k]
variable {I:c9 (cy σ k)} {J:c9 (cy τ k)}
private theorem afo
   (g: (cy τ k ⧸ J) →ₐ[k] (cy σ k ⧸ I))
   (d:cy τ k ⧸ J)
   (hgen : ∀ i,∃ a,g d* aU I (lV i)=g a)
   (x :cy σ k ⧸ I) :
   ∃ (e :ℕ) (a :cy τ k ⧸ J),g d^e*x=g a := by
 obtain ⟨p,rfl⟩:=pz x
 induction p using MvPolynomial.induction_on with
 | C c =>
   refine ⟨0,algebraMap k _ c,?_⟩
   rw [pow_zero,one_mul]
   exact (g.commutes c).symm
 | add p q hp hq =>
   obtain ⟨e,a,ha⟩:=hp
   obtain ⟨f,b,hb⟩:=hq
   refine ⟨e+f,d^f*a+d^e*b,?_⟩
   simp only [map_add,lJ,map_pow,pow_add,mul_add]
   calc
     _=g d^f*(g d^e* aU I p) +
         g d^e*(g d^f* aU I q) := by ac_rfl
     _ = _:= by rw [ha,hb]
 | mul_X p i hp =>
   obtain ⟨e,a,ha⟩:=hp
   obtain ⟨b,hb⟩:=hgen i
   refine ⟨e+1,a*b,?_⟩
   simp only [lJ,pow_succ]
   calc
     _=(g d^e* aU I p) *
         (g d* aU I (lV i)) := by ac_rfl
     _ = _:= by rw [ha,hb]
private abbrev bex
   (g: (cy τ k ⧸ J) →ₐ[k] (cy σ k ⧸ I)) (n:ℕ) :=
 (lI J n).map g.toLinearMap
variable [Finite σ] [Finite τ]
private theorem cUO
    (g: (cy τ k ⧸ J) →ₐ[k] (cy σ k ⧸ I))
    (d:cy τ k ⧸ J) (hd:nq (g d))
    (hgen : ∀ j,∃ a,g d* aU I (lV j)=g a)
    (i:τ) {ℓ:cy σ k}
    (hℓ:g (aU J (lV i))=aU I ℓ)
    (hred:ahc I ℓ) :
    ∃ C:ℕ,∀ n:ℕ,oz I n≤oz J (n+C) := by
  classical
  obtain ⟨N,hN⟩:=hred
  let B:=Module.finBasis k (lI I N)
  choose e a ha using fun j ↦ afo g d hgen (B j:cy σ k ⧸ I)
  obtain ⟨E,hE⟩:=Finite.exists_le e
  let Fr := fun j ↦ d^(E-e j)*a j
  have hclear (j:Fin (Module.finrank k (lI I N))) :
      g d^E*(B j:cy σ k ⧸ I)=g (Fr j) := by
    calc
      _=g d^(E-e j)*(g d^e j*(B j:cy σ k ⧸ I)) := by
        rw [← mul_assoc,← pow_add,Nat.sub_add_cancel (hE j)]
      _ = _:= by rw [ha j]; simp only [Fr,lJ,map_pow]
  choose levels hlevels using fun j ↦ exists_mem_quotientDegreeLE J (Fr j)
  obtain ⟨C,hC⟩:=Finite.exists_le levels
  have hbase (x :cy σ k ⧸ I) (hx :x∈lI I N) :
      g d^E*x∈bex g C:= by
    let z :lI I N :=⟨x,hx⟩
    have hz : (∑ j,(B.repr z j)•(B j:cy σ k ⧸ I))=x := by
      simpa only [map_sum,map_smul,Submodule.subtype_apply] using
        oq (lI I N).subtype (B.sum_repr z)
    rw [← hz,Finset.mul_sum]
    refine p5 _ fun j _ ↦ ?_
    rw [show g d^E*((B.repr z j)•(B j:cy σ k ⧸ I)) =
      (B.repr z j)•(g d^E*(B j:cy σ k ⧸ I)) from
        Algebra.mul_smul_comm (B.repr z j) (g d^E) (B j:cy σ k ⧸ I),hclear j]
    apply oY
    exact Submodule.mem_map.mpr ⟨_,n5 J (hC j) (hlevels j),rfl⟩
  have hall (n:ℕ) : ∀ x∈lI I n,g d^E*x∈bex g (n+C) := by
    induction n with
    | zero =>
      intro x hx
      simpa using hbase x (n5 I (Nat.zero_le N) hx)
    | succ n ih =>
      intro x hx
      by_cases hn:N≤n
      · obtain ⟨u,hu,v,hv,rfl⟩:=hN n hn x hx
        obtain ⟨s,hs,he⟩:=Submodule.mem_map.mp (ih v hv)
        change g s=g d^E*v at he
        rw [mul_add,mul_left_comm (g d^E),← hℓ]
        apply pQ
        · exact p7 (n5 J (by omega)) (ih u hu)
        · change g _ *(g d^E*v)∈_
          rw [← he,← lJ]
          exact Submodule.mem_map.mpr ⟨_,by
            simpa only [Nat.add_left_comm,Nat.add_comm,Nat.add_assoc] using
              mul_mem_quotientDegreeLE (mk_X_mem_quotientDegreeLE J i) hs,rfl⟩
      · exact p7 (n5 J (Nat.le_add_left C _))
          (hbase x (n5 I (by omega) hx))
  refine ⟨C,fun n ↦ ?_⟩
  let mult:=(LinearMap.mulLeft k (g d^E)).comp (lI I n).subtype
  let m:lI I n →ₗ[k] bex g (n+C) :=
    mult.codRestrict (bex g (n+C)) (fun x ↦ hall n x x.property)
  have hm:oy m:= by
    intro x y hxy
    exact Subtype.ext ((hd.pow E) (oq Subtype.val hxy))
  have hfin:Module.Finite k (bex g (n+C)) := by
    unfold bex
    infer_instance
  exact (LinearMap.finrank_le_finrank_of_injective hm).trans (Submodule.finrank_map_le _ _)
private theorem cJ2
   (g: (cy τ k ⧸ J) →ₐ[k] (cy σ k ⧸ I)) (hg:oy g)
   {C:ℕ} (hupper : ∀ n:ℕ,oz I n≤oz J (n+C)) :
   mD J=mD I∧lz I≤lz J:= by
 let P:=affineHilbertPolynomial I
 let Q:=affineHilbertPolynomial J
 have hshift:Tendsto (fun n:ℕ ↦ n+C) atTop atTop :=
   tendsto_atTop_mono (fun n ↦ Nat.le_add_right n C) tendsto_id
 have hbound : ∀ᶠ n:ℕ in atTop,P.eval (n:ℚ)≤(taylor (C:ℚ) Q).eval (n:ℚ) := by
   filter_upwards [pL I,
     hshift.eventually (pL J)] with n hn hnC
   rw [taylor_eval,← Nat.cast_add,hn,hnC]
   exact_mod_cast hupper n
 have hle :=natDegree_le_of_eventually_eval_natCast_le
   (eventually_eval_affineHilbertPolynomial_nonneg I) hbound
 have hdeg:P.natDegree= Q.natDegree :=
   (hle.1.trans_eq (natDegree_taylor Q _)).antisymm
     (natDegree_affineHilbertPolynomial_le_of_injective g hg)
 have hlc:P.leadingCoeff≤Q.leadingCoeff := by
   simpa only [leadingCoeff_taylor] using hle.2 (hdeg.trans (natDegree_taylor Q _).symm)
 refine ⟨hdeg.symm,?_⟩
 change (P.natDegree.factorial:ℚ)*P.leadingCoeff ≤
   (Q.natDegree.factorial:ℚ)*Q.leadingCoeff
 rw [hdeg]
 exact pC hlc (by positivity)
end Filtration
private def al7:nI →ₐ[GeoField] mK :=
 aeval (fun i:Fin 4 ↦ J1 rI i.val)
private def ZM (I:c9 mK) :
  (nI ⧸ I.comap mS) →ₐ[GeoField] (mK ⧸ I) :=
 Ideal.quotientMapₐ I al7 (fun _ hp ↦ hp)
private theorem aDt (I:c9 mK) (p:nI) :
 ZM I (aU (I.comap mS) p) =
  aU I (mS p) :=rfl
private theorem b6L (I:c9 mK) :oy (ZM I) := by
 apply (injective_iff_map_eq_zero (ZM I)).mpr
 intro z hz
 obtain ⟨p,rfl⟩:=pz z
 rw [aDt,oj] at hz
 exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
theorem proof :aRU.c2 := by
 intro I D hreg hrec hdim hred
 let J:=I.comap mS
 let d:nI ⧸ J:=aU J D
 have hd:nq (ZM I d) :=hreg
 have hgen (i:Fin bf) :
     ∃ a,ZM I d* aU I (lV i)=ZM I a := by
   obtain ⟨p,hp⟩:=hrec i
   refine ⟨aU J p,?_⟩
   rw [show ZM I d=aU I (mS D) from aDt I D,
     aDt,mul_comm,← lJ]
   exact (pU _ _).mpr hp
 have hv :ZM I (aU J (lV (0:Fin 4))) =
     aU I (J1 rI 0) := by
   rw [aDt]
   exact oq (aU I) (eval₂Hom_X' _ _ _)
 obtain ⟨C,hC⟩:=cUO (ZM I) d hd hgen 0 hv hred
 obtain ⟨hdimJ,hdegree⟩:=cJ2 (ZM I) (b6L I) hC
 exact ⟨hdimJ.trans hdim,hdegree⟩
end
end dnh
end
end
section
section
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000
namespace ata
noncomputable section
open aR dN rW NS aRU MvPolynomial
section Parameters
variable {k E σ:Type*} [Field k] [Field E] [Algebra k E] [Fintype σ]
private def Qe : (k×(σ→k)) →ₗ[k] MvPolynomial σ E :=
 ∑ i:σ,((LinearMap.proj i).comp (LinearMap.snd k k (σ→k))).smulRight
   (MvPolynomial.X i)
private def aU0: (k×(σ→k)) →ₗ[k] MvPolynomial σ E :=
 (LinearMap.fst k k (σ→k)).smulRight 1+Qe
private theorem bwC (v :k×(σ→k)) :
  Qe (E :=E) v = ∑ i:σ,C (algebraMap k E (v.2 i))*MvPolynomial.X i:= by
 simp only [Qe,LinearMap.sum_apply,LinearMap.smulRight_apply,
  LinearMap.comp_apply,LinearMap.proj_apply,LinearMap.snd_apply,Algebra.smul_def,
  IsScalarTower.algebraMap_eq k E (MvPolynomial σ E),RingHom.comp_apply,MvPolynomial.algebraMap_eq]
private theorem b3M (v :k×(σ→k)) :
  aU0 (E :=E) v=C (algebraMap k E v.1)+Qe (E :=E) v := by
 simp only [aU0,LinearMap.add_apply,LinearMap.smulRight_apply,LinearMap.fst_apply,
  Algebra.smul_def,IsScalarTower.algebraMap_eq k E (MvPolynomial σ E),
  RingHom.comp_apply,MvPolynomial.algebraMap_eq,mul_one]
private theorem cNF [Infinite k] (I J B:Ideal (MvPolynomial σ E)) :
    ∃ v :k×(σ→k),
      (∀ P∈associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ I),aU0 v∉P) ∧
      (∀ P∈associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ J),aU0 v∉P) ∧
      (∀ P∈associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ B),
        (∃ i:σ,MvPolynomial.X i∉P)→Qe v∉P) := by
  classical
  let S:=associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ I) ∪
    associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ J)
  let T := {P∈associatedPrimes (MvPolynomial σ E) (MvPolynomial σ E ⧸ B) |
    ∃ i:σ,MvPolynomial.X i∉P}
  have hS:S.Finite :=(associatedPrimes.finite _ _).union (associatedPrimes.finite _ _)
  have hT:T.Finite :=(associatedPrimes.finite _ _).subset fun _ hp ↦ hp.1
  let:Finite S:=hS.to_subtype
  let:Finite T:=hT.to_subtype
  let bad:S ⊕ T→Submodule k (k×(σ→k)) :=
    Sum.elim
      (fun P ↦ (P.val.restrictScalars k).comap aU0)
      (fun P ↦ (P.val.restrictScalars k).comap Qe)
  have hbad : ∀ t,bad t ≠ ⊤ := by
    intro t htop
    cases t with
    | inl P =>
      have hprime :P.val.IsPrime :=P.property.elim (·.isPrime) (·.isPrime)
      have hmem: ((1 :k),(0:σ→k))∈bad (.inl P) :=htop ▸ Submodule.mem_top
      change aU0 (1,0)∈P.val at hmem
      rw [b3M,bwC] at hmem
      apply hprime.ne_top
      apply P.val.eq_top_of_isUnit_mem _ isUnit_one
      simpa only [map_one,Pi.zero_apply,map_zero,zero_mul,Finset.sum_const_zero,add_zero] using hmem
    | inr P =>
      obtain ⟨i,hi⟩:=P.property.2
      let v :σ→k := fun j ↦ if j=i then 1 else 0
      have hmem: ((0:k),v)∈bad (.inr P) :=htop ▸ Submodule.mem_top
      change Qe (0,v)∈P.val at hmem
      rw [bwC] at hmem
      have hv : (∑ j:σ,C (algebraMap k E (v j))*MvPolynomial.X j)=MvPolynomial.X i:= by
        rw [Finset.sum_eq_single i]
        · simp [v]
        · intro j _ hji
          simp [v,hji]
        · simp
      exact hi (hv ▸ hmem)
  obtain ⟨v,hv⟩:=Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨v,fun P hP ↦ hv (.inl ⟨P,Or.inl hP⟩),fun P hP ↦ hv (.inl ⟨P,Or.inr hP⟩),
    fun P hP hi ↦ hv (.inr ⟨P,hP,hi⟩)⟩
end Parameters
def freshSlope (H :UF) :mK :=
 ∑ i:Fin bf,C (ni (H.slope i))*MvPolynomial.X i
private theorem br3 {F σ:Type*} [Field F] [Fintype σ] (a :σ→F) :
   (∑ i:σ,C (a i)*MvPolynomial.X i).IsHomogeneous 1 :=
 (homogeneousSubmodule σ F 1).sum_mem fun i _ ↦ isHomogeneous_C_mul_X (a i) i
theorem freshSlope_homogeneous (H :UF) : (freshSlope H).IsHomogeneous 1 :=
 br3 (fun i:Fin bf ↦ ni (H.slope i))
theorem freshForm_eq (H :UF) :
  H.aoc=C (ni H.offset)+freshSlope H := by
 simp only [freshSlope,UF.aoc,UF.form,
  map_add,map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.map_X]
theorem exists_slice (I J B:Ideal mK) :
    ∃ H :UF,
      (∀ P∈associatedPrimes mK (mK ⧸ I),H.aoc∉P) ∧
      (∀ P∈associatedPrimes mK (mK ⧸ J),H.aoc∉P) ∧
      (∀ P∈associatedPrimes mK (mK ⧸ B),
        (∃ i:Fin bf,MvPolynomial.X i∉P)→freshSlope H∉P) := by
  let:Algebra ao GeoField:=ni.toAlgebra
  obtain ⟨v,hp,hq,hb⟩:=cNF (k :=ao) I J B
  let H :UF:=⟨v.1,v.2⟩
  have hSlope :Qe v=freshSlope H :=bwC v
  have hForm:aU0 v=H.aoc:= by
    rw [b3M,hSlope,freshForm_eq]
    rfl
  exact ⟨H,fun P hP ↦ hForm ▸ hp P hP,fun P hP ↦ hForm ▸ hq P hP,
    fun P hP hi ↦ hSlope ▸ hb P hP hi⟩
theorem saturate_eq_of_regular {R:Type*} [CommRing R] (I:Ideal R) (d:R)
  (hd:IsLeftRegular (Ideal.Quotient.mk I d)) :saturate I d=I:= by
 apply le_antisymm _ (Yq I d)
 intro p hp
 change algebraMap R (Localization.Away d) p∈I.map _ at hp
 rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers d)] at hp
 obtain ⟨s,hs,hsp⟩:=hp
 obtain ⟨n,rfl⟩:=(Submonoid.mem_powers_iff s d).mp hs
 have hn:IsLeftRegular (Ideal.Quotient.mk I d^n) :=hd.pow n
 rw [← Ideal.Quotient.eq_zero_iff_mem]
 apply isLeftRegular_iff_right_eq_zero_of_mul.mp hn
 rwa [← map_pow,← map_mul,Ideal.Quotient.eq_zero_iff_mem]
theorem b2D (A:kT) (H :UF) :
  gN (cut A H.form)=cut (gN A) H.aoc:= by
 simp only [gN,cut,UF.aoc,Ideal.map_sup,Ideal.map_span,
  Set.image_singleton]
end
end ata
end
section
namespace ata
noncomputable section
open aR rW NS aRU MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
private theorem cCJ {k σ:Type} [Field k] [Finite σ]
  (I J:Ideal (MvPolynomial σ k)) (hI:0<dimension I)
  (h:affineHilbertPolynomial J=Polynomial.backwardDifference 1 (affineHilbertPolynomial I)) :
  dimension J=dimension I - 1∧affineDegree J=affineDegree I:= by
 obtain ⟨hd,hc⟩:=Polynomial.natDegree_backwardDifference_eq_and_leadingCoeff_of_ne_zero
  (one_ne_zero : (1 :ℚ)≠0) hI
 refine ⟨by simp only [dimension,h,hd],?_⟩
 have hsucc:dimension I - 1+1=dimension I:= by omega
 have hfact :=congrArg Nat.factorial hsucc
 rw [Nat.factorial_succ,hsucc] at hfact
 rw [affineDegree,affineDegree,h,hd,hc,one_mul]
 change _=((dimension I).factorial:ℚ)*_
 rw [← hfact,Nat.cast_mul]
 ring
private theorem c1s (h1 :c1) (h2 :c2) (A:kT)
   (d:mK) (hd:IsLeftRegular (Ideal.Quotient.mk (gN A) d))
   (hA:0<dimension A) :
   ∃ H :UF,
     IsLeftRegular (Ideal.Quotient.mk (gN A) H.aoc) ∧
     IsLeftRegular (Ideal.Quotient.mk (gN (cGz A H)) d) ∧
     dimension (cGz A H)=dimension A - 1 ∧
     affineDegree (gN (cGz A H))=affineDegree (gN A) := by
 let I:=gN A
 obtain ⟨H,hp,hq,hb⟩:=exists_slice I (cut I d) (lW I)
 have hf :=ceZ I H.aoc hp
 have hfd:=ceZ (cut I d) H.aoc hq
 have he :gN (cGz A H)=cut I H.aoc:=b2D A H
 have hm:=h1 (lW I) (freshSlope H) (bBP I)
   (freshSlope_homogeneous H) hb
 have hform :IsLeftRegular (Ideal.Quotient.mk I (C (ni H.offset)+freshSlope H)) := by
   rwa [← freshForm_eq H]
 have hpoly :=h2 I _ _ (freshSlope_homogeneous H) hform hm
 rw [← freshForm_eq H,← he] at hpoly
 have hAext:0<dimension I:= by
   change 0<(affineHilbertPolynomial (gN A)).natDegree
   rw [cyx.proof A]
   exact hA
 obtain ⟨hdim,hdeg⟩:=cCJ I _ hAext hpoly
 refine ⟨H,hf,he.symm ▸ cKo I d H.aoc hd hfd,?_,hdeg⟩
 change (affineHilbertPolynomial (gN (cGz A H))).natDegree =
   (affineHilbertPolynomial (gN A)).natDegree - 1 at hdim
 rw [cyx.proof,cyx.proof] at hdim
 exact hdim
theorem of_children (h1 :c1) (h2 :c2) :aRU.c1 := by
 intro A _ hprime hdim d hd
 let: (gN A).IsPrime :=hprime
 have hreg:IsLeftRegular (Ideal.Quotient.mk (gN A) d) :=
   IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (mt Ideal.Quotient.eq_zero_iff_mem.mp hd)
 obtain ⟨H,hH,hdH,hdimH,hdegH⟩:=c1s h1 h2 A d hreg (by omega)
 let U:=cGz A H
 have hU:dimension U=2 := by dsimp [U]; omega
 obtain ⟨G,hG,hdG,hdimG,hdegG⟩:=c1s h1 h2 U d hdH (by omega)
 let V:=cGr A H G
 have hV:dimension V=1 := by
   change dimension (cGz U G)=1
   omega
 have hs :fXp A d H=gN U:=saturate_eq_of_regular _ _ hdH
 have ht:c8I A d H G=gN V:=saturate_eq_of_regular _ _ hdG
 refine ⟨⟨H,G,?_,hs.symm ▸ hG,?_,?_,cDn V hV⟩⟩
 · intro hh
   have hz :Ideal.Quotient.mk (gN A) H.aoc=0 :=
     Ideal.Quotient.eq_zero_iff_mem.mpr hh
   rw [hz] at hH
   have heq : (0:mK ⧸ gN A)*0=0*1 := by simp
   exact zero_ne_one (hH heq)
 · rw [ht]
   change (affineHilbertPolynomial (gN V)).natDegree=1
   rwa [cyx.proof]
 · rw [ht]
   calc
     affineDegree (gN V)=affineDegree (gN U) :=hdegG
     _=affineDegree (gN A) :=hdegH
     _=affineDegree A:= by rw [affineDegree,affineDegree,cyx.proof]
end
end ata
end
end
