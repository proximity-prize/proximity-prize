import ProximityPrize.SubmissionLower.ZhNzRYc
set_option Elab.async false
open _root_ renaming Algebra → zZE, Algebra.EssFiniteType → zl5, Algebra.EssFiniteType.comp → zQi, Algebra.FiniteType → zUK, Algebra.IsIntegral → zVK, Algebra.adjoin_le → zjL, Algebra.subset_adjoin → zkk, Algebra.trdeg → zls, Function.Injective → zq4, Function.Surjective → zpX, IsScalarTower → zsf, IsScalarTower.of_algebraMap_eq → zsL, Polynomial.trdeg_of_isDomain → zBA, Set.mem_insert_iff → zP8, Set.mem_singleton_iff → zpV, Subalgebra → zTg
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
section
set_option maxSynthPendingDepth 12
namespace qIGP9Qa
noncomputable section
open Polynomial
open private ezT from ProximityPrize.SubmissionLower.T
open cu (L)
open E7 (CurvePlace CurveField)
open qNu3xvc qoCymac
variable {E :Type} [Field E] [zZE L E]
private theorem normalEssential (A:Equation E) (w:CurvePlace L E)
   (hE :CurveField L E) (r :Bool) [Module.Finite (Chart A w r) (Normal A w r)] :
   zl5 L (Normal A w r) := by
 classical
 let W:=w.value.valuationSubring
 let R:=Chart A w r
 let N :=Normal A w r
 let:zZE W R:=(seedRingHom A w r).toAlgebra
 let:SMul W R:=Algebra.toSMul
 have :zsf L W R:=zsL fun _=>rfl
 let x :=xAt A w r
 let y :R:=⟨jU A r,zkk (Or.inr (by simp))⟩
 let j:R:=⟨jet A r,zkk (Or.inr (by simp))⟩
 let B:=Algebra.adjoin W ({x,y,j} : Set R)
 have hB:R≤(B.restrictScalars L).map R.val :=zjL fun u hu=> by
   rcases hu with ⟨a,rfl⟩ | hu
   · exact ⟨aee A w r a,B.algebraMap_mem a,rfl⟩
   · simp only [zP8,zpV] at hu
     rcases hu with rfl | rfl | rfl
     · exact ⟨x,zkk (by simp),rfl⟩
     · exact ⟨y,zkk (by simp),rfl⟩
     · exact ⟨j,zkk (by simp),rfl⟩
 have htop:B = ⊤ := top_unique fun a _=> by
   obtain ⟨b,hb,e⟩:=hB a.property
   exact (Subtype.ext e :b=a) ▸ hb
 have :zUK W R:=⟨⟨{x,y,j},by simpa [B] using htop⟩⟩
 have :zl5 L W:=seedEssential hE w
 have :zl5 L R:=zQi L W R
 exact zQi L R N
private theorem chartTrdeg (A:Equation E) (w:CurvePlace L E) (r :Bool) :
    2≤zls L (Chart A w r) := by
  let W:=w.value.valuationSubring
  let R:=Chart A w r
  obtain ⟨t,ht,hw⟩:=LX w
  let t' : W:=⟨t,hw.le⟩
  have :zsf L W E :=zsL fun _=>rfl
  have ht' : Transcendental L t' :=
    (transcendental_algebraMap_iff (R:=L) Subtype.val_injective).mp ht
  let f :W[X] →ₐ[L] R :=
    { RH A w r with
      commutes' := fun c=> by
        change (eval₂RingHom (seedRingHom A w r) (xAt A w r)) (C (algebraMap L W c)) =
          algebraMap L R c
        rw [coe_eval₂RingHom,eval₂_C]
        rfl }
  let g:=f.comp (mapAlgHom (aeval t'))
  have hgi:zq4 g :=
    (chartPolynomial_injective A w r).comp
      (Polynomial.map_injective _ (transcendental_iff_injective.mp ht'))
  have hdim:zls L (L[X][X])=2 := by
    rw [← trdeg_add_eq L L[X] (A:=L[X][X]),zBA,
      zBA,one_add_one_eq_two]
  rw [← hdim]
  exact trdeg_le_of_injective g hgi
private theorem finiteTypeClosedHeight {T:Type} [CommRing T] [IsDomain T]
  [zZE L T] [zUK L T] (hT:2≤zls L T)
  (P:Ideal T) [P.IsMaximal] :2≤P.height:= by
 obtain ⟨n,g,hgi,hg⟩:=exists_integral_inj_algHom_of_fg L T
 let B:=MvPolynomial (Fin n) L
 let:zZE B T:=g.toRingHom.toAlgebra
 have :zsf L B T:=zsL fun a=>(g.commutes a).symm
 have :FaithfulSMul B T:=(faithfulSMul_iff_algebraMap_injective B T).mpr hgi
 have :zVK B T:=⟨hg⟩
 have hn:2≤n:= by
  have ht:=trdeg_add_eq L B (A:=T)
  rw [trdeg_eq_zero (R:=B) (A:=T),add_zero,MvPolynomial.trdeg_of_isDomain] at ht
  rw [← ht] at hT
  simpa [B] using hT
 have :IsNoetherianRing T:=Algebra.FiniteType.isNoetherianRing L T
 let q:=P.under B
 have :q.IsMaximal:=Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
 have :P.LiesOver q:=⟨rfl⟩
 have hle :q.height≤P.height:= by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q P]
  exact le_self_add
 rw [ezT L n q] at hle
 exact (Nat.cast_le.mpr hn).trans hle
private theorem essentialClosedHeight {N :Type} [CommRing N] [IsDomain N]
   [zZE L N] [zl5 L N]
   (hN :2≤zls L N) (P:Ideal N) [P.IsPrime]
   (hsurj:zpX (algebraMap L (N ⧸ P))) :2≤P.height:= by
 let T:=Algebra.EssFiniteType.subalgebra L N
 let M:=Algebra.EssFiniteType.submonoid L N
 let q:=P.under T
 have :P.LiesOver q:=⟨rfl⟩
 have :q.IsPrime :=Ideal.IsPrime.under T P
 have hq:zpX (algebraMap L (T ⧸ q)) := by
   intro z
   obtain ⟨a,ha⟩:=hsurj (algebraMap (T ⧸ q) (N ⧸ P) z)
   exact ⟨a,Ideal.algebraMap_quotient_injective
     ((IsScalarTower.algebraMap_apply L (T ⧸ q) (N ⧸ P) a).symm.trans ha)⟩
 let e :=RingEquiv.ofBijective (algebraMap L (T ⧸ q)) ⟨(algebraMap L _).injective,hq⟩
 have :q.IsMaximal:=Ideal.Quotient.maximal_of_isField q (e.symm.toMulEquiv.isField (Field.toIsField L))
 have :Algebra.IsAlgebraic T N :=IsLocalization.isAlgebraic N M
 have hT:2≤zls L T:= by
   have he :=trdeg_add_eq L T (A:=N)
   rw [trdeg_eq_zero (R:=T) (A:=N),add_zero] at he
   exact he.symm ▸ hN
 rw [← IsLocalization.height_under M P]
 exact finiteTypeClosedHeight hT q
theorem normalClosedHeight (A:Equation E) (w:CurvePlace L E) (hE :CurveField L E)
  (r :Bool) [Module.Finite (Chart A w r) (Normal A w r)] (P:Ideal (Normal A w r))
  [P.IsPrime] (hsurj:zpX (algebraMap L (Normal A w r ⧸ P))) :
  2≤Ideal.height (R:=Normal A w r) P:= by
 let R:=Chart A w r
 let N :=Normal A w r
 have :zl5 L N :=normalEssential A w hE r
 let f :R →ₐ[L] N :=IsScalarTower.toAlgHom L R N
 have hfi:zq4 f := by
  intro a b h
  exact Subtype.ext (congrArg (fun z :N=>(z :EC A)) h)
 exact essentialClosedHeight ((chartTrdeg A w r).trans (trdeg_le_of_injective f hfi))
  P hsurj
end
end qIGP9Qa
end
section
set_option maxSynthPendingDepth 12
namespace qIGP9Qa
open cu (L)
open E7 (CurvePlace CurveField)
open qNu3xvc qoCymac
variable {E :Type} [Field E] [zZE L E]
theorem quotientConstants (A:Equation E) (w:CurvePlace L E)
    (hE :CurveField L E) (r :Bool) (P:Ideal (Normal A w r)) [P.IsPrime]
    (v :GraphVal A r)
    (hcenter : ∀ a :Chart A w r,
      v.val (a :EC A)<1↔algebraMap (Chart A w r) (Normal A w r) a∈P)
    (hscale :SeedScale v w) (hx :ResidueConstant v (amm A))
    (hy :ResidueConstant v (jU A r)) (hj:ResidueConstant v (jet A r)) :
    zpX (algebraMap L (Normal A w r ⧸ P)) := by
  classical
  let R:=Chart A w r
  let N :=Normal A w r
  let q:Ideal R:=P.under R
  have :P.LiesOver q:=⟨rfl⟩
  let f :=Ideal.Quotient.mkₐ L q
  let S:zTg L R:=(⊥ : zTg L (R ⧸ q)).comap f
  have hs (a :w.value.valuationSubring) :ResidueConstant v (seed A a) := by
    obtain ⟨c,hc⟩:=seedResidue hE w a
    obtain ⟨n,hn,hpow⟩:=hscale
    refine ⟨c,?_⟩
    rw [constant,← map_sub,hpow]
    exact pow_lt_one₀ zero_le hc (Nat.ne_of_gt hn)
  have hle :R≤S.map R.val :=zjL fun a ha=> by
    have ha' : ResidueConstant v a := by
      rcases ha with ⟨b,rfl⟩ | ha
      · exact hs b
      · simp only [zP8,zpV] at ha
        rcases ha with rfl | rfl | rfl
        · exact hx
        · exact hy
        · exact hj
    obtain ⟨c,hc⟩:=ha'
    let z :R:=⟨a,zkk ha⟩
    refine ⟨z,?_,rfl⟩
    change f z∈(⊥ : zTg L (R ⧸ q))
    refine Algebra.mem_bot.mpr ⟨c,?_⟩
    rw [← f.commutes]
    exact (Ideal.Quotient.eq.mpr ((hcenter (z-algebraMap L R c)).mp hc)).symm
  have hsurj:zpX (algebraMap L (R ⧸ q)) := by
    intro u
    obtain ⟨a,rfl⟩:=Ideal.Quotient.mkₐ_surjective L q u
    obtain ⟨b,hb,he⟩:=hle a.property
    have hab:b=a :=Subtype.ext he
    subst b
    exact Algebra.mem_bot.mp hb
  have :zVK L (R ⧸ q) :=
    ⟨fun y=> by obtain ⟨a,rfl⟩:=hsurj y; exact isIntegral_algebraMap⟩
  have :zVK L (N ⧸ P) :=Algebra.IsIntegral.trans (R ⧸ q)
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral.surjective
end qIGP9Qa
end
