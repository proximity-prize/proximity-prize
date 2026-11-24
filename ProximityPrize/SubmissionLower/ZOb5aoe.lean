import Mathlib.NumberTheory.RamificationInertia.Galois
import ProximityPrize.SubmissionLower.ZEe4bHc
import ProximityPrize.SubmissionLower.ZwAMdHa
import ProximityPrize.SubmissionLower.ZPKTqyb
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsScalarTower → zsf, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Module.Flat → zpQ, Module.IsTorsionFree → zYo, MvPolynomial.X → z9v, Nat.card → z6S, Nat.card_congr → zKJ, Nat.mul_le_mul_left → zBI
section
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
namespace q9r9FBa
noncomputable section
open IsDedekindDomain
open scoped Pointwise
section Decomposition
variable (A K Ω C:Type) [za6 A] [za6 C] [IsDedekindDomain A]
 [Field K] [Field Ω] [zZE A K] [z0o A K] [zZE K Ω]
 [zZE A Ω] [zZE A C] [zZE C Ω] [zsf A K Ω]
 [zsf A C Ω] [IsIntegralClosure C A Ω] [zAa K Ω]
private abbrev decomposition (Q:Ideal C) :Subgroup (Ω ≃ₐ[K] Ω) :=
 letI:=IsIntegralClosure.MulSemiringAction A K Ω C
 MulAction.stabilizer (Ω ≃ₐ[K] Ω) Q
private theorem mem_decomposition {Q:Ideal C} {σ:Ω ≃ₐ[K] Ω} :
   σ∈decomposition A K Ω C Q↔Q.comap (galRestrict A K Ω C σ)= Q:= by
 letI:=IsIntegralClosure.MulSemiringAction A K Ω C
 let f :=(galRestrict A K Ω C σ).toRingEquiv
 change Q.map (f :C →+* C)= Q↔Q.comap (f :C →+* C)= Q
 constructor
 · intro h
   exact (congrArg (Ideal.comap (f :C →+* C)) h.symm).trans
     (Ideal.comap_map_of_bijective _ f.bijective)
 · intro h
   exact (congrArg (Ideal.map (f :C →+* C)) h.symm).trans
     (Ideal.map_comap_of_surjective _ f.surjective Q)
private theorem decomposition_card [IsDomain C] [z0o C Ω] [IsGalois K Ω]
  (p:Ideal A) (Q:Ideal C) [p.IsPrime] [Q.IsPrime] [Q.LiesOver p]
  [zAa A C] [zpQ A C] :
  z6S (decomposition A K Ω C Q)= Q.ramificationIdx A*Q.inertiaDeg A:= by
 letI:=IsIntegralClosure.MulSemiringAction A K Ω C
 letI:IsGaloisGroup (Ω ≃ₐ[K] Ω) A C:=IsGaloisGroup.of_isFractionRing _ _ _ K Ω
 have h:=zKJ (MulAction.orbitProdStabilizerEquivGroup (Ω ≃ₐ[K] Ω) Q)
 rw [Nat.card_prod,Algebra.IsInvariant.orbit_eq_primesOver A C (Ω ≃ₐ[K] Ω) p Q,
  Nat.card_coe_set_eq] at h
 have h' := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p C (Ω ≃ₐ[K] Ω)
 rw [Ideal.ramificationIdxIn_eq_ramificationIdx p Q (Ω ≃ₐ[K] Ω),
  Ideal.inertiaDegIn_eq_inertiaDeg p Q (Ω ≃ₐ[K] Ω)] at h'
 have hne : (p.primesOver C).Nonempty :=⟨Q,inferInstance,inferInstance⟩
 exact Nat.eq_of_mul_eq_mul_left
  (hne.ncard_pos (Algebra.QuasiFinite.finite_primesOver p)) (h.trans h'.symm)
private theorem adic_transport [IsDedekindDomain C] [z0o C Ω]
   (Q R:HeightOneSpectrum C) (σ:Ω ≃ₐ[K] Ω)
   (h:Q.asIdeal.comap (galRestrict A K Ω C σ)=R.asIdeal) :
   R.valuation Ω=(Q.valuation Ω).comap σ.toRingHom:= by
 apply eqAdicOfCenter R ((Q.valuation Ω).comap σ.toRingHom)
   ((Q.valuation_surjective Ω).comp σ.surjective)
 · intro b
   change Q.valuation Ω (σ (algebraMap C Ω b))≤1
   rw [← algebraMap_galRestrict_apply A σ b]
   exact Q.valuation_le_one _
 · intro b
   change b∈R.asIdeal↔Q.valuation Ω (σ (algebraMap C Ω b))<1
   rw [← algebraMap_galRestrict_apply A σ b,Q.valuation_lt_one_iff_mem,← h]
   rfl
end Decomposition
section Embeddings
variable {A B C K F Ω:Type} [za6 A] [za6 B] [za6 C]
 [IsDedekindDomain A] [IsDedekindDomain B] [IsDedekindDomain C]
 [Field K] [Field F] [Field Ω] [zZE K F] [zZE K Ω] [zZE F Ω] [zsf K F Ω]
 [zZE A K] [z0o A K] [zZE A F] [zZE A Ω]
 [zsf A K F] [zsf A K Ω] [zsf A F Ω]
 [zZE A B] [zZE A C] [zZE B C] [zsf A B C]
 [zZE B F] [z0o B F] [zsf A B F]
 [zZE B Ω] [zsf B F Ω] [zZE C Ω] [z0o C Ω]
 [zsf A C Ω] [zsf B C Ω]
 [IsIntegralClosure C A Ω] [IsIntegralClosure C B Ω]
 [zAa K Ω] [zAa F Ω] [IsGalois K Ω] [IsGalois F Ω]
 [zAa A C] [zpQ A C] [zAa B C] [zpQ B C]
 [zAa A B] [zpQ A B] [FaithfulSMul A C] [FaithfulSMul B C]
theorem placeEmbeddings (p:HeightOneSpectrum A) (P:HeightOneSpectrum B)
    (Q R:HeightOneSpectrum C) [P.asIdeal.LiesOver p.asIdeal] [Q.asIdeal.LiesOver p.asIdeal]
    [R.asIdeal.LiesOver P.asIdeal] [R.asIdeal.LiesOver p.asIdeal] :
    ∃ j:Fin (P.asIdeal.ramificationIdx A) ↪ (F →ₐ[K] Ω),∀ b x,
      Q.valuation Ω (j b x)=P.valuation F x^(P.asIdeal.ramificationIdx' R.asIdeal) := by
  classical
  let q:=R.asIdeal
  let D:=decomposition A K Ω C q
  let H :=decomposition B F Ω C q
  let inc:=IsScalarTower.toAlgHom K F Ω
  letI:MulAction D (F →ₐ[K] Ω) :=
    { smul := fun σ f=>(σ.val :Ω →ₐ[K] Ω).comp f
      one_smul := fun _=>rfl
      mul_smul := fun _ _ _=>rfl }
  let O:=MulAction.orbit D inc
  let T:=MulAction.stabilizer D inc
  have equivT:H ≃ T:= by
    let φ (σ:Ω ≃ₐ[F] Ω) :=σ.restrictScalars K
    have hcompat (σ:Ω ≃ₐ[F] Ω) :
        q.comap (galRestrict A K Ω C (φ σ))=q.comap (galRestrict B F Ω C σ) := by
      ext b
      change galRestrict A K Ω C (φ σ) b∈q↔galRestrict B F Ω C σ b∈q
      have heq :galRestrict A K Ω C (φ σ) b=galRestrict B F Ω C σ b :=
        (zxb C Ω) (by simp [φ,algebraMap_galRestrict_apply])
      rw [heq]
    let f :H→T:= fun σ =>
      ⟨⟨φ σ.val,(mem_decomposition A K Ω C).mpr (by
        rw [hcompat]
        exact (mem_decomposition B F Ω C).mp σ.property)⟩,
        AlgHom.ext fun x=>σ.val.commutes x⟩
    refine Equiv.ofBijective f ⟨?_,?_⟩
    · intro a b h
      exact Subtype.ext (AlgEquiv.restrictScalars_injective K
        (congrArg (fun t:T=>t.val.val) h))
    · intro t
      have ht:t.val.val.toAlgHom.comp inc=inc:=t.property
      let σ:Ω ≃ₐ[F] Ω:=AlgEquiv.ofRingEquiv (f :=t.val.val.toRingEquiv)
        (fun x=>congrArg (fun g:F →ₐ[K] Ω=>g x) ht)
      have hσ:φ σ=t.val.val :=rfl
      have hmem:=(mem_decomposition A K Ω C).mp t.val.property
      rw [← hσ,hcompat] at hmem
      exact ⟨⟨σ,(mem_decomposition B F Ω C).mpr hmem⟩,Subtype.ext (Subtype.ext hσ)⟩
  have hcard:=zKJ (MulAction.orbitProdStabilizerEquivGroup D inc)
  change z6S (O×T)=z6S D at hcard
  rw [Nat.card_prod,← zKJ equivT,
    decomposition_card B F Ω C P.asIdeal q,decomposition_card A K Ω C p.asIdeal q,
    Ideal.ramificationIdx_tower (R:=A) P.asIdeal q,Ideal.inertiaDeg_tower (R:=A) P.asIdeal q] at hcard
  have hpos :0<q.ramificationIdx B*q.inertiaDeg B :=
    Nat.mul_pos (q.ramificationIdx_pos B) (q.inertiaDeg_pos B)
  have hO:z6S O=P.asIdeal.ramificationIdx A*P.asIdeal.inertiaDeg A :=
    Nat.eq_of_mul_eq_mul_right hpos (by
      simpa only [mul_assoc,mul_left_comm,mul_comm] using hcard)
  have hle :P.asIdeal.ramificationIdx A≤z6S O:= by
    rw [hO]
    exact Nat.le_mul_of_pos_right _ (P.asIdeal.inertiaDeg_pos A)
  obtain ⟨σ,hσ⟩:=Ideal.exists_comap_galRestrict_eq A K Ω C
    (p:=p.asIdeal) (P₁:= Q.asIdeal) (P₂:=q)
    ⟨Q.isPrime,inferInstance⟩ ⟨R.isPrime,inferInstance⟩
  have hQ:=adic_transport A K Ω C Q R σ hσ
  letI:Finite O:=Finite.of_surjective
    (fun τ:D =>(⟨τ•inc,⟨τ,rfl⟩⟩:O))
    (fun ⟨_,⟨τ,hτ⟩⟩=>⟨τ,Subtype.ext hτ⟩)
  letI:=Fintype.ofFinite O
  let l:Fin (P.asIdeal.ramificationIdx A) ↪ O :=
    (Fin.castLEEmb (by simpa only [Nat.card_eq_fintype_card] using hle)).trans
      (Fintype.equivFin O).symm.toEmbedding
  let j:Fin (P.asIdeal.ramificationIdx A) ↪ (F →ₐ[K] Ω) :=
    ⟨fun b=>(σ:Ω →ₐ[K] Ω).comp (l b).val,by
      intro a b hab
      apply l.injective
      exact Subtype.ext (AlgHom.ext fun x =>
        σ.injective (congrArg (fun g:F →ₐ[K] Ω=>g x) hab))⟩
  refine ⟨j,fun b x => ?_⟩
  obtain ⟨τ,hτ⟩:=(l b).property
  have hR:=adic_transport A K Ω C R R τ.val
    ((mem_decomposition A K Ω C).mp τ.property)
  calc
    Q.valuation Ω (j b x)=R.valuation Ω ((l b).val x) :=
      (congrArg (fun v :Valuation Ω _=>v ((l b).val x)) hQ).symm
    _=R.valuation Ω (τ.val (algebraMap F Ω x)) := by rw [← hτ]; rfl
    _=R.valuation Ω (algebraMap F Ω x) :=
      (congrArg (fun v :Valuation Ω _=>v (algebraMap F Ω x)) hR).symm
    _ = _:=(P.valuation_liesOver Ω R x).symm
end Embeddings
end
end q9r9FBa
end
section
set_option linter.style.haveILetI false
namespace q9r9FBa
noncomputable section
open IsDedekindDomain
theorem embeddingMultiplicity :qv2t4Be.c2 := by
  intro K F Ω _ _ _ _ _ _ _ _ _ u v U hu hv hU e n he hn hUbase hvbase
  let A:=u.valuationSubring
  let B:=integralClosure A F
  let C:=integralClosure A Ω
  letI:IsDiscreteValuationRing A:=valuationDVR u hu
  letI:zAa K F:=Module.Finite.left K F Ω
  letI:zAa F Ω:=Module.Finite.right K F Ω
  letI:Algebra.IsSeparable K F:=Algebra.isSeparable_tower_bot_of_isSeparable K F Ω
  letI:IsGalois F Ω:=IsGalois.tower_top_of_isGalois K F Ω
  letI:IsDedekindDomain B:=integralClosure.isDedekindDomain A K F
  letI:IsDedekindDomain C:=integralClosure.isDedekindDomain A K Ω
  letI:z0o B F:=IsIntegralClosure.isFractionRing_of_finite_extension A K F B
  letI:z0o C Ω:=IsIntegralClosure.isFractionRing_of_finite_extension A K Ω C
  letI:zsf B C Ω:=zsL (fun _=>rfl)
  letI:zsf A B C:=zsL (fun a =>
    Subtype.ext (IsScalarTower.algebraMap_apply A F Ω (a :A)))
  letI:IsIntegralClosure C B Ω:=IsIntegralClosure.tower_top (R:=A)
  letI:zAa A B:=IsIntegralClosure.finite A K F B
  letI:zAa A C:=IsIntegralClosure.finite A K Ω C
  letI:zAa B C:=IsIntegralClosure.finite B F Ω C
  letI:zYo A B:=IsIntegralClosure.isTorsionFree A F
  letI:zYo A C:=IsIntegralClosure.isTorsionFree A Ω
  letI:zYo B C:=IsIntegralClosure.isTorsionFree B Ω
  letI:FaithfulSMul A C:=(faithfulSMul_iff_algebraMap_injective A C).mpr
    (ValuationSubring.integralClosure_algebraMap_injective u Ω)
  letI:FaithfulSMul B C:=(faithfulSMul_iff_algebraMap_injective B C).mpr
    (fun _ _ h=>(zxb B F) ((algebraMap F Ω).injective (congrArg Subtype.val h)))
  let p:=IsDiscreteValuationRing.maximalIdeal A
  obtain ⟨P,hP,hPv⟩:=centerPlace u v hv hn hvbase
  obtain ⟨Q,hQ,hQU⟩:=centerPlace u U hU he hUbase
  letI:P.asIdeal.LiesOver p.asIdeal:=hP
  letI:Q.asIdeal.LiesOver p.asIdeal:=hQ
  letI:P.asIdeal.IsMaximal:=P.isPrime.isMaximal P.ne_bot
  letI:Algebra.IsIntegral B C:=Algebra.IsIntegral.tower_top A
  obtain ⟨I,hI,hIP⟩:=Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=C) P.asIdeal
  letI:I.IsPrime :=hI.isPrime
  letI:I.LiesOver P.asIdeal:=hIP
  let R:=primeAbove P I
  letI:R.asIdeal.LiesOver P.asIdeal:=hIP
  letI:R.asIdeal.LiesOver p.asIdeal:=Ideal.LiesOver.trans R.asIdeal P.asIdeal p.asIdeal
  obtain ⟨j₀,hj₀⟩:=placeEmbeddings (K:=K) (F:=F) (Ω:=Ω) p P Q R
  have hpn:p.asIdeal.ramificationIdx' P.asIdeal=n:= by
    apply exponent_eq u hu
    intro x
    calc
      _=p.valuation K x^p.asIdeal.ramificationIdx' P.asIdeal :=
        congrArg (fun t=>t x^p.asIdeal.ramificationIdx' P.asIdeal) (adicBase u hu).symm
      _=P.valuation F (algebraMap K F x) :=p.valuation_liesOver F P x
      _ = _:=(congrArg (fun t:Valuation F _=>t (algebraMap K F x)) hPv).trans (hvbase x)
  have hn' := (Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.asIdeal p.ne_bot).symm.trans hpn
  let j:=(⟨Fin.cast hn'.symm,Fin.cast_injective hn'.symm⟩:Fin n ↪ _).trans j₀
  let r :=P.asIdeal.ramificationIdx' R.asIdeal
  have hr :0< r :=Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver R.asIdeal P.ne_bot)
  have hj' (b:Fin n) (x :F) :U (j b x)=v x^r := by
    rw [← hQU,← hPv]
    exact hj₀ (Fin.cast hn'.symm b) x
  refine ⟨r,hr,exponent_eq u hu (fun x => ?_),j,hj'⟩
  have h:=hj' ⟨0,hn⟩ (algebraMap K F x)
  rw [(j ⟨0,hn⟩).commutes x,hUbase,hvbase,← pow_mul] at h
  exact h.symm
theorem proof :qJOpoVa.c6 :=
 qv2t4Be.of_children normalExtension embeddingMultiplicity
end
end q9r9FBa
end
section
namespace qxDtRld
noncomputable section
open Polynomial q82zwcd
open P5 (K I)
open P5_7_7 (phys)
open cu (L)
open Cu (sQ)
open qb0hmCe (SiteTarget)
open qFD8jve (Vanishes)
open scoped Classical
open private coprime_eval scale reduced_test from ProximityPrize.SubmissionLower.Z66Jm5b
variable {D:ℕ} {w:I→K} {U:Finset K} {s :K→K[X]}
 {z :K→K} {q:sQ} {J:WordChart D w U s} {F:DualSheet J q z}
private theorem mark_scale {V:Variation F} {R:SiteTarget} {γ:K}
   (hγ:γ∈V.good) (hm:targetHit J z R γ) :
   ∃ k :L,k≠0∧(J.P γ).eval R.center=k*resA R z γ ∧
     (J.Q γ).eval R.center=k*resB R z γ:= by
 refine scale hm.1 ?_ hm.2
 by_cases h: (J.Q γ).eval R.center=0
 · exact Or.inl (coprime_eval (J.coprime γ (Finset.mem_filter.mp (V.Bp hγ)).1) R.center h)
 · exact Or.inr h
theorem mark_zero {V:Variation F} {R:SiteTarget} {t:L} (A:Chart V R t)
    {γ:K} (hγ:γ∈V.good) (hm:targetHit J z R γ) :
    (markP J R z γ).coeff 0=0∧(markQ J R t γ).coeff 0≠0:= by
  constructor
  · simp only [markP,coeff_sub,coeff_C_mul,taylor_coeff_zero]
    exact sub_eq_zero.mpr (by simpa only [resA,resB,mul_comm] using hm.2)
  · obtain ⟨k,hk,hP,hQ⟩:=mark_scale hγ hm
    simp only [markQ,coeff_sub,coeff_C_mul,taylor_coeff_zero,hP,hQ]
    rw [show t*(k*resB R z γ) - k*resA R z γ =
        k*(t*resB R z γ - resA R z γ) by ring]
    exact mul_ne_zero hk (A.avoids γ hγ hm)
theorem transfer {V:Variation F} {R:SiteTarget} {t:L} (A:Chart V R t)
   {γ:K} (hγ:γ∈V.good) (hm:targetHit J z R γ)
   (hv :Vanishes (phys (C (t*resB R z γ - resA R z γ)) *
     (phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ))) +
     phys (correction F R t γ))) :
   ¬ exception V R γ:= by
 have hd:taylor R.center (V.den γ)≠0:= fun h =>
   V.den_ne γ hγ ((taylor_eq_zero _ _).mp h)
 have hc:=(V.reduced γ hγ).map (taylorAlgHom R.center).toRingHom
 have h:=reduced_test hd hc (A.avoids γ hγ hm) hv
 change (taylor R.center (V.num γ)).coeff 0=0↔_ at h
 rw [taylor_coeff_zero] at h
 obtain ⟨k,hk,hP,hQ⟩:=mark_scale hγ hm
 have hT: (correction F R t γ).coeff 0 =
     (k*k*(t*resB R z γ - resA R z γ))*(R.det*F.direction γ R.coord) := by
   simp only [correction,markQ,mul_coeff_zero,coeff_C_zero,coeff_sub,taylor_coeff_zero,
     hP,hQ,SiteTarget.det,resA,resB]
   ring
 intro he
 apply he.2
 rw [h,hT]
 simp only [mul_eq_zero,mul_ne_zero (mul_ne_zero hk hk) (A.avoids γ hγ hm),false_or]
end
end qxDtRld
end
section
namespace qxDtRld
noncomputable section
open Polynomial Finset q82zwcd
open P5 (K p)
open P5_7_7 (phys)
open cu (L)

open E7 (CurvePlace axV)
open agN (b27)
open qb0hmCe (SiteTarget cLN specialize zD)
open qFD8jve (aFA sheetPole seedPole aaD polarResultant guard_le)
open scoped Classical WithZero
local notation "siteGuard" => qFD8jve.guard
def c1 :Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} {F:DualSheet J q z}
    (V:Variation F),F.d<p → ∀ R:SiteTarget,
      (∃ γ∈V.good,targetHit J z R γ) → ∃ t:L,Chart V R t
def c2 :Prop :=
  ∀ {D w U s z q} {J:WordChart D w U s} {F:DualSheet J q z}
    {V:Variation F} {R:SiteTarget} {t:L},Chart V R t →
    ∀ γ (hγ:γ∈V.good),targetHit J z R γ →
    let a :=F.atPlace γ (Finset.mem_filter.mp (V.Bp hγ)).1
    let G:=nY (F.scale γ:F.curve.E) (Go F R t)
    let P:=markP J R z γ
    let Q:=markQ J R t γ
    specialize (cLN a 0 G) P Q=0 ∧
    specialize (cLN a 0 G).derivative P Q≠0 ∧
    zD a G P Q =
      phys (C (t*resB R z γ - resA R z γ)) *
        (phys (taylor R.center (V.num γ))/phys (taylor R.center (V.den γ))) +
      phys (correction F R t γ)
def c3:Prop :=qFD8jve.c2
theorem of_children (bY:c1) (transport:c2) (local_test :c3) :q82zwcd.c4 := by
  intro D w U s z q J F V hp R
  let T:=V.good.filter (exception V R)
  by_cases hm : ∃ γ∈V.good,targetHit J z R γ
  swap
  · have he :T = ∅ := eq_empty_iff_forall_notMem.mpr fun γ hγ=> by
      obtain ⟨hv,hr,_⟩:=mem_filter.mp hγ
      exact hm ⟨γ,hv,hr⟩
    change T.card≤_
    simp [he]
  obtain ⟨t,A⟩:=bY V hp R hm
  let G:=Go F R t
  have hF:0<F.d:= by
    have h:=natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible F.irreducible)
    rwa [natDegree_map_eq_of_injective (zxb _ _) _] at h
  have hd:0<G.natDegree :=A.degree.symm ▸ hF
  let g:=siteGuard G
  have hc:aaD G≠0:= by
    intro hz
    have h:=congrArg (fun f :F.curve.E[X]=>f.coeff G.natDegree) hz
    exact A.leading (by
      simpa only [aaD,coeff_map,coe_evalRingHom,← coeff_zero_eq_eval_zero,
        leadingCoeff,coeff_zero] using h)
  have hg:g≠0:=mul_ne_zero
    (mt trailingCoeff_eq_zero.mp A.separant) (mt trailingCoeff_eq_zero.mp hc)
  let H (v :CurvePlace L F.curve.E) :=sheetPole v.value F.f
  let S (v :CurvePlace L F.curve.E) :=seedPole F.curve R v.value
  let M (v :CurvePlace L F.curve.E) :=H v+F.d*S v
  let B (v :CurvePlace L F.curve.E) :=2*F.d*M v
  have hdiv :axV L F.curve.E :=
    aFU.of_children
      bRt.proof bRu.proof L F.curve.E F.curve.curve
  have hH :H.HasFiniteSupport:=b27 hdiv _
  have hS:S.HasFiniteSupport∧(∑ᶠ v,S v)≤R.height q:= by
    by_cases h:R.b=0∧R.d=0
    · simp [S,seedPole,SiteTarget.height,Function.HasFiniteSupport,h]
    · exact ⟨by simpa [S,seedPole,h] using (hdiv (F.curve.seed R.coord)).1,
        by simpa [S,seedPole,SiteTarget.height,h] using F.curve.co6 R.coord⟩
  have hM:M.HasFiniteSupport:=hH.add (hS.1.mul_right F.d)
  have hB:B.HasFiniteSupport:=hM.mul_right (2*F.d:ℕ)
  have hb (v :CurvePlace L F.curve.E) :WithZero.log (v.value g)≤(B v :ℤ) := by
    apply (WithZero.log_le_iff_le_exp (v.value.ne_zero_iff.mpr hg)).mpr
    have h:=guard_le hd (A.bound v)
    rw [A.degree] at h
    exact h
  have ht (γ:K) (hγ:γ∈T) :WithZero.log ((F.place γ).value g)<(B (F.place γ) :ℤ) := by
    obtain ⟨hv,hr,he⟩:=mem_filter.mp hγ
    have hU:=(mem_filter.mp (V.Bp hv)).1
    let v :=(F.place γ).value
    let u:F.curve.E :=F.scale γ
    let G' := nY u G
    have hu:u≠0:=Units.ne_zero _
    have hdeg:G'.natDegree=G.natDegree :=natDegree_C_mul (C_ne_zero.mpr hu)
    have hd' : 0<G'.natDegree :=hdeg.symm ▸ hd
    have hlead:G'.leadingCoeff.coeff 0≠0:= by
      rw [leadingCoeff,hdeg,show G' = C (C u)*G from rfl,coeff_C_mul,coeff_C_mul]
      exact mul_ne_zero hu A.leading
    have hsep:polarResultant G' ≠ 0:= by
      intro hz
      have h:=guard_scaled hu hd
      change siteGuard G' = _ at h
      rw [qFD8jve.guard,hz,trailingCoeff_zero,zero_mul] at h
      exact mul_ne_zero (pow_ne_zero _ hu) hg h.symm
    have hs :v (siteGuard G')≤1 := by
      simpa only [Nat.mul_zero,Nat.cast_zero,WithZero.exp_zero] using guard_le hd' (A.integral γ hv hr)
    have hsmall:v (siteGuard G')<1 := by
      apply lt_of_le_of_ne hs
      intro heq
      obtain ⟨hP,hQ⟩:=mark_zero A hv hr
      obtain ⟨hroot,hsimple,hvar⟩:=transport A γ hv hr
      let a :=F.atPlace γ hU
      let va :=(Valued.v :Valuation (LaurentSeries L) ℤᵐ⁰).comap a.toRingHom
      have hv_eq (c:F.curve.E) :va c=v c:=(F.value γ hU c).symm
      have hi:aFA va G' 0:= fun i j=>(hv_eq _).trans_le (A.integral γ hv hr i j)
      have hlt:G'.natDegree<p:= by rw [hdeg,A.degree]; exact hp
      have van:=local_test F.curve.E a G' hd' hlt hlead hsep hi
        ((hv_eq (siteGuard G')).trans heq) _ _ hP hQ hroot hsimple
      rw [hvar] at van
      exact transfer A hv hr van ⟨hr,he⟩
    have hscale : -(M (F.place γ) :ℤ)≤WithZero.log (v u) :=
      (neg_le_neg (Int.ofNat_le.mpr (Nat.le_add_right _ _))).trans (scale_log F hU)
    rw [show G' = nY u G from rfl,guard_scaled hu hd,A.degree] at hsmall
    exact log_unscale v hu hg hscale hsmall
  have hinj:Set.InjOn F.place (T:Set K) :=
    F.distinct.mono fun _ hγ=>(mem_filter.mp (V.Bp (mem_filter.mp hγ).1)).1
  refine (divisor_count hdiv T F.place hinj (g:=g) B hB hb ht).trans ?_
  change (∑ᶠ v,2*F.d*M v)≤_
  rw [← mul_finsum' M (2*F.d) hM]
  apply zBI
  change (∑ᶠ v,(H v+F.d*S v))≤_
  have hmul : (fun v=>F.d*S v).HasFiniteSupport:=hS.1.mul_right F.d
  rw [finsum_add_distrib hH hmul,← mul_finsum' S F.d hS.1]
  exact Nat.add_le_add le_rfl (zBI F.d hS.2)
end
end qxDtRld
end
section
set_option backward.isDefEq.respectTransparency false
namespace qEAs6me
noncomputable section
open cu (L)
open qfbIfsd (Slot)
open q2tSkEc (bzm caps orders)
open scoped BigOperators Classical
abbrev Coeff (s b d:ℕ) :=MvPolynomial (bzm s b d) L
def topSlot (s b d:ℕ) (t:Fin 3) (j:Fin (caps b s t+1)) :
    Slot s (caps b s t) (orders d t) :=
  ⟨⟨orders d t,Nat.lt_succ_self _⟩,⟨j,by simpa using j.isLt⟩⟩
def topPoly {M:Type} [CommSemiring M] {s b d:ℕ}
    (a :bzm s b d→M) (t:Fin 3) :Polynomial M :=
  ∑ j:Fin (caps b s t+1),Polynomial.monomial j (a ⟨t,topSlot s b d t j⟩)
def topRes {s b d:ℕ} : Coeff s b d :=
 (topPoly z9v 0).resultant (topPoly z9v 1) b (b+s+1)
def tied {M:Type} [CommSemiring M] {s b d:ℕ}
    (a :bzm s b d→M) (r :bzm s b d) :M :=
  if h:r.1=2∧r.2.1.val=orders d r.1 then
    (d:M)*a ⟨0,topSlot s b d 0 ⟨r.2.2.val,by
      refine r.2.2.isLt.trans_eq ?_
      rw [h.2,Nat.sub_self,zero_mul,add_zero,h.1]
      rfl⟩⟩
  else a r
def tie {s b d:ℕ} : Coeff s b d →+* Coeff s b d :=
 MvPolynomial.eval₂Hom MvPolynomial.C (tied z9v)
end
end qEAs6me
end
