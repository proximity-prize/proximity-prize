import ProximityPrize.SubmissionLower.A3
import ProximityPrize.SubmissionLower.Za4gQ2b
import ProximityPrize.SubmissionLower.Zc6ZBRc
set_option Elab.async false
open _root_ renaming Algebra → zZE, CommRing → za6, DFunLike.congr_fun → zmU, Fin.rev → z8T, Function.Injective → zq4, Function.Surjective → zpX, Ideal → znc, Ideal.Quotient.commRing → z0w, Ideal.Quotient.liftₐ → zTA, Ideal.Quotient.mk → zVv, Ideal.Quotient.mk_surjective → zld, Ideal.Quotient.mkₐ → zvR, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.span → zye, Ideal.span_singleton_le_iff_mem → zvl, IsDomain → ztn, IsFractionRing → z0o, IsFractionRing.injective → zxb, IsLocalization → zNo, IsScalarTower → zsf, IsScalarTower.of_algebraMap_eq → zsL, Module.Finite → zAa, Module.finite_of_finrank_pos → zlS, Module.finrank → zsE, Module.nontrivial_of_finrank_pos → zcE, MvPolynomial → z3y, MvPolynomial.C → znf, MvPolynomial.X → z9v, MvPolynomial.algebraMap_eq → zKm, MvPolynomial.eval → zY9, MvPolynomial.eval₂Hom → zOD, MvPolynomial.eval₂Hom_C → zTv, MvPolynomial.map → zDK, MvPolynomial.map_C → zpw, MvPolynomial.map_X → z7N, MvPolynomial.map_injective → zNV, MvPolynomial.ringHom_ext → zXT, Nat.eq_zero_of_le_zero → za7, Nat.mul_le_mul_left → zBI, Nat.mul_le_mul_right → ztf, Nat.pos_of_ne_zero → zOl, Polynomial → zM1, Polynomial.C → z1z, Polynomial.IsRoot → zT9, Polynomial.X → z7y
open _root_ renaming Polynomial.algebraMap_eq → zrD, Polynomial.coe_eval₂RingHom → z4Q, Polynomial.coe_mapRingHom → zKC, Polynomial.commRing → zqU, Polynomial.eq_C_of_natDegree_eq_zero → zr7, Polynomial.eval₂RingHom → zqf, Polynomial.eval₂_C → zJU, Polynomial.mapRingHom → zhd, Polynomial.map_C → zrL, Polynomial.natDegree_map_eq_of_injective → zt8, Polynomial.ringHom_ext → z86, RingHom.comp_apply → zQb, RingHom.congr_fun → zLs, RingHom.ker → zdq
set_option maxHeartbeats 1200000
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qjbBN1b
noncomputable section
open cu (FX aZ)
open gT (gk aQ B4 Pp ek)
open GK (Raw Over coord qw)
open scoped Polynomial nonZeroDivisors
attribute [local instance] MvPolynomial.algebraMvPolynomial Polynomial.algebra
local instance (n:ℕ) (I:znc (Raw n)) :za6 (gk I)[X] :=
  @zqU (gk I) (z0w I)
abbrev cut {n:ℕ} (i:Fin n) (j:Option (Fin n)) :Over n :=
  j.elim (Pp i) (B4 i)
abbrev ke {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :=
  I.map (zDK (algebraMap FX aQ)) ⊔ zye {cut i j}
abbrev Section {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :=
  gk (ke I i j)
def params {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :
    aZ →+* (gk I)[X] :=
  j.elim (zOD (Polynomial.C.comp (algebraMap FX (gk I)))
    ![z7y,z1z (coord I i)]) (qw I i)
def fromRaw {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :
    gk I →+* Section I i j :=
  Ideal.quotientMap (ke I i j) (zDK (algebraMap FX aQ))
    (Ideal.map_le_iff_le_comap.mp le_sup_left)
def fromPoly {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :
    (gk I)[X] →+* Section I i j :=
  zqf (fromRaw I i j)
    (algebraMap aQ (Section I i j) (ek 0))
private theorem params_commute {n:ℕ} (I:znc (Raw n)) (i:Fin n)
    (j:Option (Fin n)) :
    (fromPoly I i j).comp (params I i j) =
      (algebraMap aQ (Section I i j)).comp (algebraMap aZ aQ) := by
  cases j with
  | some k=>exact GK.aEa I i k
  | none =>
    have h:zVv (ke I i none) (Pp i)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (zs0 (z5J _))
    apply zXT
    · intro a
      simp [params,fromPoly,fromRaw,zQb,zKm]
      rfl
    · intro k
      fin_cases k
      · simp [params,fromPoly,zQb,ek]
      · have hi:zVv (ke I i none) (z9v i) =
            algebraMap aQ (Section I i none) (ek 1) :=
          by
            rw [← Ideal.Quotient.mk_algebraMap,zKm]
            exact sub_eq_zero.mp (by simpa only [Pp,map_sub] using h)
        simpa [params,fromPoly,fromRaw,zQb,coord,
          zKm,ek] using hi
theorem params_injective {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n))
    [Nontrivial (Section I i j)] :zq4 (params I i j) := by
  apply Function.Injective.of_comp (f :=fromPoly I i j)
  change zq4 ((fromPoly I i j).comp (params I i j))
  rw [params_commute]
  exact (algebraMap aQ _).injective.comp (zxb aZ aQ)
private abbrev Integral (n:ℕ) :=z3y (Fin n) aZ
private abbrev beforeCut {n:ℕ} (i:Fin n) (j:Option (Fin n)) :Integral n :=
  j.elim (z9v i)
    (fun k=>z9v i+MvPolynomial.C (z9v 0)*z9v k) -
      znf (z9v 1)
private def FT {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :
    Integral n →+* (gk I)[X] :=
  zOD (params I i j) (fun k=>z1z (coord I k))
private theorem eliminate_base {n:ℕ} (I:znc (Raw n)) (i:Fin n)
    (j:Option (Fin n)) :
    (FT I i j).comp (zDK znf) =
      Polynomial.C.comp (zVv I) := by
  apply zXT
  · intro a
    cases j <;> simp [FT,params,qw] <;> rfl
  · intro k
    simp [FT,coord]
private theorem eliminate_surjective {n:ℕ} (I:znc (Raw n)) (i:Fin n)
    (j:Option (Fin n)) :zpX (FT I i j) := by
  let u: (Raw n)[X] →+* Integral n:=zqf
    (zDK znf)
    (znf (z9v 0))
  have he : (FT I i j).comp u=zhd (zVv I) := by
    apply z86
    · intro a
      simp only [zQb,u,z4Q,zJU,
        zKC,zrL]
      exact zLs (eliminate_base I i j) a
    · cases j <;> simp [u,FT,params,qw]
  apply Function.Surjective.of_comp (g:=u)
  change zpX ((FT I i j).comp u)
  rw [he]
  exact Polynomial.map_surjective _ zld
private theorem b19 {n:ℕ} (I:znc (Raw n)) (i:Fin n)
    (j:Option (Fin n)) :
    (zVv (ke I i j)).comp (algebraMap (Integral n) (Over n)) =
      (fromPoly I i j).comp (FT I i j) := by
  apply zXT
  · intro a
    change zVv (ke I i j)
        (zDK (algebraMap aZ aQ) (znf a)) =
      fromPoly I i j (FT I i j (znf a))
    rw [zpw,FT,zTv]
    exact (zLs (params_commute I i j) a).symm
  · intro k
    change zVv (ke I i j)
        (zDK (algebraMap aZ aQ) (z9v k)) =
      fromPoly I i j (FT I i j (z9v k))
    simp [FT,fromPoly,fromRaw,coord]
abbrev Ek {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :=
  aZ⁰.map (params I i j)
abbrev aXs {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :
    zZE (gk I)[X] (Section I i j) :=
  @RingHom.toAlgebra' (gk I)[X] (Section I i j) _ _ (fromPoly I i j)
    (fun a b=>(Ideal.Quotient.commSemiring (ke I i j)).mul_comm (fromPoly I i j a) b)
theorem localization {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n)) :
    letI:zZE (gk I)[X] (Section I i j) :=aXs I i j
    zNo (Ek I i j) (Section I i j) := by
  let:zZE (gk I)[X] (Section I i j) :=aXs I i j
  let M:=aZ⁰.map (znf (σ:=Fin n))
  let l:=algebraMap (Integral n) (Over n)
  have hden:M.map (FT I i j)=Ek I i j:= by
    change (aZ⁰.map (znf (σ:=Fin n)).toMonoidHom).map
      (FT I i j).toMonoidHom=aZ⁰.map (params I i j).toMonoidHom
    rw [Submonoid.map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    exact zTv _ _ _
  rw [← hden]
  refine @IsLocalization.of_surjective (Integral n) _ M (Over n) _ _ _
    ((gk I)[X]) (Section I i j) _ _ (aXs I i j)
    (FT I i j) (eliminate_surjective I i j) (zVv (ke I i j))
    zld (b19 I i j) ?_
  rw [Ideal.mk_ker,ke]
  have hb:l.comp (zDK (znf:FX →+* aZ)) =
      zDK (algebraMap FX aQ) := by
    apply RingHom.ext
    intro p
    change zDK (algebraMap aZ aQ) (zDK znf p)= _
    rw [MvPolynomial.map_map]
    rfl
  have hc:l (beforeCut i j)=cut i j:= by
    change zDK (algebraMap aZ aQ) (beforeCut i j)= _
    cases j <;> simp only [beforeCut,cut,Pp,B4,ek,Option.elim,
      map_sub,map_add,map_mul,zpw,z7N]
  apply sup_le
  · rw [← hb,← Ideal.map_map]
    apply Ideal.map_mono
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change ((FT I i j).comp (zDK znf)) a=0
    rw [eliminate_base]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  · rw [← hc,zvl]
    apply z7X
    change FT I i j (beforeCut i j)=0
    cases j <;> simp [FT,beforeCut,params,qw]
theorem section_domain {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n))
    [I.IsPrime] (h:zq4 (params I i j)) :ztn (Section I i j) := by
  let:zZE (gk I)[X] (Section I i j) :=aXs I i j
  let:zNo (Ek I i j) (Section I i j) :=localization I i j
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (Section I i j)
    (map_le_nonZeroDivisors_of_injective (params I i j) h le_rfl)
private theorem frac_of_loc {R K:Type} [za6 R] [Field K] [zZE R K]
    (M:Submonoid R) [hLoc:zNo M K] (hM:M≤R⁰) :z0o R K:= by
  let:FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr (IsLocalization.injective K hM)
  apply IsFractionRing.of_field
  intro x
  obtain ⟨⟨a,b⟩,hab⟩:=IsLocalization.surj M x
  have hb:algebraMap R K b≠0:=(IsLocalization.map_units K b).ne_zero
  exact ⟨a,b,(eq_div_iff_mul_eq hb).mpr hab⟩
theorem section_frac {n:ℕ} (I:znc (Raw n)) (i:Fin n) (j:Option (Fin n))
    [I.IsPrime] [zAa aQ (Section I i j)]
    (h:zq4 (params I i j)) :
    letI:zZE (gk I)[X] (Section I i j) :=aXs I i j
    z0o (gk I)[X] (Section I i j) := by
  let:zZE (gk I)[X] (Section I i j) :=aXs I i j
  let:ztn (Section I i j) :=section_domain I i j h
  let:Field (Section I i j) :=fieldOfFiniteDimensional aQ (Section I i j)
  exact frac_of_loc (K:=Section I i j) (Ek I i j) (hLoc:=localization I i j)
    (map_le_nonZeroDivisors_of_injective (params I i j) h le_rfl)
end
end qjbBN1b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qjbBN1b
noncomputable section
open cu (FX aZ)
open gT (aQ ek Pp)
open GK (Over)
open private AV dc2 co3 bNH from ProximityPrize.SubmissionLower.A3
open scoped Polynomial
abbrev opposite (i:Fin 2) :Fin 2 :=if i=0 then 1 else 0
private def substitute (i:Fin 2) :Over 2 →ₐ[aQ] aQ[X] :=
  MvPolynomial.aeval (fun j=>if j=i then z7y else z1z (ek 1))
private def coeffs :z3y (Fin 1) FX →+* aQ :=
  (algebraMap aZ aQ).comp (MvPolynomial.rename (fun _:Fin 1=>(1 :Fin 2))).toRingHom
private theorem coeffs_injective :zq4 coeffs :=
  (zxb aZ aQ).comp
    (MvPolynomial.rename_injective _ (fun _ _ _=>Subsingleton.elim _ _))
private abbrev EG:aZ →+* Over 2 :=zDK (algebraMap FX aQ)
private theorem substitute_degree (i:Fin 2) (f :aZ) :
    (substitute i (EG f)).natDegree=f.degreeOf i:= by
  have h: (substitute i).toRingHom.comp EG =
      (zhd coeffs).comp (AV i).toRingHom:= by
    apply zXT
    · intro a
      simp [zQb,co3,substitute,coeffs,zrD]
      rfl
    · intro j
      by_cases h:j=i <;>
        simp [zQb,bNH,substitute,coeffs,ek,h]
  rw [show substitute i (EG f)=(AV i f).map coeffs from zLs h f,
    zt8 coeffs_injective,dc2]
private def axisEquiv (i:Fin 2) (f :aZ) :
    Section (zye {f}) (opposite i) none ≃ₐ[aQ]
      (aQ[X] ⧸ zye {substitute i (EG f)}) := by
  let J:=ke (zye {f}) (opposite i) none
  let H :=zye {substitute i (EG f)}
  let q:=zvR aQ J
  let r :=zvR aQ H
  have hi:opposite i≠i:= by fin_cases i <;> decide
  have hJ:J=zye {EG f} ⊔ zye {Pp (opposite i)} := by
    simp only [J,ke,cut,Option.elim,Ideal.map_span,Set.image_singleton,EG]
  have hrel :q (z9v (opposite i)) =
      algebraMap aQ (Over 2 ⧸ J) (ek 1) := by
    have hz :q (Pp (opposite i))=0:=Ideal.Quotient.eq_zero_iff_mem.mpr
      (show Pp (opposite i)∈J from hJ.symm ▸ zs0 (z5J _))
    simpa only [Pp,map_sub,sub_eq_zero,MvPolynomial.algHom_C] using hz
  let s : (Over 2 ⧸ J) →ₐ[aQ] (aQ[X] ⧸ H) :=
    zTA J (r.comp (substitute i)) <| fun x hx=> by
      have hker :J≤zdq (r.comp (substitute i)).toRingHom:= by
        rw [hJ]
        apply sup_le <;> rw [zvl]
        · exact Ideal.Quotient.mk_singleton_self _
        · simp [RingHom.mem_ker,Pp,substitute,hi,zrD]
      exact hker hx
  let p:aQ[X] →ₐ[aQ] (Over 2 ⧸ J) :=Polynomial.aeval (q (z9v i))
  have hp:p.comp (substitute i)=q:= by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases h:j=i
    · subst j
      simp [p,substitute]
    · have hj:j=opposite i:= by fin_cases i <;> fin_cases j <;> simp_all
      subst j
      simpa [p,substitute,hi] using hrel.symm
  let t: (aQ[X] ⧸ H) →ₐ[aQ] (Over 2 ⧸ J) :=
    zTA H p <| fun x hx=> by
      have hker :H≤zdq p.toRingHom:= by
        change zye {substitute i (EG f)} ≤ zdq p.toRingHom
        rw [zvl,RingHom.mem_ker]
        exact (zmU hp (EG f)).trans
          (Ideal.Quotient.eq_zero_iff_mem.mpr
            (show EG f∈J from hJ.symm ▸ zKg (z5J _)))
      exact hker hx
  apply AlgEquiv.ofAlgHom s t
  · have h: (s.comp t).comp r=r := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply]
      have ht:t (r z7y)=q (z9v i) := by
        change p z7y=q (z9v i)
        exact Polynomial.aeval_X _
      rw [ht]
      change r (substitute i (z9v i))= _
      simp [substitute]
    ext x
    obtain ⟨x,rfl⟩:=zld x
    exact zmU h x
  · ext x
    obtain ⟨x,rfl⟩:=zld x
    exact zmU hp x
theorem axis_plane_degree (i:Fin 2) (f :aZ) :
    zsE aQ (Section (zye {f}) (opposite i) none)=f.degreeOf i:= by
  rw [(axisEquiv i f).toLinearEquiv.finrank_eq,finrank_quotient_span_eq_natDegree,substitute_degree]
end
end qjbBN1b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qjbBN1b
noncomputable section
open cu (FX)
open gT (Ambient gk aQ B4 Pp oi pZ)
open YY (xg)
open GK (Raw coord qw bg7)

open qRNngId (axisLength)
open private aii goA dcN a8q from ProximityPrize.SubmissionLower.G
open scoped Polynomial
attribute [local instance] Polynomial.algebra
local instance (n:ℕ) (I:znc (Raw n)) :za6 (gk I)[X] :=
  @zqU (gk I) (z0w I)
private abbrev castSeed :Fin 2→Fin 4 :=Fin.castLE (by decide)
private theorem cut_rename (i:Fin 2) (j:Option (Fin 2)) :
    a8q (cut i j)=cut (castSeed i) (j.map castSeed) := by
  cases j <;> simp [cut,Pp,B4,castSeed]
private def aWo (q:znc Ambient) (i:Fin 2) (j:Option (Fin 2)) :
    Section (xg q) i j →ₐ[aQ] Section q (castSeed i) (j.map castSeed) :=
  Ideal.quotientMapₐ (ke q (castSeed i) (j.map castSeed)) a8q <| by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr ?_) (Ideal.span_le.mpr ?_)
    · intro x hx
      change (a8q.toRingHom.comp (zDK (algebraMap FX aQ))) x ∈
        ke q (castSeed i) (j.map castSeed)
      rw [dcN]
      exact zKg (z7X _ hx)
    · rintro _ (rfl :_=cut i j)
      change a8q (cut i j)∈ke q (castSeed i) (j.map castSeed)
      rw [cut_rename]
      exact zs0 (z5J _)
private theorem raw_coord (q:znc Ambient) (i:Fin 2) :
    aii q (coord (xg q) i)=coord q (castSeed i) := by
  simp [aii,coord,oi,pZ,castSeed]
private theorem ao9 (q:znc Ambient) (a :FX) :
    aii q (algebraMap FX (gk (xg q)) a) =
      algebraMap FX (gk q) a := by
  simp [aii,oi,pZ,zKm]
  rfl
private theorem params_square (q:znc Ambient) (i:Fin 2) (j:Option (Fin 2)) :
    (zhd (aii q)).comp (params (xg q) i j) =
      params q (castSeed i) (j.map castSeed) := by
  apply zXT
  · intro a
    cases j <;> simp [params,qw,zQb,ao9]
  · intro k
    cases j <;> fin_cases k <;>
      simp [params,qw,raw_coord]
private theorem slice_square (q:znc Ambient) (i:Fin 2) (j:Option (Fin 2)) :
    (aWo q i j).toRingHom.comp (fromPoly (xg q) i j) =
      (fromPoly q (castSeed i) (j.map castSeed)).comp (zhd (aii q)) := by
  apply z86
  · intro a
    obtain ⟨a,rfl⟩:=zld a
    simp only [zQb,fromPoly,z4Q,zJU,
      zKC,zrL,fromRaw,Ideal.quotientMap_mk,
      aii,aWo,Ideal.quotient_map_mkₐ,Ideal.Quotient.mkₐ_eq_mk,
      AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
    exact congrArg (zVv _) (zLs dcN a)
  · simp [fromPoly,zQb]
private def polynomialRank {R A:Type} [za6 R] [za6 A] (g:R →+* A) :ℕ :=
  letI:zZE R A:=g.toAlgebra
  zsE R[X] A[X]
private theorem compareRings {F R A S T:Type}
    [Field F] [za6 R] [za6 A] [Field S] [Field T]
    [zZE F S] [zZE F T] [zAa F T]
    (g:R →+* A) (f :S →ₐ[F] T) (r :R[X] →+* S) (a :A[X] →+* T)
    (hs :letI:zZE R[X] S:=r.toAlgebra; z0o R[X] S)
    (ht:letI:zZE A[X] T:=a.toAlgebra; z0o A[X] T)
    (hc:f.toRingHom.comp r=a.comp (zhd g)) :
    0<polynomialRank g∧zsE F T=zsE F S*polynomialRank g:= by
  let:zZE S T:=f.toRingHom.toAlgebra
  let:zsf F S T:=zsL fun x=>(f.commutes x).symm
  let:zAa S T:=Module.Finite.of_restrictScalars_finite F S T
  let:zZE R[X] S:=r.toAlgebra
  let:zZE A[X] T:=a.toAlgebra
  let:z0o R[X] S:=hs
  let:z0o A[X] T:=ht
  let:zZE R A:=g.toAlgebra
  let:zZE R[X] T:=(f.toRingHom.comp r).toAlgebra
  let:zsf R[X] S T:=zsL fun _=>rfl
  let:zsf R[X] A[X] T:=IsScalarTower.of_algebraMap_eq' hc
  have he :zsE S T=polynomialRank g:=IsFractionRing.finrank_eq R[X] S A[X] T
  refine ⟨he ▸ Module.finrank_pos,?_⟩
  rw [← he]
  exact (Module.finrank_mul_finrank F S T).symm
private abbrev rawRank (q:znc Ambient) :ℕ :=
  @polynomialRank (gk (xg q)) (gk q)
    (z0w (xg q)) (z0w q) (aii q)
private theorem ranks (q:znc Ambient) [q.IsPrime] (i:Fin 2) (j:Option (Fin 2))
    [zAa aQ (Section (xg q) i j)]
    [zAa aQ (Section q (castSeed i) (j.map castSeed))]
    (hP:zq4 (params (xg q) i j)) :
    0< rawRank q ∧
      zsE aQ (Section q (castSeed i) (j.map castSeed)) =
        zsE aQ (Section (xg q) i j)*rawRank q:= by
  let P:=xg q
  let k :=castSeed i
  let l:=j.map castSeed
  let S:=Section P i j
  let T:=Section q k l
  let R:=(gk P)[X]
  let A:=(gk q)[X]
  have hp:P.IsPrime :=bg7 q
  have hQ:zq4 (params q k l) := by
    rw [← params_square]
    exact (Polynomial.map_injective _ (goA q)).comp hP
  let:ztn S:=section_domain P i j hP
  let:ztn T:=section_domain q k l hQ
  let:Field T:=fieldOfFiniteDimensional aQ T
  let:Field S:=fieldOfFiniteDimensional aQ S
  have hs :letI:zZE R S:=aXs P i j; z0o R S :=
    section_frac P i j hP
  have ht:letI:zZE A T:=aXs q k l; z0o A T :=
    section_frac q k l hQ
  exact @compareRings aQ (gk P) (gk q) S T
    inferInstance (z0w P) (z0w q) inferInstance inferInstance
    inferInstance inferInstance inferInstance
    (aii q) (aWo q i j) (fromPoly P i j) (fromPoly q k l) hs ht (slice_square q i j)
theorem proof :qRNngId.c1 := by
  intro q f hq hf himage hfinite
  have hprime :q.IsPrime :=hq.1
  have hjet:zAa aQ (Section q (castSeed 0) ((some 1).map castSeed)) :=hq.2.2.1
  have hdeg:0<f.totalDegree := by
    by_contra! h
    have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (za7 h)
    have hc:f.coeff 0≠0:= fun hz=>hf.ne_zero (by simpa [hz] using he)
    exact hf.not_isUnit (he ▸ hc.isUnit.map znf)
  have hplane :zsE aQ (Section (xg q) 0 (some 1))=f.totalDegree := by
    change zsE aQ (aBb.aLP (xg q))= _
    rw [himage,aBb.eLN f hf.ne_zero]
  have hp:0<zsE aQ (Section (xg q) 0 (some 1)) :=hplane.symm ▸ hdeg
  have :Nontrivial (Section (xg q) 0 (some 1)) :=zcE hp
  have hS:zAa aQ (Section (xg q) 0 (some 1)) :=zlS hp
  obtain ⟨hg,hline⟩ := @ranks q hprime 0 (some 1) hS hjet (params_injective (xg q) 0 (some 1))
  refine ⟨rawRank q,hg,?_,?_⟩
  · exact hline.trans (congrArg (· * rawRank q) hplane)
  · intro i
    by_cases hzero :f.degreeOf i=0
    · simp [hzero]
    have hpos :0<zsE aQ (Section (xg q) (opposite i) none) := by
      rw [himage,axis_plane_degree]
      exact zOl hzero
    have :Nontrivial (Section (xg q) (opposite i) none) :=zcE hpos
    have hS:zAa aQ (Section (xg q) (opposite i) none) :=zlS hpos
    have haxis :castSeed (opposite i)=if i=0 then (1 :Fin 4) else 0:= by
      fin_cases i <;> rfl
    have hT:zAa aQ (Section q (castSeed (opposite i)) none) := by
      rw [haxis]
      exact hfinite i
    have he :=(@ranks q hprime (opposite i) none hS hT (params_injective (xg q) (opposite i) none)).2
    have he' : axisLength q i=f.degreeOf i*rawRank q:= by
      fin_cases i <;> rw [himage,axis_plane_degree] at he <;> exact he
    exact he'.ge
end
end qjbBN1b
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace qmyaTMd
noncomputable section
open K1 (K p)
open cu (L FX aZ qD jz)
open YY (U7 by9 bnQ)
open P5_7 (OneSeedEquation NativeSeedBound)
open P5_7_7 (nativeEval ek ePy)
open MvPolynomial
open scoped Polynomial BigOperators
open private bDf from ProximityPrize.SubmissionLower.G
private theorem constant_cut (f :aZ) (hf :f≠0) :
    ∃ Q:z3y (Fin 2) L,Q≠0∧Q.support⊆f.support ∧
      ∀ x :Fin 2→L,zY9 (U7 ∘ x) f=0 →
        zY9 x Q=0:= by
  classical
  let b:=Module.Free.chooseBasis L FX
  obtain ⟨e,he⟩:=support_nonempty.mpr hf
  have he' := mem_support_iff.mp he
  have hrepr :b.repr (f.coeff e)≠0:= fun hz=>he' (b.repr.injective
    (hz.trans (map_zero b.repr).symm))
  obtain ⟨j,hj⟩:=Finsupp.support_nonempty_iff.mpr hrepr
  let ℓ:=b.coord j
  have hℓ:ℓ (f.coeff e)≠0:=Finsupp.mem_support_iff.mp hj
  let Q:z3y (Fin 2) L := ∑ m∈f.support,monomial m (ℓ (f.coeff m))
  have hcoeff (m:Fin 2 →₀ ℕ) :Q.coeff m=ℓ (f.coeff m) := by
    by_cases hm:m∈f.support
    · rw [show Q = ∑ n∈f.support,monomial n (ℓ (f.coeff n)) from rfl,coeff_sum,
        Finset.sum_eq_single_of_mem m hm]
      · simp
      · intro n _ hnm
        simp [coeff_monomial,hnm]
    · rw [notMem_support_iff.mp hm,map_zero]
      change (∑ n∈f.support,monomial n (ℓ (f.coeff n))).coeff m=0
      rw [coeff_sum]
      apply Finset.sum_eq_zero
      intro n hn
      have hnm:n≠m:= fun h=>hm (h ▸ hn)
      simp [coeff_monomial,hnm]
  refine ⟨Q,fun hz=>hℓ (by simpa [hz] using (hcoeff e).symm),?_,?_⟩
  · intro m hm
    by_contra h
    exact (mem_support_iff.mp hm) (by rw [hcoeff,notMem_support_iff.mp h,map_zero])
  · intro x hx
    have hx' : zY9 (U7 ∘ x) f =
        ∑ m∈f.support,f.coeff m*U7 (m.prod fun i k=>x i^k) := by
      conv_lhs=>rw [f.as_sum]
      simp only [map_sum,eval_monomial,Finsupp.prod,map_prod,map_pow,Function.comp_apply]
    have hEval :zY9 x Q=ℓ (zY9 (U7 ∘ x) f) := by
      simp only [Q,hx',map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [eval_monomial,bDf,mul_comm (f.coeff m),← Algebra.smul_def,
        map_smul,smul_eq_mul,mul_comm]
    rw [hEval,hx,map_zero]
private theorem bKS {f :aZ} (hf :Irreducible f)
    (hm : ¬ by9 (zye {f})) {Q:z3y (Fin 2) L}
    (hQ:Q≠0) (hs : (zDK U7 Q).support⊆f.support) :
    ¬ f∣zDK U7 Q:= by
  let B:=zDK U7 Q
  have hinj:=zNV (σ:=Fin 2) U7
    U7.injective
  have hB:B≠0:=(map_ne_zero_iff _ hinj).mpr hQ
  have hdeg:B.totalDegree≤f.totalDegree :=totalDegree_le_of_support_subset hs
  rintro ⟨a,ha⟩
  change B=f*a at ha
  have han:a≠0:= fun h=>hB (by simp [ha,h])
  have haz :a.totalDegree=0:= by
    rw [ha,totalDegree_mul_of_isDomain hf.ne_zero han] at hdeg
    omega
  have hau:IsUnit a :=(isUnit_iff_totalDegree_of_isReduced.mpr
    ⟨(by
      have h:=totalDegree_eq_zero_iff_eq_C.mp haz
      exact (isUnit_iff_ne_zero.mpr fun hz=>han (by rw [h,hz,map_zero]))),haz⟩)
  obtain ⟨u,hu⟩:=hau
  have hAssoc:Associated f B:=⟨u,by rw [hu,← ha]⟩
  let:IsLocalHom (zDK (σ:=Fin 2) U7) :=
    ⟨fun g hg=> by
      obtain ⟨h,hd⟩:=isUnit_iff_totalDegree_of_isReduced.mp hg
      rw [bnQ] at hd
      rw [coeff_map] at h
      exact isUnit_iff_totalDegree_of_isReduced.mpr
        ⟨(isUnit_iff_ne_zero.mpr fun hz=>h.ne_zero (by rw [hz,map_zero])),hd⟩⟩
  exact hm ⟨Q,(hAssoc.irreducible hf).of_map,Ideal.span_singleton_eq_span_singleton.mpr hAssoc⟩
private def bivar :aZ ≃+* OneSeedEquation :=
  ((renameEquiv FX Fin.revPerm).toRingEquiv.trans (finSuccEquiv FX 1).toRingEquiv).trans
    (Polynomial.mapEquiv (uniqueAlgEquiv FX (Fin 1)).toRingEquiv)
private theorem bivar_apply (f :aZ) :
    bivar f=(finSuccEquiv FX 1 (rename z8T f)).map
      (uniqueAlgEquiv FX (Fin 1)).toRingHom:=rfl
private theorem bivar_C (c:FX) :
    bivar (znf c)=z1z (z1z c) := by
  simp [bivar_apply,finSuccEquiv_apply,uniqueAlgEquiv_apply]
private theorem bivar_X_zero :
    bivar (z9v 0)=z1z Polynomial.X:= by
  rw [bivar_apply,rename_X,
    show z8T (0:Fin 2)=Fin.succ (0:Fin 1) by rfl,finSuccEquiv_X_succ,zrL]
  simp [uniqueAlgEquiv_apply]
private theorem bivar_X_one :
    bivar (z9v 1)=Polynomial.X:= by
  rw [bivar_apply,rename_X,show Fin.rev (1 :Fin 2)=0 by rfl,
    finSuccEquiv_X_zero,Polynomial.map_X]
private theorem bivar_eval (f :aZ) (z :K) :
    nativeEval z ((jz z)^p) (bivar f)=qD z f := by
  change ((nativeEval z ((jz z)^p)).comp bivar.toRingHom) f=qD z f
  apply zLs
  apply zXT
  · intro c
    simp [bivar_C,nativeEval,qD]
  · intro i
    fin_cases i <;> simp [bivar_X_zero,bivar_X_one,nativeEval,qD]
private theorem outer_degree (f :aZ) : (bivar f).natDegree=f.degreeOf 1 := by
  rw [bivar_apply,zt8 (uniqueAlgEquiv FX (Fin 1)).injective,
    natDegree_finSuccEquiv,← show z8T (1 :Fin 2)=0 by rfl]
  exact degreeOf_rename_of_injective Fin.rev_injective 1
private theorem inner_degree (f :aZ) :NativeSeedBound (bivar f) (f.degreeOf 0) := by
  intro i
  rw [bivar_apply,Polynomial.coeff_map,Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  change (uniqueAlgEquiv FX (Fin 1) ((finSuccEquiv FX 1 (rename z8T f)).coeff i)).coeff j=0
  rw [coeff_uniqueAlgEquiv]
  by_contra h
  have hle :=le_degreeOf_of_mem_support (0:Fin 1) (mem_support_iff.mpr h)
  have hcap:=degreeOf_coeff_finSuccEquiv (rename z8T f) (0:Fin 1) i
  rw [← show Fin.rev (0:Fin 2)=Fin.succ (0:Fin 1) by rfl,
    degreeOf_rename_of_injective Fin.rev_injective] at hcap
  exact (Nat.not_le.mpr hj) ((by simpa using hle :j≤_) |>.trans hcap)
private theorem generic_coprime {F G:OneSeedEquation} (hF:Irreducible F)
    (hdeg:0<F.natDegree) (h : ¬ F∣G) :IsCoprime (ek F) (ek G) := by
  let:StrongNormalizationMonoid (zM1 FX) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let:NormalizedGCDMonoid (zM1 FX) :=UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  have hp:=hF.isPrimitive hdeg.ne'
  have hi:=(hp.irreducible_iff_irreducible_map_fraction_map
    (K:=FractionRing (zM1 FX))).mp hF
  exact hi.coprime_iff_not_dvd.mpr fun hd=>h (hp.dvd_of_fraction_map_dvd_fraction_map hd)
private theorem no_common_root_of_zero_degree {F G:OneSeedEquation} (hF:Irreducible F)
    (hn : ¬ F∣G) (hF0:F.natDegree=0) (hG0:G.natDegree=0) {z :K} {y :FX}
    (hfr :nativeEval z y F=0) (hgr :nativeEval z y G=0) :False := by
  let d:zM1 FX:=z7y-Polynomial.C (jz z)
  have hF' := zr7 hF0
  have hG' := zr7 hG0
  have hdF:d∣F.coeff 0:=Polynomial.dvd_iff_isRoot.mpr (by
    rw [hF'] at hfr
    simpa [nativeEval,zT9] using hfr)
  have hdG:d∣G.coeff 0:=Polynomial.dvd_iff_isRoot.mpr (by
    rw [hG'] at hgr
    simpa [nativeEval,zT9] using hgr)
  obtain ⟨a,ha⟩:=map_dvd z1z hdF
  have he :F=z1z d*a :=hF'.trans ha
  have hnu : ¬ IsUnit (z1z d:OneSeedEquation) :=
    fun h=>Polynomial.not_isUnit_X_sub_C _ (Polynomial.isUnit_C.mp h)
  have hu:=(hF.isUnit_or_isUnit he).resolve_left hnu
  apply hn
  rw [he,hu.mul_right_dvd,hG']
  exact map_dvd z1z hdG
private theorem graph_constants (n:ℕ) (z :K) :
    U7 ∘ ![algebraMap K L z,(algebraMap K L z)^n] =
      ![jz z,(jz z)^n] :=
  funext (Fin.forall_fin_two.mpr ⟨rfl,map_pow U7 (algebraMap K L z) n⟩)
private theorem graph_cut {f :aZ} (hf :Irreducible f)
    (hm : ¬ by9 (zye {f})) :
    ∃ B:aZ,¬ f∣B∧(∀ i,B.degreeOf i≤f.degreeOf i) ∧
      ∀ z,qD z f=0→qD z B=0:= by
  obtain ⟨Q,hQ,hs,hroot⟩:=constant_cut f hf.ne_zero
  let B:=zDK U7 Q
  have hBsub:B.support⊆f.support := by
    rw [show B.support= Q.support from support_map_of_injective Q U7.injective]
    exact hs
  refine ⟨B,bKS hf hm hQ hBsub,?_,?_⟩
  · intro i
    rw [degreeOf_eq_sup,degreeOf_eq_sup]
    exact Finset.sup_mono hBsub
  · intro z hz
    have hr :=hroot _ (show zY9 (_ ∘ _) f=0 by
      rw [graph_constants p z]
      exact hz)
    change zY9 ![jz z,(jz z)^p]
      (zDK U7 Q)=0
    rw [← graph_constants p z,eval_map,← eval₂_comp,hr,map_zero]
private theorem bivar_count {F G:OneSeedEquation} {U V:ℕ} {CF:Finset K}
    {y :K→FX} (hF:Irreducible F) (hnd : ¬ F∣G) (hdF:F.natDegree=V)
    (hdG:G.natDegree≤V) (huF:NativeSeedBound F U) (huG:NativeSeedBound G U)
    (hfz : ∀ z∈CF,nativeEval z (y z) F=0)
    (hgz : ∀ z∈CF,nativeEval z (y z) G=0) :CF.card≤2*U*V:= by
  by_cases hpos :0<F.natDegree
  · refine (ePy huF huG hpos (generic_coprime hF hpos hnd)
      (z :=id) (fun _ _ _ _ h=>h) hfz hgz).trans ?_
    calc
      _≤V*U + V*U :=
        Nat.add_le_add (ztf _ hdF.le) (ztf _ hdG)
      _=2*U*V:= by rw [Nat.mul_comm V U,← Nat.add_mul,← Nat.two_mul]
  · have hF0:=Nat.eq_zero_of_not_pos hpos
    have hG0:G.natDegree=0:=za7 (by simpa [← hdF,hF0] using hdG)
    have hnil:CF = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun z ht =>
      no_common_root_of_zero_degree hF hnd hF0 hG0 (hfz z ht) (hgz z ht)
    simp [hnil]
theorem proof :qRNngId.c2 := by
  intro f CF hf hm hz
  obtain ⟨B,hB,hBdeg,hBroot⟩:=graph_cut hf hm
  let F:=bivar f
  let G:=bivar B
  have hF:Irreducible F:=(MulEquiv.irreducible_iff bivar.toMulEquiv).mpr hf
  have hnd : ¬ F∣G:= by
    intro hd
    apply hB
    have hh:=map_dvd bivar.symm.toRingHom hd
    change bivar.symm (bivar f)∣bivar.symm (bivar B) at hh
    simpa only [RingEquiv.symm_apply_apply] using hh
  have hfz (z :K) (h:z∈CF) :nativeEval z ((jz z)^p) F=0 :=
    (bivar_eval f z).trans (hz z h)
  have hgz (z :K) (h:z∈CF) :nativeEval z ((jz z)^p) G=0 :=
    (bivar_eval B z).trans (hBroot z (hz z h))
  have hdF:F.natDegree=f.degreeOf 1 :=outer_degree f
  have hdG:G.natDegree≤f.degreeOf 1 :=(outer_degree B).trans_le (hBdeg 1)
  have hG:NativeSeedBound G (f.degreeOf 0) := fun i=>(inner_degree B i).trans (hBdeg 0)
  exact bivar_count hF hnd hdF hdG (inner_degree f) hG hfz hgz
end
end qmyaTMd
end
section
set_option autoImplicit true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace qYKpuIc
noncomputable section
open cu (FX)
open gT (aQ ek Pp)
open private cRR from ProximityPrize.SubmissionLower.U
open private c2p from ProximityPrize.SubmissionLower.G
theorem proof :qu56FMb.c4 := by
  classical
  intro b x I hI hm
  have sl:YY.bAG I:=⟨hI.1,hI.2.1,hI.2.2.1,hI.2.2.2.1⟩
  obtain ⟨C,hC,hp,_,_⟩:=GK.proof I sl
  let _:I.IsPrime :=hI.1
  have fin (a :Fin 2) :zAa aQ (q3rjQGe.AxisSection I a) := by
    have he :I.map (zDK (algebraMap FX aQ)) ⊔ zye
        {zDK (algebraMap FX aQ) (z9v (if a=0 then 1 else 0)) +
          znf (ek 0)*zDK (algebraMap FX aQ) 0 -
            znf (ek 1)} =
        I.map (zDK (algebraMap FX aQ)) ⊔
          zye {Pp (if a=0 then (1 :Fin 4) else 0)} := by
      rw [z7N,map_zero,mul_zero,add_zero]
      rfl
    exact (congrArg (fun J=>zAa aQ (z3y (Fin 4) aQ ⧸ J)) he).mp
      (cRR I _ 0 hI.2.1)
  obtain ⟨g,hg,-,hb⟩:=qjbBN1b.proof I C sl hC hp fin
  have hl:=qmyaTMd.proof C ((P6_7_2_3.marks x I).image x.M.label) hC (hp ▸ hm) (by
    intro a ha
    obtain ⟨γ,hγ,rfl⟩:=Finset.mem_image.mp ha
    exact c2p (Finset.mem_filter.mp hγ).2 (hp ▸ z5J C))
  have hi:zq4 x.M.label := fun _ _ h=>sub_left_inj.mp h
  rw [Finset.card_image_of_injective _ hi] at hl
  have ax (i:Fin 2) :=(Nat.le_mul_of_pos_right (C.degreeOf i) hg).trans (hb i)
  change ((P6_7_2_3.marks x I).card:ℚ)≤2*((qRNngId.axisLength I 0:ℕ) :ℚ)*
    ((qRNngId.axisLength I 1 :ℕ) :ℚ)
  exact_mod_cast hl.trans (Nat.mul_le_mul (zBI 2 (ax 0)) (ax 1))
end
end qYKpuIc
end
section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
namespace qlfpcDe
noncomputable section
open cu (FX aZ)
open gT (Ambient gk aQ Pp oi pZ)

open YY (bAG U7 bnQ)
open q3rjQGe (AxisSection)
open qRNngId (axisLength)
open private cRR i9 from ProximityPrize.SubmissionLower.U
private theorem axis_finite (I:znc Ambient) [I.IsPrime]
    (hdim:ringKrullDim (gk I)=1) (i:Fin 2) :
    zAa aQ (AxisSection I i) := by
  let j:Fin 4 :=if i=0 then 1 else 0
  have he :i9 I (z9v j) 0 =
      I.map (zDK (algebraMap FX aQ)) ⊔ zye {Pp j} := by
    simp [i9,Pp]
  change zAa aQ
    (gk (I.map (zDK (algebraMap FX aQ)) ⊔ zye {Pp j}))
  rw [← he]
  exact cRR I (z9v j) 0 hdim
theorem proof :qu56FMb.c5:= by
  intro I geom hconst
  obtain ⟨C,hC,himg⟩:=hconst
  let:I.IsPrime :=geom.1
  have hs :bAG I:=⟨geom.1,geom.2.1,geom.2.2.1,geom.2.2.2.1⟩
  obtain ⟨g,hg,hroot,hplane⟩ :=
    aBb.of_children czq.proof bzX.proof
      I C hs geom.2.2.2.2 hC himg
  let f :aZ:=zDK U7 C
  have hin:zq4 U7:=U7.injective
  have hf :f≠0:= fun h=>hC.ne_zero
    (zNV _ hin (h.trans (map_zero _).symm))
  have hfprime : (zye {f}).IsPrime := by
    rw [← himg]
    exact (geom.1.comap oi).comap pZ
  have hfI:Irreducible f :=((Ideal.span_singleton_prime hf).mp hfprime).irreducible
  have hd:f.totalDegree=C.totalDegree :=bnQ C
  have hp:0<C.totalDegree := by
    apply zOl
    intro hz
    have he :=MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hz
    have hn:C.coeff 0≠0:= by
      intro h
      exact hC.ne_zero (by simpa only [h,map_zero] using he)
    exact hC.not_isUnit (he ▸ hn.isUnit.map znf)
  obtain ⟨d,_,hline,hdir⟩ :=
    qjbBN1b.proof I f hs hfI himg (axis_finite I geom.2.1)
  have hgd:g≤d:=Nat.le_of_mul_le_mul_left (by simpa only [hline,hd] using hplane) hp
  have hbounds (i:Fin 2) :C.degreeOf i*g≤axisLength I i:= by
    have he :f.degreeOf i=C.degreeOf i:= by
      simp only [f,MvPolynomial.degreeOf_eq_sup,MvPolynomial.support_map_of_injective _ hin]
    exact (zBI _ hgd).trans (by simpa only [he] using hdir i)
  refine ⟨C,g,hC,himg,hg,hp,hroot,hplane,?_,?_⟩
  · change (C.degreeOf 0:ℚ)*g≤(axisLength I 0:ℚ)
    exact_mod_cast hbounds 0
  · change (C.degreeOf 1 :ℚ)*g≤(axisLength I 1 :ℚ)
    exact_mod_cast hbounds 1
end
end qlfpcDe
end
