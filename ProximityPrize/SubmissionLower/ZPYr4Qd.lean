import ProximityPrize.SubmissionLower.Z8zQzne
set_option Elab.async false
open _root_ renaming Ideal → znc, Ideal.Quotient.factor_surjective → zuo, Ideal.Quotient.factorₐ → z5F, Ideal.comap → zK3, Ideal.comap_comap → zg6, Ideal.comap_map_of_bijective → zFA, Ideal.mem_map_of_mem → z7X, Ideal.mem_span_singleton_self → z5J, Ideal.mem_sup_left → zKg, Ideal.mem_sup_right → zs0, Ideal.span → zye, Module.Finite → zAa, Module.finrank → zsE, MvPolynomial.renameEquiv → zGY
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace qPP0zte
noncomputable section
open Finset
open K1 (p)
open cu (Shape FX)
open gT (Ambient aQ Pp)
open pI (xN dual)
open ac4 (Hr btg)
open OH (N8 Q6)


open qu56FMb
open Rk (KR bsm)
open scoped Classical BigOperators
def c1 :Prop :=
  ∀ (s :Shape) (Q:znc Ambient) (f :Ambient) (k :Fin 3),
    (k=0∨k=1)→s.J≤ s.B→xN Q→dual Q→f∉Q→RectCaps s f →
    zAa aQ (N8 ⧸ bR k Q f) ∧
    (length (bR k Q f) :ℚ)≤budget s Q k
def c2 :Prop :=
  ∀ (I:znc N8) (f :N8) (v :ℕ),
    I.IsMaximal→zAa aQ (N8 ⧸ I)→length I<p →
    (∀ a :Exponent,(∑ i,a i)≤v→KR a f∈I)→f∈I^(v+1)
def c3:Prop :=
  ∀ (k R:Type) [Field k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
    (Q:znc R) (f :R) (A:Finset (znc R)) (w:znc R→ℕ),
    Q.IsPrime→f∉Q→zAa k (R ⧸ (Q ⊔ zye {f})) →
    (∀ I∈A,I.IsMaximal∧Q ⊔ zye {f} ≤ I∧0<w I∧f∈Q ⊔ I^(w I)) →
    ∑ I∈A,w I*zsE k (R ⧸ I)≤zsE k (R ⧸ (Q ⊔ zye {f}))
private theorem axis_prime (i:Fin 4) {I:znc Ambient} (hp:I.IsPrime)
    (ht:I.map Q6 ⊔ zye {Pp i} ≠ ⊤) :
    (I.map Q6 ⊔ zye {Pp i}).IsPrime ∧
      (I.map Q6 ⊔ zye {Pp i}).comap Q6=I:= by
  let e :=Equiv.swap i 2
  let u:=(zGY FX e).toRingEquiv
  let U:=(zGY aQ e).toRingEquiv
  have he :e i=2 :=Equiv.swap_apply_left _ _
  have hcom:U.toRingHom.comp Q6= Q6.comp u.toRingHom:= by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [u,U,Q6]
    · intro j
      simp [u,U,Q6]
  have hdir :U.toRingHom (Pp i)=Pp 2 := by simp [U,Pp,he]
  have hU (A:znc N8) : (A.map U.toRingHom).comap U.toRingHom=A :=
    zFA U.toRingHom U.bijective
  have huInv : (I.map u.toRingHom).comap u.toRingHom=I :=
    zFA u.toRingHom u.bijective
  let J:=I.map Q6 ⊔ zye {Pp i}
  have hJ:J.map U.toRingHom=Hr (I.map u.toRingHom) := by
    rw [show J=I.map Q6 ⊔ zye {Pp i} from rfl,
      Ideal.map_sup,Ideal.map_map,hcom,← Ideal.map_map,Ideal.map_span,Set.image_singleton,hdir]
    rfl
  have htop:Hr (I.map u.toRingHom) ≠ ⊤ := by
    intro h
    have hh:=congrArg (zK3 U.toRingHom) (hJ.trans h)
    rw [hU,Ideal.comap_top] at hh
    exact ht hh
  have hu: (I.map u.toRingHom).IsPrime := by
    rw [show I.map u.toRingHom=I.comap u.symm.toRingHom from Ideal.map_comap_of_equiv u]
    exact hp.comap u.symm.toRingHom
  obtain ⟨hprime,hcontra⟩:=(btg _ hu).1 (by
    by_contra h
    exact htop ((btg _ hu).2 h))
  change J.IsPrime∧J.comap Q6=I
  constructor
  · have hh:=hprime.comap U.toRingHom
    rwa [← hJ,hU] at hh
  · change (Hr (I.map u.toRingHom)).comap Q6=I.map u.toRingHom at hcontra
    have hh:=congrArg (zK3 u.toRingHom) hcontra
    rw [zg6,← hcom,← zg6,← hJ,
      hU,huInv] at hh
    exact hh
private theorem slice_prime (k :Fin 3) {I:znc Ambient}
    (hp:I.IsPrime) (ht:slice k I ≠ ⊤) :
    (slice k I).IsPrime∧(slice k I).comap Q6=I:= by
  fin_cases k
  · exact axis_prime 1 hp ht
  · exact axis_prime 0 hp ht
  · exact cza.proof I hp ht
private theorem component_le {Q I:znc Ambient} {f :Ambient}
    (hI:I∈qv Q f) (k :Fin 3) :bR k Q f≤ slice k I:= by
  have h:=(Ideal.mem_minimalPrimesFinset.mp (mem_filter.mp hI).1).le
  refine sup_le (sup_le_sup_right (Ideal.map_mono (le_sup_left.trans h)) _) ?_
  exact (Ideal.span_singleton_le_iff_mem _).mpr (zKg
    (z7X _ (h (zs0 (z5J _)))))
private theorem length_le {A B:znc N8} [zAa aQ (N8 ⧸ A)]
    (h:A≤B) :length B≤length A :=
  LinearMap.finrank_le_finrank_of_surjective (f :=(z5F aQ h).toLinearMap)
    (zuo h)
private theorem positive_weight (f :Ambient) (v :ℕ) (I:znc Ambient) :
    0<paidWeight f v I:= by
  unfold paidWeight
  split <;> omega
private theorem HE (h2 :c2) (h3:c3)
    (k :Fin 3) {Q:znc Ambient} {f :Ambient} (ha :xN Q) (hf :f∉Q) (v :ℕ)
    [zAa aQ (N8 ⧸ bR k Q f)] (hsmall:length (bR k Q f)<p) :
    ∑ I∈qv Q f,paidWeight f v I*length (slice k I)≤length (bR k Q f) := by
  let S:=(qv Q f).filter (fun I=>slice k I ≠ ⊤)
  have hsum :
      ∑ I∈qv Q f,paidWeight f v I*length (slice k I) =
        ∑ I∈S,paidWeight f v I*length (slice k I) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro I hi hout
    have ht:slice k I = ⊤ := by simpa [S,hi] using hout
    have :Subsingleton (N8 ⧸ slice k I) :=Ideal.Quotient.subsingleton_iff.mpr ht
    change paidWeight f v I*zsE aQ (N8 ⧸ slice k I)=0
    rw [Module.finrank_eq_zero_of_subsingleton,mul_zero]
  rw [hsum]
  by_cases hS:S.Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hS,sum_empty]
    exact Nat.zero_le _
  have hparent :slice k Q ≠ ⊤ := by
    obtain ⟨I,hi⟩:=hS
    obtain ⟨hc,ht⟩:=mem_filter.mp hi
    exact ne_top_of_le_ne_top ht (le_sup_left.trans (component_le hc k))
  obtain ⟨hq,hcomap⟩:=slice_prime k ha.prime hparent
  have hproper :Q6 f∉slice k Q:= fun h =>
    hf (hcomap ▸ (show f∈(slice k Q).comap Q6 from h))
  have hsub (I:znc Ambient) (hi:I∈S) :
      (slice k I).IsPrime∧(slice k I).comap Q6=I:= by
    obtain ⟨hc,ht⟩:=mem_filter.mp hi
    exact slice_prime k (Ideal.mem_minimalPrimesFinset.mp (mem_filter.mp hc).1).isPrime ht
  let w (A:znc N8) :=paidWeight f v (A.comap Q6)
  have hmass : ∑ I∈S,paidWeight f v I*length (slice k I) =
      ∑ A∈S.image (slice k),w A*length A:= by
    rw [sum_image (fun I hi J hj he=>(hsub I hi).2.symm.trans
      ((congrArg (zK3 Q6) he).trans (hsub J hj).2))]
    exact sum_congr rfl fun I hi=> by
      change _=paidWeight f v ((slice k I).comap Q6)*_
      rw [(hsub I hi).2]
  rw [hmass]
  apply h3 aQ N8 (slice k Q) (Q6 f) _ w hq hproper inferInstance
  intro A hA
  obtain ⟨I,hi,rfl⟩:=mem_image.mp hA
  have hle :=component_le (mem_filter.mp hi).1 k
  let: (slice k I).IsPrime :=(hsub I hi).1
  let:zAa aQ (N8 ⧸ slice k I) :=
    Module.Finite.of_surjective (z5F aQ hle).toLinearMap
      (zuo hle)
  have :Algebra.IsIntegral aQ (N8 ⧸ slice k I) :=Algebra.IsIntegral.of_finite ..
  have hm: (slice k I).IsMaximal:=Ideal.Quotient.maximal_of_isField (slice k I)
    (isField_of_isIntegral_of_isField' (S:=N8 ⧸ slice k I) (Field.toIsField aQ))
  rw [show w (slice k I)=paidWeight f v I from congrArg (paidWeight f v) (hsub I hi).2]
  refine ⟨hm,hle,positive_weight f v I,?_⟩
  by_cases hp:PaidOn f v I
  · rw [paidWeight,ite_eq_left hp]
    apply zs0
    apply h2 (slice k I) (Q6 f) v hm inferInstance ((length_le hle).trans_lt hsmall)
    intro a ha
    have he :KR a (Q6 f)= Q6 (KR a f) :=
      (bsm (algebraMap FX aQ) a f).symm
    rw [he]
    exact zKg (z7X Q6 (hp a ha))
  · simpa only [paidWeight,ite_eq_right hp,pow_one] using zs0
      (S:=slice k Q) (hle (zs0 (z5J (Q6 f))))
private theorem rational_weighted (h2 :c2) (h3:c3)
    (k :Fin 3) {Q:znc Ambient} {f :Ambient} (ha :xN Q) (hf :f∉Q) (v :ℕ)
    [zAa aQ (N8 ⧸ bR k Q f)] (hsmall:length (bR k Q f)<p) :
    divisorMass Q f v (fun I=>length (slice k I))≤length (bR k Q f) := by
  have h:=(Nat.cast_le (α:=ℚ)).mpr (HE h2 h3 k ha hf v hsmall)
  simpa only [Nat.cast_sum,Nat.cast_mul,divisorMass] using h
end
end qPP0zte
