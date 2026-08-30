import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.S0
import ProximityPrize.SubmissionLower.HY
import ProximityPrize.SubmissionLower.HZ
import ProximityPrize.SubmissionLower.U2
import ProximityPrize.SubmissionLower.F4
import ProximityPrize.SubmissionLower.V1
section ProximityFlatProofPort
open Module
open scoped nonZeroDivisors
section abs_norm
namespace Submodule
variable {R M:Type*} [Ring R] [AddCommGroup M] [Module R M]
section
noncomputable def cardQuot (S:Submodule R M):ℕ:=
 AddSubgroup.index S.toAddSubgroup
theorem cardQuot_apply (S:Submodule R M):cardQuot S=Nat.card (M ⧸ S):=by
 rfl
variable (R M)
@[simp]
theorem cardQuot_bot [Infinite M]:cardQuot (⊥:Submodule R M)=0:=
 AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite
@[simp]
theorem cardQuot_top:cardQuot (⊤:Submodule R M)=1:=
 AddSubgroup.index_top
variable {R M}
@[simp]
theorem cardQuot_eq_one_iff {P:Submodule R M}:cardQuot P=1 ↔ P=⊤:=
 AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])
end
end Submodule
section RingOfIntegers
variable {S:Type*} [CommRing S]
open Submodule
theorem cardQuot_mul_of_coprime
   {I J:Ideal S} (coprime:IsCoprime I J):cardQuot (I*J)=cardQuot I*cardQuot J:=by
 rw [cardQuot_apply,cardQuot_apply,cardQuot_apply,
   Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv,
   Nat.card_prod]
theorem Ideal.mul_add_mem_pow_succ_inj (P:Ideal S) {i:ℕ} (a d d' e e':S) (a_mem:a∈P^i)
   (e_mem:e∈P^(i+1)) (e'_mem:e'∈P^(i+1)) (h:d-d'∈P):
   a*d+e-(a*d'+e')∈P^(i+1):=by
 have:a*d-a*d'∈P^(i+1):=by
   simp only [←mul_sub]
   exact Ideal.mul_mem_mul a_mem h
 convert! Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
 ring
section PPrime
variable {P:Ideal S} [P_prime:P.IsPrime]
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] (hP:P≠⊥)
   {i:ℕ} (a c:S) (a_mem:a∈P^i)
   (a_notMem:a∉P^(i+1)) (c_mem:c∈P^i):
   ∃ d:S,∃ e∈P^(i+1),a*d+e=c:=by
 suffices eq_b:P^i=Ideal.span {a} ⊔ P^(i+1) by
   rw [eq_b] at c_mem
   simp only [mul_comm a]
   exact Ideal.mem_span_singleton_sup.mp c_mem
 refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
   (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a_mem))
     (Ideal.pow_succ_lt_pow hP i).le)).symm
 contrapose a_notMem with this
 rw [this]
 exact mem_sup.mpr ⟨a,mem_span_singleton_self a,0,by simp,by simp⟩
theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P:Ideal S} [P_prime:P.IsPrime]
   (hP:P≠⊥) {i:ℕ} {a b:S} (a_notMem:a∉P^(i+1)) (ab_mem:a*b∈P^(i+1)):
   b∈P:=by
 simp only [←Ideal.span_singleton_le_iff_mem, ←Ideal.dvd_iff_le,pow_succ, ←
   Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
 exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] (hP:P≠⊥)
   {i:ℕ} (a d d' e e':S)
   (a_notMem:a∉P^(i+1)) (e_mem:e∈P^(i+1)) (e'_mem:e'∈P^(i+1))
   (h:a*d+e-(a*d'+e')∈P^(i+1)):d-d'∈P:=by
 have h':a*(d-d')∈P^(i+1):=by
   convert! Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
   ring
 exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'
theorem cardQuot_pow_of_prime [IsDedekindDomain S] (hP:P≠⊥) {i:ℕ}:
   cardQuot (P^i)=cardQuot P^i:=by
 induction i with
 | zero => simp
 | succ i ih => ?_
 have:P^(i+1) < P^i:=Ideal.pow_succ_lt_pow hP i
 suffices hquot:map (P^i.succ).mkQ (P^i) ≃ S ⧸ P by
   rw [pow_succ' (cardQuot P), ←ih,cardQuot_apply (P^i.succ), ←
     card_quotient_mul_card_quotient (P^i) (P^i.succ) this.le,cardQuot_apply (P^i),
     cardQuot_apply P,Nat.card_congr hquot]
 choose a a_mem a_notMem using SetLike.exists_of_lt this
 choose f g hg hf using fun c (hc:c∈P^i) =>
   Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_notMem hc
 choose k hk_mem hk_eq using fun c' (hc':c'∈map (mkQ (P^i.succ)) (P^i)) =>
   Submodule.mem_map.mp hc'
 refine Equiv.ofBijective (fun c' => Quotient.mk'' (f (k c' c'.prop) (hk_mem c' c'.prop))) ⟨?_,?_⟩
 · rintro ⟨c₁',hc₁'⟩ ⟨c₂',hc₂'⟩ h
   rw [Subtype.mk_eq_mk, ←hk_eq _ hc₁', ←hk_eq _ hc₂',mkQ_apply,mkQ_apply,
     Submodule.Quotient.eq, ←hf _ (hk_mem _ hc₁'), ←hf _ (hk_mem _ hc₂')]
   refine Ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) ?_
   simpa only [Submodule.Quotient.mk''_eq_mk,Submodule.Quotient.mk''_eq_mk,
     Submodule.Quotient.eq] using h
 · intro d'
   induction d' using Quotient.inductionOn with | _ d
   have hd':=(mem_map (f:=mkQ (P^i.succ))).mpr ⟨a*d,Ideal.mul_mem_right d _ a_mem,rfl⟩
   refine ⟨⟨_,hd'⟩,?_⟩
   simp only [Submodule.Quotient.mk''_eq_mk,Ideal.Quotient.mk_eq_mk,Ideal.Quotient.eq]
   refine
     Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_notMem (hg _ (hk_mem _ hd')) (zero_mem _) ?_
   rw [hf,add_zero]
   exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')
end PPrime
theorem cardQuot_mul [IsDedekindDomain S] [Module.Free ℤ S] (I J:Ideal S):
   cardQuot (I*J)=cardQuot I*cardQuot J:=by
 let b:=Module.Free.chooseBasis ℤ S
 haveI:Infinite S:=Infinite.of_surjective _ b.repr.toEquiv.surjective
 exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
     (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI,Ideal.mul_top])
     (fun {I} i hI =>
       have:Ideal.IsPrime I:=Ideal.isPrime_of_prime hI
       cardQuot_pow_of_prime hI.ne_zero)
     fun {I J} hIJ => cardQuot_mul_of_coprime <| Ideal.isCoprime_iff_sup_eq.mpr
       (Ideal.isUnit_iff.mp
         (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))
noncomputable def Ideal.absNorm [IsDedekindDomain S] [Module.Free ℤ S]:
   Ideal S →*₀ ℕ where
 toFun:=Submodule.cardQuot
 map_mul' I J:=by rw [cardQuot_mul]
 map_one':=by rw [Ideal.one_eq_top,cardQuot_top]
 map_zero':=by
   have:Infinite S:=Module.Free.infinite ℤ S
   rw [Ideal.zero_eq_bot,cardQuot_bot]
namespace Ideal
variable [IsDedekindDomain S] [Module.Free ℤ S]
theorem absNorm_apply (I:Ideal S):absNorm I=cardQuot I:=rfl
lemma absNorm_eq_index (I:Ideal S):absNorm I=I.toAddSubgroup.index:=rfl
@[simp]
theorem absNorm_bot:absNorm (⊥:Ideal S)=0:=by rw [←Ideal.zero_eq_bot,map_zero]
@[simp]
theorem absNorm_top:absNorm (⊤:Ideal S)=1:=by rw [←Ideal.one_eq_top,map_one]
@[simp]
theorem absNorm_eq_one_iff {I:Ideal S}:absNorm I=1 ↔ I=⊤:=by
 rw [absNorm_apply,cardQuot_eq_one_iff]
theorem absNorm_ne_zero_iff (I:Ideal S):Ideal.absNorm I≠0 ↔ Finite (S ⧸ I):=
 ⟨fun h => Nat.finite_of_card_ne_zero h,fun h =>
   (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩
theorem absNorm_dvd_absNorm_of_le {I J:Ideal S} (h:J ≤ I):Ideal.absNorm I∣Ideal.absNorm J:=
 map_dvd absNorm (dvd_iff_le.mpr h)
theorem irreducible_of_irreducible_absNorm {I:Ideal S} (hI:Irreducible (Ideal.absNorm I)):
   Irreducible I:=
 irreducible_iff.mpr
   ⟨fun h =>
     hI.not_isUnit (by simpa only [Ideal.isUnit_iff,Nat.isUnit_iff,absNorm_eq_one_iff] using h),
     by
     rintro a b rfl
     simpa only [Ideal.isUnit_iff,Nat.isUnit_iff,absNorm_eq_one_iff] using
       hI.isUnit_or_isUnit (map_mul absNorm a b)⟩
theorem isPrime_of_irreducible_absNorm {I:Ideal S} (hI:Irreducible (Ideal.absNorm I)):
   I.IsPrime:=
 isPrime_of_prime
   (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))
theorem prime_of_irreducible_absNorm_span {a:S} (ha:a≠0)
   (hI:Irreducible (Ideal.absNorm (Ideal.span ({a}:Set S)))):Prime a:=
 (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)
theorem absNorm_mem (I:Ideal S):↑(Ideal.absNorm I)∈I:=by
 rw [absNorm_apply,cardQuot, ←Ideal.Quotient.eq_zero_iff_mem,map_natCast,
   Quotient.index_eq_zero]
theorem span_singleton_absNorm_le (I:Ideal S):Ideal.span {(Ideal.absNorm I:S)} ≤ I:=by
 simp only [Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe,Ideal.absNorm_mem I]
theorem span_singleton_absNorm {I:Ideal S} (hI:(Ideal.absNorm I).Prime):
   Ideal.span (singleton (Ideal.absNorm I:ℤ))=I.comap (algebraMap ℤ S):=by
 have:Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I:ℤ))):=by
   rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ←Nat.prime_iff_prime_int]
 apply (this.isMaximal _).eq_of_le
 · exact ((isPrime_of_irreducible_absNorm
     ((Nat.irreducible_iff_nat_prime _).mpr hI)).comap (algebraMap ℤ S)).ne_top
 · rw [span_singleton_le_iff_mem,mem_comap,algebraMap_int_eq,map_natCast]
   exact absNorm_mem I
 · rw [Ne,span_singleton_eq_bot]
   exact Int.ofNat_ne_zero.mpr hI.ne_zero
variable [Module.Finite ℤ S]
theorem natAbs_det_equiv (I:Ideal S) {E:Type*} [EquivLike E S I] [AddEquivClass E S I] (e:E):
   Int.natAbs
       (LinearMap.det
         ((Submodule.subtype I).restrictScalars ℤ ∘ₗ AddMonoidHom.toIntLinearMap (e:S →+I)))=
     Ideal.absNorm I:=by
 by_cases hI:I=⊥
 · subst hI
   have:(1:S)≠0:=one_ne_zero
   have:(1:S)=0:=EquivLike.injective e (Subsingleton.elim _ _)
   contradiction
 exact Submodule.natAbs_det_equiv (I.restrictScalars ℤ) e
theorem natAbs_det_basis_change {ι:Type*} [Fintype ι] [DecidableEq ι] (b:Basis ι ℤ S)
   (I:Ideal S) (bI:Basis ι ℤ I):(b.det ((↑) ∘ bI)).natAbs=Ideal.absNorm I:=
 Submodule.natAbs_det_basis_change b (I.restrictScalars ℤ) bI
@[simp]
theorem absNorm_span_singleton (r:S):
   absNorm (span ({r}:Set S))=(Algebra.norm ℤ r).natAbs:=by
 letI:DecidableEq S:=Classical.decEq S
 rw [Algebra.norm_apply]
 by_cases hr:r=0
 · simp only [hr,Ideal.span_zero,Ideal.absNorm_bot,
     LinearMap.det_zero'',Set.singleton_zero,map_zero,Int.natAbs_zero]
 let b:=Module.Free.chooseBasis ℤ S
 rw [←natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]
 congr
 refine b.ext fun i => ?_
 simp
lemma absNorm_span_natCast (n:ℕ):(span {(n:S)}).absNorm=n^Module.finrank ℤ S:=by
 simp [absNorm_span_singleton,Algebra.norm_natCast]
theorem absNorm_dvd_norm_of_mem {I:Ideal S} {x:S} (h:x∈I):
   ↑(Ideal.absNorm I)∣Algebra.norm ℤ x:=by
 rw [←Int.dvd_natAbs, ←absNorm_span_singleton x,Int.natCast_dvd_natCast]
 exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)
@[simp]
theorem absNorm_span_insert (r:S) (s:Set S):
   absNorm (span (insert r s))∣gcd (absNorm (span s)) (Algebra.norm ℤ r).natAbs:=
 (dvd_gcd_iff _ _ _).mpr
   ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
     _root_.trans
       (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
       (by rw [absNorm_span_singleton])⟩
theorem absNorm_eq_zero_iff {I:Ideal S}:Ideal.absNorm I=0 ↔ I=⊥:=by
 constructor
 · intro hI
   rw [←le_bot_iff]
   intro x hx
   rw [mem_bot, ←Algebra.norm_eq_zero_iff (R:=ℤ), ←Int.natAbs_eq_zero,
     ←Ideal.absNorm_span_singleton, ←zero_dvd_iff, ←hI]
   apply Ideal.absNorm_dvd_absNorm_of_le
   rwa [Ideal.span_singleton_le_iff_mem]
 · rintro rfl
   exact absNorm_bot
theorem absNorm_ne_zero_iff_mem_nonZeroDivisors {I:Ideal S}:
   absNorm I≠0 ↔ I∈(Ideal S)⁰:=by
 simp_rw [ne_eq,Ideal.absNorm_eq_zero_iff,mem_nonZeroDivisors_iff_ne_zero,Submodule.zero_eq_bot]
theorem absNorm_pos_iff_mem_nonZeroDivisors {I:Ideal S}:
   0 < absNorm I ↔ I∈(Ideal S)⁰:=by
 rw [←absNorm_ne_zero_iff_mem_nonZeroDivisors,Nat.pos_iff_ne_zero]
theorem absNorm_ne_zero_of_nonZeroDivisors (I:(Ideal S)⁰):absNorm (I:Ideal S)≠0:=
 absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)
theorem absNorm_pos_of_nonZeroDivisors (I:(Ideal S)⁰):0 < absNorm (I:Ideal S):=
 absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)
lemma finiteIndex {I:Ideal S} (hI:I≠⊥):I.toAddSubgroup.FiniteIndex:=by
 rwa [AddSubgroup.finiteIndex_iff, ←absNorm_eq_index,Ne,absNorm_eq_zero_iff]
open AddSubgroup in
lemma isFiniteRelIndex {I:Ideal S} (hI:I≠⊥) (J:Ideal S):
   I.toAddSubgroup.IsFiniteRelIndex J.toAddSubgroup:=by
 have:=finiteIndex hI
 exact isFiniteRelIndex_of_finiteIndex
lemma exists_prime_and_absNorm_eq_pow (P:Ideal S) [P.IsMaximal]:
   ∃ p n,0 < n∧↑p∈P∧p.Prime∧P.absNorm=p^n:=by
 have:IsAddTorsionFree S:=.of_isTorsionFree ℤ _
 have:=CharZero.of_isAddTorsionFree S S
 have:Finite (S ⧸ P):=Submodule.finiteQuotientOfFreeOfRankEq (P.restrictScalars ℤ)
   (Ideal.finrank_eq_finrank (Module.Free.chooseBasis _ _) _
     (Ideal.IsMaximal.ne_bot_of_isIntegral_int P))
 cases nonempty_fintype (S ⧸ P)
 letI:=Ideal.Quotient.field P
 obtain ⟨p,hpR⟩:=CharP.exists (S ⧸ P)
 obtain ⟨n,hp,e⟩:=FiniteField.card (S ⧸ P) p
 have hP:P.absNorm=p^(n:ℕ):=(Nat.card_eq_fintype_card.trans e:)
 refine ⟨p,n,n.2,?_,hp,hP⟩
 rw [←Ideal.IsPrime.pow_mem_iff_mem (I:=P) inferInstance _ n.pos, ←Nat.cast_pow, ←hP]
 exact P.absNorm_mem
lemma exists_isMaximal_dvd_of_dvd_absNorm
   {p:ℤ} (hp:Prime p) (I:Ideal S) (hI:p∣I.absNorm):
   ∃ P:Ideal S,P.IsMaximal∧P.under ℤ=.span {p}∧P∣I:=by
 have:IsAddTorsionFree S:=.of_isTorsionFree ℤ _
 have:=CharZero.of_isAddTorsionFree S S
 have hpMax:(Ideal.span {p}).IsMaximal:=
   ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
 induction I using UniqueFactorizationMonoid.induction_on_prime with
 | h₁ =>
   obtain ⟨Q,hQ,e⟩:=Ideal.exists_ideal_over_maximal_of_isIntegral (S:=S) (Ideal.span {p})
     (fun x↦by simp+contextual)
   exact ⟨Q,hQ,e,dvd_zero _⟩
 | h₂ I hI' =>
   obtain rfl:I=⊤:=by simpa using hI'
   cases hp.not_dvd_one (by simpa using hI)
 | h₃ I P hI' hP IH =>
   simp only [_root_.map_mul,Nat.cast_mul,hp.dvd_mul] at hI
   cases hI with
   | inr h =>
     obtain ⟨Q,h₁,h₂,h₃⟩:=IH h
     exact ⟨Q,h₁,h₂,dvd_mul_of_dvd_right h₃ _⟩
   | inl hI =>
     have:=(Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
     refine ⟨P,this,(hpMax.eq_of_le (by simpa using this.ne_top) ?_).symm,dvd_mul_right _ _⟩
     obtain ⟨q,n,hn,hqP,hq,H⟩:=Ideal.exists_prime_and_absNorm_eq_pow P
     rw [H,Nat.cast_pow,dvd_prime_pow (Nat.prime_iff_prime_int.mp hq)] at hI
     obtain ⟨m,hmn,hp⟩:=hI
     rw [Ideal.span_singleton_le_iff_mem]
     have:m≠0:=fun h↦hpMax.ne_top (Ideal.span_singleton_eq_top.mpr (by simpa [h] using hp))
     exact Ideal.mem_of_dvd _ hp.symm.dvd (Ideal.pow_mem_of_mem _ (by simpa) _ this.bot_lt)
lemma exists_isMaximal_dvd_of_dvd_absNorm'
   {p:ℕ} (hp:p.Prime) (I:Ideal S) (hI:p∣I.absNorm):
   ∃ P:Ideal S,P.IsMaximal∧P.under ℤ=.span {(p:ℤ)}∧P∣I:=
 exists_isMaximal_dvd_of_dvd_absNorm (Int.prime_iff_natAbs_prime.mpr (by simpa)) _
   (by exact_mod_cast hI)
theorem finite_setOf_absNorm_eq [CharZero S] (n:ℕ):
   {I:Ideal S | Ideal.absNorm I=n}.Finite:=by
 obtain hn | hn:=Nat.eq_zero_or_pos n
 · simp only [hn,absNorm_eq_zero_iff,Set.setOf_eq_eq_singleton,Set.finite_singleton]
 · let f:=fun I:Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
   refine Set.Finite.of_finite_image (f:=f) ?_ ?_
   · suffices Finite (S ⧸ @Ideal.span S _ {↑n}) by
       let g:=((↑):Ideal (S ⧸ @Ideal.span S _ {↑n}) → Set (S ⧸ @Ideal.span S _ {↑n}))
       refine Set.Finite.of_finite_image (f:=g) ?_ SetLike.coe_injective.injOn
       exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)
     rw [←absNorm_ne_zero_iff,absNorm_span_singleton]
     simpa only [Ne,Int.natAbs_eq_zero,Algebra.norm_eq_zero_iff,Nat.cast_eq_zero] using
       ne_of_gt hn
   · intro I hI J hJ h
     rw [←comap_map_mk (span_singleton_absNorm_le I), ←hI.symm, ←
       comap_map_mk (span_singleton_absNorm_le J), ←hJ.symm]
     congr
theorem finite_setOf_absNorm_le [CharZero S] (n:ℕ):
   {I:Ideal S | Ideal.absNorm I ≤ n}.Finite:=by
 rw [show {I:Ideal S | Ideal.absNorm I ≤ n}=
   (⋃ i∈Set.Icc 0 n,{I:Ideal S | Ideal.absNorm I=i}) by ext;simp]
 refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOf_absNorm_eq i)
theorem finite_setOf_absNorm_le₀ [CharZero S] (n:ℕ):
   {I:(Ideal S)⁰ | Ideal.absNorm (I:Ideal S) ≤ n}.Finite:=by
 have:Finite {I:Ideal S//I∈(Ideal S)⁰∧absNorm I ≤ n}:=
   (finite_setOf_absNorm_le n).subset fun _ ⟨_,h⟩↦h
 exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I↦absNorm I ≤ n)).symm
theorem norm_dvd_iff {x:S} (hx:Prime (Algebra.norm ℤ x)) {y:ℤ}:
   Algebra.norm ℤ x∣y ↔ x∣y:=by
 rw [←Ideal.mem_span_singleton (y:=x), ←eq_intCast (algebraMap ℤ S), ←Ideal.mem_comap,
   ←Ideal.span_singleton_absNorm,Ideal.mem_span_singleton,Ideal.absNorm_span_singleton,
   Int.natAbs_dvd]
 rwa [Ideal.absNorm_span_singleton, ←Int.prime_iff_natAbs_prime]
end Ideal
end RingOfIntegers
section Int
open Ideal
@[simp]
theorem Int.ideal_span_absNorm_eq_self (J:Ideal ℤ):
   span {(absNorm J:ℤ)}=J:=by
 obtain ⟨g,rfl⟩:=IsPrincipalIdealRing.principal J
 simp
@[simp]
theorem Int.prime_absNorm (J:Ideal ℤ):
   (absNorm J).Prime ↔ Prime J:=by
 obtain ⟨g,rfl⟩:=IsPrincipalIdealRing.principal J
 simp [prime_span_singleton_iff,prime_iff_natAbs_prime]
end Int
end abs_norm
