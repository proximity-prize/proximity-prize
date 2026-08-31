import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BC
namespace ProximityPrize.SubmissionLower.RCN285
open scoped BigOperators Pointwise
open RCN119
noncomputable section
variable (K:Type*) [Field K]
abbrev Poly:=MvPolynomial (Fin 3) K
def seedlessExponents (M L s:ℕ):Set (Fin 3 →₀ ℕ):=
 {d | d 0 ≤ M∧d 0+d 1 ≤ L∧d 1 ≤ s∧d 2=0}
def seedlessBox (M L s:ℕ):Submodule K (Poly K):=
 MvPolynomial.restrictSupport K (seedlessExponents M L s)
theorem seedlessBox_mul
   {M L s M' L' s':ℕ} {f g:Poly K}
   (hf:f∈seedlessBox K M L s)
   (hg:g∈seedlessBox K M' L' s'):
   f*g∈seedlessBox K (M+M') (L+L') (s+s'):=by
 have hset:seedlessExponents M L s+seedlessExponents M' L' s' ⊆
     seedlessExponents (M+M') (L+L') (s+s'):=by
   rintro _ ⟨d,hd,e,he,rfl⟩
   rcases hd with ⟨hd0,hd01,hd1,hd2⟩
   rcases he with ⟨he0,he01,he1,he2⟩
   simp only [seedlessExponents,Set.mem_setOf_eq,Finsupp.add_apply]
   exact ⟨by omega,by omega,by omega,by omega⟩
 apply MvPolynomial.restrictSupport_mono (R:=K) hset
 rw [MvPolynomial.restrictSupport_add]
 exact Submodule.mul_mem_mul hf hg
theorem slopeDifference_mem_seedlessBox:
   slopeDifference K∈seedlessBox K 1 1 1:=by
 apply (seedlessBox K 1 1 1).sub_mem
 · change MvPolynomial.monomial (Finsupp.single 0 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
 · change MvPolynomial.monomial (Finsupp.single 1 1) (1:K)∈_
   apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
   left
   simp [seedlessExponents]
theorem slopeDifference_pow_mem_seedlessBox (h:ℕ):
   slopeDifference K^h∈seedlessBox K h h h:=by
 induction h with
 | zero =>
     simp only [pow_zero]
     change MvPolynomial.monomial 0 (1:K)∈_
     apply (MvPolynomial.monomial_mem_restrictSupport (R:=K)).mpr
     left
     simp [seedlessExponents]
 | succ h ih =>
     simpa only [pow_succ] using
       seedlessBox_mul K ih (slopeDifference_mem_seedlessBox K)
theorem slopeDifference_mul_mem_seedlessBox
   {M L s h:ℕ} (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s)
   {q:Poly K} (hq:q∈seedlessBox K (M-h) (L-h) (s-h)):
   slopeDifference K^h*q∈seedlessBox K M L s:=by
 have hh:=seedlessBox_mul K (slopeDifference_pow_mem_seedlessBox K h) hq
 simpa only [Nat.add_sub_of_le hM,Nat.add_sub_of_le hL,
   Nat.add_sub_of_le hs] using hh
private def exponentPair (i j:ℕ):Fin 3 →₀ ℕ:=
 Finsupp.single 0 i+Finsupp.single 1 j
@[simp] private theorem exponentPair_zero (i j:ℕ):
   exponentPair i j 0=i:=by simp [exponentPair]
@[simp] private theorem exponentPair_one (i j:ℕ):
   exponentPair i j 1=j:=by simp [exponentPair]
@[simp] private theorem exponentPair_two (i j:ℕ):
   exponentPair i j 2=0:=by simp [exponentPair]
private theorem exponentPair_eta (d:Fin 3 →₀ ℕ) (hd:d 2=0):
   exponentPair (d 0) (d 1)=d:=by
 ext i
 fin_cases i <;> simp [hd]
abbrev SeedlessBoxIndex (M L s:ℕ):=
 (i:Fin (M+1)) × Fin (min (s+1) (L+1-i.val))
private theorem fin_heq_of_val_eq
   {a b:ℕ} {u:Fin a} {v:Fin b}
   (hab:a=b) (huv:u.val=v.val):HEq u v:=by
 subst b
 exact heq_of_eq (Fin.ext huv)
def seedlessExponentsEquivIndex (M L s:ℕ):
   seedlessExponents M L s ≃ SeedlessBoxIndex M L s where
 toFun d:=
   ⟨⟨d.val 0,Nat.lt_succ_of_le d.property.1⟩,
     ⟨d.val 1,by
       rcases d.property with ⟨_,h01,h1,_⟩
       rw [lt_min_iff]
       constructor
       · omega
       · change d.val 1 < L+1-d.val 0
         omega⟩⟩
 invFun q:=
   ⟨exponentPair q.1.val q.2.val,by
     have hi:=q.1.isLt
     have hj:=q.2.isLt
     rw [lt_min_iff] at hj
     simp only [seedlessExponents,Set.mem_setOf_eq,exponentPair_zero,
       exponentPair_one,exponentPair_two]
     exact ⟨by omega,by omega,by omega,by simp⟩⟩
 left_inv d:=Subtype.ext (exponentPair_eta d.val d.property.2.2.2)
 right_inv q:=by
   rcases q with ⟨⟨i,hi⟩,⟨j,hj⟩⟩
   apply Sigma.ext
   · apply Fin.ext
     exact exponentPair_zero i j
   · apply fin_heq_of_val_eq
     · simp only [exponentPair_zero]
     · exact exponentPair_one i j
instance seedlessExponentsFintype (M L s:ℕ):
   Fintype (seedlessExponents M L s):=
 Fintype.ofEquiv (SeedlessBoxIndex M L s)
   (seedlessExponentsEquivIndex M L s).symm
instance seedlessBoxFinite (M L s:ℕ):
   Module.Finite K (seedlessBox K M L s):=
 Module.Finite.of_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))
def seedlessInputCount (M L s:ℕ):ℕ:=
 ∑ i∈Finset.range (M+1),min (s+1) (L+1-i)
theorem seedlessBox_finrank (M L s:ℕ):
   Module.finrank K (seedlessBox K M L s)=seedlessInputCount M L s:=by
 change Module.finrank K
     (MvPolynomial.restrictSupport K (seedlessExponents M L s))=_
 rw [Module.finrank_eq_card_basis
   (MvPolynomial.basisRestrictSupport K (seedlessExponents M L s))]
 rw [Fintype.card_congr (seedlessExponentsEquivIndex M L s)]
 simp [SeedlessBoxIndex,seedlessInputCount,Fintype.card_sigma,
   Finset.sum_range]
def seedlessBlockJet (M L s h:ℕ):
   seedlessBox K M L s →ₗ[K] Poly K:=
 (contactJet K h).comp (seedlessBox K M L s).subtype
def multiplyIntoSeedlessBox {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     seedlessBox K M L s where
 toFun q:=⟨slopeDifference K^h*q.val,
   slopeDifference_mul_mem_seedlessBox K hM hL hs q.property⟩
 map_add' q r:=by apply Subtype.ext;simp [mul_add]
 map_smul' c q:=by apply Subtype.ext;simp [mul_smul_comm]
theorem multiplyIntoSeedlessBox_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (multiplyIntoSeedlessBox K hM hL hs):=by
 intro q r heq
 apply Subtype.ext
 have hh:slopeDifference K^h*q.val=
     slopeDifference K^h*r.val:=congrArg Subtype.val heq
 exact mul_left_cancel₀ (pow_ne_zero h (slopeDifference_ne_zero K)) hh
def seedlessKernelEmbedding {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   seedlessBox K (M-h) (L-h) (s-h) →ₗ[K]
     LinearMap.ker (seedlessBlockJet K M L s h):=
 LinearMap.codRestrict (LinearMap.ker (seedlessBlockJet K M L s h))
   (multiplyIntoSeedlessBox K hM hL hs) (fun q => by
     change contactJet K h (slopeDifference K^h*q.val)=0
     exact contactJet_mul_slopeDifference K h q.val)
theorem seedlessKernelEmbedding_injective {M L s h:ℕ}
   (hM:h ≤ M) (hL:h ≤ L) (hs:h ≤ s):
   Function.Injective (seedlessKernelEmbedding K hM hL hs):=by
 intro q r heq
 apply multiplyIntoSeedlessBox_injective K hM hL hs
 exact congrArg Subtype.val heq
def seedlessKernelLowerBound (M L s h:ℕ):ℕ:=
 if h ≤ M∧h ≤ L∧h ≤ s then
   seedlessInputCount (M-h) (L-h) (s-h)
 else 0
def seedlessContactRankBound (M L s h:ℕ):ℕ:=
 seedlessInputCount M L s-seedlessKernelLowerBound M L s h
theorem seedlessBlockJet_rank_le_contactRankBound
   (M L s h:ℕ) (hML:M ≤ L):
   Module.finrank K (LinearMap.range (seedlessBlockJet K M L s h)) ≤
     seedlessContactRankBound M L s h:=by
 by_cases hM:h ≤ M
 · by_cases hs:h ≤ s
   · have hL:h ≤ L:=hM.trans hML
     have hker:=LinearMap.finrank_le_finrank_of_injective
       (seedlessKernelEmbedding_injective K hM hL hs)
     have hsum:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hker
     rw [seedlessBox_finrank K] at hsum
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_pos ⟨hM,hL,hs⟩]
     omega
   · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
       intro hh
       exact hs hh.2.2
     have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
     rw [seedlessBox_finrank K] at hinput
     unfold seedlessContactRankBound seedlessKernelLowerBound
     rw [if_neg hbad,Nat.sub_zero]
     omega
 · have hbad:¬ (h ≤ M∧h ≤ L∧h ≤ s):=by
     intro hh
     exact hM hh.1
   have hinput:=(seedlessBlockJet K M L s h).finrank_range_add_finrank_ker
   rw [seedlessBox_finrank K] at hinput
   unfold seedlessContactRankBound seedlessKernelLowerBound
   rw [if_neg hbad,Nat.sub_zero]
   omega
end
end ProximityPrize.SubmissionLower.RCN285
