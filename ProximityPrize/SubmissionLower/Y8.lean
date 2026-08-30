import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.R7
import ProximityPrize.SubmissionLower.Y7
import ProximityPrize.SubmissionLower.BB
namespace ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection6543Research
open scoped Classical BigOperators WithZero TensorProduct
open Polynomial KaehlerDifferential IsDedekindDomain
open ArbitraryRationalProjectionResearch GlobalSeparableShearResearch
open CoordinateBoxZeroCount ContactSparsePoleSupportResearch
open ContactDependentGenericity6543Research
open ActualCurveCoordinateField ActualCurveRationalProjection ActualCurveZeroCount
open ContactRegularComponentCover
open ContactFlagAffineFamilyDegree6543Research
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 300000
theorem exists_nonzero_avoiding_finite_subsingleton
   {K ι:Type*} [Field K] [Infinite K] [Finite ι]
   (Bad:ι → K → Prop)
   (hsingle:∀ i {a b},Bad i a → Bad i b → a=b):
   ∃ a:K,a≠0∧∀ i,¬ Bad i a:=by
 classical
 letI:DecidableEq K:=Classical.decEq K
 letI:DecidableEq ι:=Classical.decEq ι
 letI:Fintype ι:=Fintype.ofFinite ι
 let representative:ι → K:=fun i↦
   if h:∃ a,Bad i a then Classical.choose h else 0
 let forbidden:Finset K:=Finset.univ.image representative
 obtain ⟨a,ha⟩:=Infinite.exists_notMem_finset (insert 0 forbidden)
 refine ⟨a,?_,?_⟩
 · intro hzero
   exact ha (hzero ▸ Finset.mem_insert_self 0 forbidden)
 · intro i hbad
   have hex:∃ b,Bad i b:=⟨a,hbad⟩
   have hrepbad:Bad i (representative i):=by
     simp only [representative,dif_pos hex]
     exact Classical.choose_spec hex
   have hab:a=representative i:=hsingle i hbad hrepbad
   have hmem:representative i∈forbidden:=by
     exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩
   exact ha (Finset.mem_insert_of_mem (hab ▸ hmem))
theorem valuation_shear_bad_coefficient_subsingleton
   {K L:Type*} [Field K] [Field L] [Algebra K L]
   (v:CoordinatePlaceClassification.NormalizedValuation K L)
   (r z:L):
   ∀ {a b:K},
     v.val (r+a • z) < max (v.val r) (v.val z) →
     v.val (r+b • z) < max (v.val r) (v.val z) → a=b:=by
 intro a b ha hb
 by_contra hab
 have hab0:a-b≠0:=sub_ne_zero.mpr hab
 letI:v.val.IsTrivialOn K:=v.property.2
 have hdiff:v.val ((r+a • z)-(r+b • z)) <
     max (v.val r) (v.val z):=v.val.map_sub_lt ha hb
 have hvaldiff:v.val ((r+a • z)-(r+b • z))=v.val z:=by
   rw [show (r+a • z)-(r+b • z)=(a-b) • z by module,
     Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one (a-b) hab0,one_mul]
 rw [hvaldiff] at hdiff
 have hzr:v.val z < v.val r:=by
   simpa only [lt_max_iff,lt_self_iff_false,or_false] using hdiff
 have hmax:max (v.val r) (v.val z)=v.val r:=max_eq_left hzr.le
 have ha0:a≠0:=by
   intro ha0
   rw [ha0,zero_smul,add_zero,hmax] at ha
   exact (lt_irrefl _ ha).elim
 have haz:v.val (a • z)=v.val z:=by
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 have hsum:v.val (r+a • z)=v.val r:=by
   apply v.val.map_add_eq_of_lt_left
   rwa [haz]
 rw [hsum,hmax] at ha
 exact (lt_irrefl _ ha).elim
section FiniteFamily
variable {K:Type*} [Field K] [IsAlgClosed K]
variable {I:Type*} [Fintype I]
variable (E:I → Type*) [∀ i,Field (E i)] [∀ i,Algebra K (E i)]
variable (r z:∀ i,E i)
variable (W:∀ i,
 Finset (CoordinatePlaceClassification.NormalizedValuation K (E i)))
theorem exists_common_exact_finite_separable_shear
   (embeddingZ:∀ i,RatFunc K →ₐ[K] E i)
   (hvalueZ:∀ i,embeddingZ i
     (algebraMap (Polynomial K) (RatFunc K) Polynomial.X)=z i)
   (hfiniteZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     FiniteDimensional (RatFunc K) (E i))
   (hsepZ:∀ i,
     letI:Algebra (RatFunc K) (E i):=
       (embeddingZ i).toRingHom.toAlgebra
     Algebra.IsSeparable (RatFunc K) (E i)):
   ∃ a:K,a≠0∧∀ i,
     ∃ hs:Transcendental K (r i+a • z i),
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         FiniteDimensional (RatFunc K) (E i))∧
       (letI:Algebra (RatFunc K) (E i):=
           (elementEmbedding K (E i) (r i+a • z i) hs).toRingHom.toAlgebra;
         Algebra.IsSeparable (RatFunc K) (E i))∧
       (∀ v∈W i,v.val (r i+a • z i)=
         max (v.val (r i)) (v.val (z i))):=by
 have hdz:∀ i,D K (E i) (z i)≠0:=by
   intro i
   have h:=parameterDifferential_ne_zero_of_isSeparable
     K (E i) (embeddingZ i) (hfiniteZ i) (hsepZ i)
   unfold SeparableShearKaehlerResearch.parameterDifferential at h
   rwa [hvalueZ i] at h
 let J:=I ⊕ Σ i:I,{v//v∈W i}
 let Bad:J → K → Prop
   | Sum.inl i,a => D K (E i) (r i)+a • D K (E i) (z i)=0
   | Sum.inr iv,a => iv.2.1.val (r iv.1+a • z iv.1) <
       max (iv.2.1.val (r iv.1)) (iv.2.1.val (z iv.1))
 have hsingle:∀ j {a b},Bad j a → Bad j b → a=b:=by
   intro j a b ha hb
   rcases j with i | ⟨i,v⟩
   · exact shear_bad_coefficient_subsingleton K (E i) (r i) (z i)
       (hdz i) ha hb
   · exact valuation_shear_bad_coefficient_subsingleton v.1 (r i) (z i) ha hb
 obtain ⟨a,ha0,havoid⟩:=
   exists_nonzero_avoiding_finite_subsingleton Bad hsingle
 refine ⟨a,ha0,fun i↦?_⟩
 have hdiff:D K (E i) (r i)+a • D K (E i) (z i)≠0:=by
   exact havoid (Sum.inl i)
 obtain ⟨hs,hfinite,hsep⟩:=
   shear_transcendental_finite_separable_of_differential_ne_zero
     K (E i) (embeddingZ i) (r i) (z i) a
       (hvalueZ i) (hfiniteZ i) (hsepZ i) hdiff
 refine ⟨hs,hfinite,hsep,?_⟩
 intro v hv
 have hnotlt:=havoid (Sum.inr ⟨i,⟨v,hv⟩⟩)
 have hupper:=v.val.map_add (r i) (a • z i)
 have haz:v.val (a • z i)=v.val (z i):=by
   letI:v.val.IsTrivialOn K:=v.property.2
   rw [Algebra.smul_def,map_mul,
     Valuation.IsTrivialOn.eq_one a ha0,one_mul]
 rw [haz] at hupper
 exact le_antisymm hupper (le_of_not_gt hnotlt)
end FiniteFamily
section RegularComponents
variable {Ω:Type} [Field Ω] [IsAlgClosed Ω]
variable {G T H:MvPolynomial (Fin 3) Ω}
structure NestedFlagProjectionData
   (hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2))
   (hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1) where
 lam:Ω
 lam_ne:lam≠0
 hU:∀ C:RegularComponent Ω G T H,
   Transcendental Ω (affineU Ω C.1 lam)
 finiteU:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1)
 separableU:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (affineU Ω C.1 lam) (hU C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1)
 exactU:∀ C:RegularComponent Ω G T H,
   ∀ v∈componentRelevantPlaces hseparator hproj C,
     v.val (affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 0))
         (v.val (coordinate Ω C.1 2))
 mu:Ω
 mu_ne:mu≠0
 hV:∀ C:RegularComponent Ω G T H,
   Transcendental Ω
     (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
 finiteV:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   FiniteDimensional (RatFunc Ω) (CoordinateField Ω C.1)
 separableV:∀ C:RegularComponent Ω G T H,
   letI:Algebra (RatFunc Ω) (CoordinateField Ω C.1):=
     (elementEmbedding Ω (CoordinateField Ω C.1)
       (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)
       (hV C)).toRingHom.toAlgebra
   Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω C.1)
 exactV:∀ C:RegularComponent Ω G T H,
   ∀ v∈componentRelevantPlaces hseparator hproj C,
     v.val (coordinate Ω C.1 1+mu • affineU Ω C.1 lam)=
       max (v.val (coordinate Ω C.1 1))
         (v.val (affineU Ω C.1 lam))
theorem nestedV_eq_affineV
   {hseparator:∀ C:RegularComponent Ω G T H,
     Transcendental Ω (coordinate Ω C.1 2)}
   {hproj:∀ C:RegularComponent Ω G T H,
     ProjectionsFiniteSeparable Ω C.1}
   (D:NestedFlagProjectionData hseparator hproj)
   (C:RegularComponent Ω G T H):
   coordinate Ω C.1 1+D.mu • affineU Ω C.1 D.lam=
     affineV Ω C.1 D.mu (D.mu*D.lam):=by
 simp only [affineU,affineV]
 simp only [smul_add,smul_smul,add_assoc]
end RegularComponents
end
end ProximityPrize.SubmissionLower.ContactFlagExactSeparableProjection6543Research
