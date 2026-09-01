import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BCHKSSeparableFactors
import ProximityPrize.SubmissionLower.PlaneCoefficientExtension
namespace ProximityPrize.SubmissionLower.PlaneRootSeparability
noncomputable section
variable {K L:Type} [Field K] [Field L] [Algebra K L]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq L:=Classical.decEq L
theorem integral_and_separable_of_small_annihilator
    (p:ℕ) [CharP K p] (f:Polynomial K) (x:L)
    (hf:f≠0) (hx:Polynomial.aeval x f=0) (hdegree:f.natDegree < p):
    IsIntegral K x∧IsSeparable K x:=by
  have hint:IsIntegral K x:=IsAlgebraic.isIntegral ⟨f,hf,hx⟩
  have hmin:(minpoly K x).natDegree ≤ f.natDegree:=
    Polynomial.natDegree_le_of_dvd (minpoly.dvd K x hx) hf
  refine ⟨hint,?_⟩
  change (minpoly K x).Separable
  apply (Polynomial.separable_def _).mpr
  exact irreducible_isCoprime_derivative_of_natDegree_lt_char p (minpoly K x)
    (minpoly.irreducible hint) (minpoly.natDegree_pos hint) (hmin.trans_lt hdegree)
theorem resultant_aeval_eq_zero_of_common_root
    (P Q:Polynomial (Polynomial K)) (m n:ℕ)
    (hPdegree:P.natDegree ≤ m) (hQdegree:Q.natDegree ≤ n)
    (hpositive:m≠0∨n≠0) (y r:L)
    (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
    (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0):
    Polynomial.aeval y (Polynomial.resultant P Q m n)=0:=by
  obtain ⟨U,V,_,_,hidentity⟩:=Polynomial.exists_mul_add_mul_eq_C_resultant
    P Q hPdegree hQdegree hpositive
  have heval:=congrArg
    (fun F:Polynomial (Polynomial K) =>
      Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r F) hidentity
  simp only [Polynomial.eval₂_add,Polynomial.eval₂_mul,Polynomial.eval₂_C,
    hP,hQ,zero_mul,zero_add] at heval
  exact heval.symm
theorem finite_separable_of_two_generators (y r:L)
    (hy:IsSeparable K y) (hr:IsSeparable K r)
    (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
    FiniteDimensional K L∧Algebra.IsSeparable K L:=by
  letI:FiniteDimensional K (IntermediateField.adjoin K ({y,r}:Set L)):=
    IntermediateField.finiteDimensional_adjoin_pair hy.isIntegral hr.isIntegral
  letI:Algebra.IsSeparable K (IntermediateField.adjoin K ({y,r}:Set L)):=
    IntermediateField.isSeparable_adjoin_pair_of_isSeparable K L hy hr
  letI:FiniteDimensional K (⊤:IntermediateField K L):=by
    rw [←hgenerate]
    infer_instance
  have hsepTop:Algebra.IsSeparable K (⊤:IntermediateField K L):=by
    rw [←hgenerate]
    infer_instance
  have hfinite:FiniteDimensional K L:=Module.Finite.of_surjective
    (IntermediateField.topEquiv (F:=K) (E:=L)).toLinearMap
    (IntermediateField.topEquiv (F:=K) (E:=L)).surjective
  exact ⟨hfinite,(IntermediateField.isSeparable_top (F:=K) (E:=L)).mp hsepTop⟩
theorem finite_separable_of_proper_plane_roots
    (p:ℕ) [CharP K p] (P Q:Polynomial (Polynomial K))
    (hirreducible:Irreducible P) (hpositive:0 < P.natDegree)
    (hproper:¬ P∣Q) (hRdegree:P.natDegree < p)
    (hresultantDegree:(Polynomial.resultant P Q P.natDegree Q.natDegree).natDegree < p)
    (y r:L)
    (hP:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r P=0)
    (hQ:Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap K L) y) r Q=0)
    (hgenerate:IntermediateField.adjoin K ({y,r}:Set L)=⊤):
    FiniteDimensional K L∧Algebra.IsSeparable K L:=by
  classical
  have hresne:=PlaneResultantIrreducible.irreducible_resultant_ne_zero_of_not_dvd
    P Q hirreducible hpositive hproper
  have hresroot:=resultant_aeval_eq_zero_of_common_root P Q
    P.natDegree Q.natDegree le_rfl le_rfl (Or.inl (Nat.ne_of_gt hpositive)) y r hP hQ
  obtain ⟨_,hySeparable⟩:=integral_and_separable_of_small_annihilator p
    (Polynomial.resultant P Q P.natDegree Q.natDegree) y hresne hresroot hresultantDegree
  let S:IntermediateField K L:=IntermediateField.adjoin K {y}
  let yS:S:=⟨y,IntermediateField.mem_adjoin_simple_self K y⟩
  letI:DecidableEq S:=Classical.decEq S
  letI:CharP S p:=charP_of_injective_algebraMap (algebraMap K S).injective p
  let g:Polynomial K →+*S:=Polynomial.eval₂RingHom (algebraMap K S) yS
  let Py:Polynomial S:=P.map g
  have hPyne:Py≠0:=by
    have h:=PlaneCoefficientExtension.bimap_specialization_ne_zero
      (algebraMap K S) P (hirreducible.isPrimitive (Nat.ne_of_gt hpositive)) yS
    rw [PlaneCoefficientExtension.bimap_specialization] at h
    exact h
  have hPydegree:Py.natDegree < p:=Polynomial.natDegree_map_le.trans_lt hRdegree
  have hcoefficient:(algebraMap S L).comp g=
      Polynomial.eval₂RingHom (algebraMap K L) y:=by
    apply Polynomial.ringHom_ext
    · intro c
      change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS (Polynomial.C c))=
        Polynomial.eval₂ (algebraMap K L) y (Polynomial.C c)
      rw [Polynomial.eval₂_C,Polynomial.eval₂_C]
      exact (IsScalarTower.algebraMap_apply K S L c).symm
    · change algebraMap S L (Polynomial.eval₂ (algebraMap K S) yS Polynomial.X)=
        Polynomial.eval₂ (algebraMap K L) y Polynomial.X
      rw [Polynomial.eval₂_X,Polynomial.eval₂_X]
      rfl
  have hPyroot:Polynomial.aeval r Py=0:=by
    change Polynomial.eval₂ (algebraMap S L) r (P.map g)=0
    rw [Polynomial.eval₂_map,hcoefficient]
    exact hP
  obtain ⟨_,hrSeparable⟩:=integral_and_separable_of_small_annihilator p
    Py r hPyne hPyroot hPydegree
  letI:Algebra.IsSeparable K S:=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K L).mpr hySeparable
  have hrOverK:IsSeparable K r:=
    IsSeparable.of_algebra_isSeparable_of_isSeparable K hrSeparable
  exact finite_separable_of_two_generators y r hySeparable hrOverK hgenerate
end
end ProximityPrize.SubmissionLower.PlaneRootSeparability
