import ProximityPrize.Benchmark.TargetLower
namespace ProximityPrize.SubmissionLower.ContactRegularQuotient6731Research
open IsLocalRing Ideal
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 2000000
variable {A:Type*} [CommRing A] [IsDomain A] [IsRegularLocalRing A]
private theorem exists_pair_generator_of_not_mem_sq
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2):
   ∃ g∈maximalIdeal A,maximalIdeal A=Ideal.span {f,g}:=by
 classical
 let m:=maximalIdeal A
 have hfg:m.FG:=m.fg_of_isNoetherianRing
 have hrank:m.spanFinrank=2:=by
   have hreg:=(isRegularLocalRing_iff A).mp (inferInstance:IsRegularLocalRing A)
   rw [hdim] at hreg
   exact_mod_cast hreg
 have hcard:m.generators.ncard=2:=by
   rw [Submodule.FG.generators_ncard hfg,hrank]
 obtain ⟨a,b,hab,hgen⟩:=Set.ncard_eq_two.mp hcard
 have hspan:Ideal.span {a,b}=m:=by
   simpa [hgen] using m.span_generators
 have ha:a∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hb:b∈m:=Submodule.FG.generators_mem m (by simp [hgen])
 have hfm:f∈m:=by simpa [m] using hf
 have hfspan:f∈Ideal.span ({a,b}:Set A):=by rwa [hspan]
 obtain ⟨r,s,hrs⟩:=Ideal.mem_span_pair.mp hfspan
 have hunit:IsUnit r∨IsUnit s:=by
   letI:Decidable (IsUnit r):=Classical.propDecidable _
   letI:Decidable (IsUnit s):=Classical.propDecidable _
   by_cases hr:IsUnit r
   · exact Or.inl hr
   by_cases hs:IsUnit s
   · exact Or.inr hs
   · exfalso
     have hrm:r∈m:=(IsLocalRing.mem_maximalIdeal r).mpr hr
     have hsm:s∈m:=(IsLocalRing.mem_maximalIdeal s).mpr hs
     apply hf2
     rw [pow_two, ←hrs]
     exact (m*m).add_mem (Ideal.mul_mem_mul hrm ha) (Ideal.mul_mem_mul hsm hb)
 rcases hunit with hr | hs
 · refine ⟨b,hb,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,b}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       obtain ⟨u,rfl⟩:=hr
       have hfmem:f∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have hbmem:b∈Ideal.span ({f,b}:Set A):=
         Ideal.subset_span (by simp)
       have heq:a=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*s*b:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           a=((↑(u⁻¹):A)*(↑u:A))*a:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*((↑u:A)*a+s*b)-
               (↑(u⁻¹):A)*s*b:=by ring
       rw [heq]
       exact (Ideal.span ({f,b}:Set A)).sub_mem
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,b}:Set A)).mul_mem_left _ hbmem)
     · rw [hx]
       exact Ideal.subset_span (by simp)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
 · refine ⟨a,ha,le_antisymm ?_ ?_⟩
   · change m ≤ Ideal.span {f,a}
     rw [←hspan]
     apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rw [hx]
       exact Ideal.subset_span (by simp)
     · rw [hx]
       obtain ⟨u,rfl⟩:=hs
       have hfmem:f∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have hamem:a∈Ideal.span ({f,a}:Set A):=
         Ideal.subset_span (by simp)
       have heq:b=(↑(u⁻¹):A)*f-(↑(u⁻¹):A)*r*a:=by
         rw [←hrs]
         have hu:(↑(u⁻¹):A)*(↑u:A)=1:=Units.inv_mul u
         calc
           b=((↑(u⁻¹):A)*(↑u:A))*b:=by rw [hu,one_mul]
           _=(↑(u⁻¹):A)*(r*a+(↑u:A)*b)-
               (↑(u⁻¹):A)*r*a:=by ring
       rw [heq]
       exact (Ideal.span ({f,a}:Set A)).sub_mem
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hfmem)
         ((Ideal.span ({f,a}:Set A)).mul_mem_left _ hamem)
   · apply Ideal.span_le.2
     intro x hx
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
     rcases hx with hx | hx
     · rwa [hx]
     · rwa [hx]
theorem quotient_span_singleton_isRegularLocalRing
   (f:A) (hf:f∈maximalIdeal A) (hf2:f∉maximalIdeal A^2)
   (hdim:ringKrullDim A=2)
   (hdimQ:ringKrullDim (A ⧸ Ideal.span {f})=1):
   IsRegularLocalRing (A ⧸ Ideal.span {f}):=by
 obtain ⟨g,hg,hmg⟩:=exists_pair_generator_of_not_mem_sq f hf hf2 hdim
 have hspanProper:Ideal.span ({f}:Set A)≠⊤:=by
   apply ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top
   exact Ideal.span_le.2 (by simpa using hf)
 letI:Nontrivial (A ⧸ Ideal.span {f}):=
   Ideal.Quotient.nontrivial_iff.mpr hspanProper
 letI:IsLocalRing (A ⧸ Ideal.span {f}):=
   IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
     Ideal.Quotient.mk_surjective
 apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
 rw [hdimQ]
 have hmax:maximalIdeal (A ⧸ Ideal.span {f})=
     Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:=by
   rw [←IsLocalRing.map_maximalIdeal_of_surjective
     (Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective,hmg,
     Ideal.map_span]
   simp [Set.image_insert_eq,Set.image_singleton]
 rw [hmax]
 have hle:(Ideal.span {Ideal.Quotient.mk (Ideal.span {f}) g}:
     Ideal (A ⧸ Ideal.span {f})).spanFinrank ≤ 1:=by
   exact (Submodule.spanFinrank_span_le_ncard_of_finite
     (Set.finite_singleton _)).trans (by simp)
 exact_mod_cast hle
end ProximityPrize.SubmissionLower.ContactRegularQuotient6731Research
