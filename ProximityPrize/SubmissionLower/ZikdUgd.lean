import ProximityPrize.SubmissionLower.ZkoLWnc
import ProximityPrize.SubmissionLower.ZpWezjb
set_option Elab.async false
set_option autoImplicit true
namespace qIQBiva
noncomputable section
open MvPolynomial P6_6_7 qAzl5me qCj6p1d
open aR (af Shape)
open dN (GeoJets bC AX kC oA)
open Dr (ccl aQG)
open rW (dimension Yg)
open WI (agr)
open private aM6 from ProximityPrize.SubmissionLower.Z3EWiUc
private theorem representative_cut {g:af 4} {S P:Ideal GeoJets} {D:GeoJets}
    (hm:MemberCurve g S P) (hr :sigma g∉P)
    (he :Represents g (bC (memberTest g)) D) :
    D∉S∧(S ⊔ Ideal.span {D}).IsMinimalPrime P:= by
  obtain ⟨e,he⟩:=he
  have hspan:AX S (memberTest g)≤S ⊔ Ideal.span {D} :=
    sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (by
      rw [he]
      exact (S ⊔ Ideal.span {D}).mul_mem_left _
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self D))))
  have hp:=hm.minimal
  refine ⟨fun h=>hm.proper (he.symm ▸ S.mul_mem_left _ h),⟨⟨hp.isPrime,?_⟩,?_⟩⟩
  · apply sup_le (le_sup_left.trans hp.le)
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have hraw:=hp.le
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (bC (memberTest g))))
    rw [he] at hraw
    exact (hp.isPrime.mem_or_mem hraw).resolve_left (fun h=>hr (hp.isPrime.mem_of_pow_mem e h))
  · exact fun Q hQ hQP=>hp.2 ⟨hQ.1,hspan.trans hQ.2⟩ hQP
private theorem paid_le {R G ell} (b:Branch R G ell) :
    b.weight≤Yg (kC R G) b.aI:= by
  have hc: (Yg (kC R G) b.aI:ℕ∞) =
      oA (kC R G) b.aI b.base.isPrime := by
    simp only [Yg,dite_eq_left b.base.isPrime]
    exact ENat.natCast_toNat (ccl b.base).2
  have hp:=b.gH
  rw [← hc] at hp
  exact ENat.natCast_le_natCast.mp hp
private theorem fiber_bound {R G ell} {p:Shape} {z :Ideal GeoJets}
    (hz : (kC R G).IsMinimalPrime z) (hzdim:dimension z=2)
    (V:Finset (Branch R G ell)) (hs : ∀ b∈V,b.aI=z)
    (hg:SameChart V) (hm : ∀ b∈V,Nonempty (Member4 b.g p)) :
    ∑ b∈V,((b.weight*b.extra :ℕ) :ℚ) ≤
      ((memberBox p).b:ℚ)*((Yg (kC R G) z :ℚ)*affineDegree z) := by
  classical
  let w:=Yg (kC R G) z
  by_cases hV:V.Nonempty
  · obtain ⟨b₀,hb₀⟩:=hV
    let M:=(hm b₀ hb₀).some
    let D:=M.polynomial
    let _:=hz.isPrime
    have hD:D.totalDegree≤(memberBox p).b:= by
      refine Finset.sup_le fun m hm => ?_
      rw [Finsupp.sum_fintype _ _ (fun _=>rfl)]
      exact (M.fits m hm).1
    have hcurve (b:Branch R G ell) (hb:b∈V) :
        D∉z∧(z ⊔ Ideal.span {D}).IsMinimalPrime b.curve := by
      have hrep:Represents b.g (bC (memberTest b.g)) D:= by
        rw [hg b hb b₀ hb₀ ((hs b hb).trans (hs b₀ hb₀).symm)]
        exact M.aEA
      simpa only [hs b hb] using representative_cut b.member b.regular hrep
    have hproper :=(hcurve b₀ hb₀).1
    have hinj:Set.InjOn Branch.curve (V:Set (Branch R G ell)) := by
      intro b hb c hc he
      have hbc:=(hs b hb).trans (hs c hc).symm
      exact Branch.b1G hbc (hg b hb c hc hbc) he
    calc
      _ ≤ ∑ b∈V,(w:ℚ)*affineDegree b.curve := by
        apply Finset.sum_le_sum
        intro b hb
        have hdim:=principalCut_natDegree_affineHilbertPolynomial_add_one hproper (hcurve b hb).2
        change (affineHilbertPolynomial z).natDegree=2 at hzdim
        obtain ⟨d,hd,he⟩:=aM6 b.curve b.member.minimal.isPrime (by omega)
        have hw:=paid_le b
        rw [hs b hb] at hw
        have hx :b.extra≤1 := by unfold Branch.extra; split <;> decide
        have hpaid :b.weight*b.extra≤w :=
          (Nat.mul_le_mul_left b.weight hx).trans (by rwa [Nat.mul_one])
        rw [he]
        exact (by exact_mod_cast hpaid : ((b.weight*b.extra :ℕ) :ℚ)≤(w:ℚ)).trans
          (le_mul_of_one_le_right (by positivity) (by exact_mod_cast Nat.succ_le_of_lt hd))
      _=(w:ℚ) * ∑ P∈V.image Branch.curve,affineDegree P:= by
        rw [Finset.mul_sum,Finset.sum_image hinj]
      _≤(w:ℚ)*(((memberBox p).b:ℚ)*affineDegree z) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun P _ _=>affineDegree_nonneg P)).trans
          (principalCut_sum_affineDegree_minimalPrimes_le hproper hD)
        intro P hP
        obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hP
        exact Ideal.mem_minimalPrimesFinset.mpr (hcurve b hb).2
      _ = _:= by change (w:ℚ)*(_ *_)= _ *((w:ℚ)*_); ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp hV,Finset.sum_empty]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (affineDegree_nonneg z))
theorem proof :qCj6p1d.c6:= by
  classical
  intro C R G ell cs h F
  let J:=kC R G
  let p:=chartBody C R cs
  let d:=(memberBox p).b
  change SameChart F→(∀ b∈F,Nonempty (Member4 b.g p)) →
    (additiveCost F:ℤ)≤((firstSlot C R cs).b:ℤ)*(cutterBody C ell).b*d
  intro hg hm
  have hR:=agr h.factor.1.ne_zero
  have hrel :=lB.amo R G h.factor.1 h.proper
  have hq: (additiveCost F:ℚ)≤((firstSlot C R cs).b:ℚ)*(cutterBody C ell).b*d:= by
    unfold additiveCost
    push_cast only [Nat.cast_sum]
    calc
      _ = ∑ z∈J.minimalPrimesFinset,∑ b∈F.filter (fun b=>b.aI=z),
          ((b.weight*b.extra :ℕ) :ℚ) :=
        (Finset.sum_fiberwise_of_maps_to
          (fun b _=>Ideal.mem_minimalPrimesFinset.mpr b.base) _).symm
      _ ≤ ∑ z∈J.minimalPrimesFinset,
          (d:ℚ)*((Yg J z :ℚ)*affineDegree z) := by
        apply Finset.sum_le_sum
        intro z hz
        have hz' := Ideal.mem_minimalPrimesFinset.mp hz
        exact fiber_bound hz' (aQG hR hrel hz') _
          (fun b hb=>(Finset.mem_filter.mp hb).2)
          (fun b hb c hc=>hg b (Finset.mem_filter.mp hb).1 c (Finset.mem_filter.mp hc).1)
          (fun b hb=>hm b (Finset.mem_filter.mp hb).1)
      _≤(d:ℚ)*(((firstSlot C R cs).b:ℚ)*(cutterBody C ell).b) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (qnODzma.cycle_budget h) (by positivity)
      _ = _:= by ring
  exact_mod_cast hq
end
end qIQBiva
