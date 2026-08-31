import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.CD
import ProximityPrize.SubmissionLower.K8
import ProximityPrize.SubmissionLower.K9
namespace ProximityPrize.SubmissionLower.RCN178
open scoped Classical BigOperators
open RCN051 RCN068 RCN136
open RCN238 RCN243 RCN065
open RCN231 RCN319 RCN001
open RCN174
open RCN306 RCN176 RCN177
open RCN003 RCN012
open RCN011 RCN009 RCN013
open RCN371
noncomputable section
variable {K Ω:Type} [Field K] [Field Ω]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
theorem rationalMap_joint_support_of_dvd
   (G Q:MvPolynomial (Fin 3) Ω) (cap:ℕ)
   (hdiv:G∣Q) (hQne:Q≠0)
   (hQsupport:∀ d∈Q.support,d 0+d 2 ≤ cap):
   ∀ e∈(rationalMap Ω (Equiv.swap 0 1) G).support,
     e 0+e 1 ≤ cap:=by
 let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
 let g:=rationalMap Ω order G
 let q:=rationalMap Ω order Q
 have hqne:q≠0:=rationalMap_ne_zero Ω order Q hQne
 have hgdvd:g∣q:=map_dvd (rationalMap Ω order) hdiv
 have hqSupport:∀ e∈q.support,e 0+e 1 ≤ cap:=by
   exact original_joint_support_to_rationalMap Ω Q cap hQsupport
 have hqTotal:q.totalDegree ≤ cap:=by
   unfold MvPolynomial.totalDegree
   apply Finset.sup_le
   intro e he
   simpa [Finsupp.sum_fintype,Fin.sum_univ_two] using hqSupport e he
 have hgTotal:g.totalDegree ≤ cap:=
   (MvPolynomial.totalDegree_le_of_dvd_of_isDomain hgdvd hqne).trans hqTotal
 intro e he
 have hweight:=(MvPolynomial.le_totalDegree he).trans hgTotal
 simpa [Finsupp.sum_fintype,Fin.sum_univ_two] using hweight
variable [IsAlgClosed Ω]
variable (φ:Polynomial K →+*Ω)
variable {ι:Type*}
local instance:DecidableEq ι:=Classical.decEq ι
theorem whole_surface_seed_bound_joint_R
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F)
   (hr:0 < G.degreeOf 1)
   (hHproper:¬ G∣surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (p w a e:ℕ) [CharP Ω p] (hw:1 ≤ w) (hchar:w < p)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hGdegree:∀ j:Fin 3,G.degreeOf j < p)
   (hmixedY:∀ i∈nodes,
     coordinateMixedDegree Ω G
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 0 < p)
   (hmixedZ:∀ i∈nodes,
     coordinateMixedDegree Ω G
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 2 < p)
   (hjoint:∀ i∈nodes,
     ¬ G∣agreementPolynomial φ F w (x i) (u₀ i) (u₁ i) →
     JointRProvider G (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) p)
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hagreement:∀ γ∈Γ,
     a ≤ (nodes.filter (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w e)
   (E:DegreeVector)
   (hcap:∀ i∈nodes,
     HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) E):
   Γ.card*(a-w)^2 ≤
     (nodes.card-w)*fiberNumerator nodes.card w a e (degreeVector G) E:=by
 classical
 let P:Ideal (MvPolynomial (Fin 3) Ω):=Ideal.span {G}
 letI:P.IsPrime:=Ideal.isPrime_span_singleton_of_prime hG.prime
 have hFmem:surfaceMap φ F∈P:=Ideal.mem_span_singleton.mpr hdiv
 have hHmem:surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F)∉P:=by
   intro h
   exact hHproper (Ideal.mem_span_singleton.mp h)
 let identities:=identityNodes φ P F nodes x u₀ u₁ w
 have hidentities:identities ⊆ nodes:=identityNodes_subset φ P F nodes x u₀ u₁ w
 have hicard:identities.card ≤ w:=
   identityNodes_card_le_of_r_dependent_principal φ P F hFmem hHmem
     nodes x u₀ u₁ w hw hinj G rfl hr
 apply scaled_sharp_incidence_bound
   (fun γ i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)
   Γ nodes identities a w (fiberNumerator nodes.card w a e (degreeVector G) E)
   hidentities hicard hwa han hagreement
 intro i hi
 obtain ⟨hinode,hnotid⟩:=Finset.mem_sdiff.mp hi
 let T:=agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
 have hproper:¬ G∣T:=by
   intro hd
   apply hnotid
   exact Finset.mem_filter.mpr ⟨hinode,Ideal.mem_span_singleton.mpr hd⟩
 let fiber:=Γ.filter (fun γ => (selected γ).eval (x i)=u₀ i+γ*u₁ i)
 have hsub:fiber ⊆ Γ:=Finset.filter_subset _ _
 have hTpoint:∀ γ∈fiber,MvPolynomial.eval (selectedPoint φ selected γ) T=0:=by
   intro γ hγ
   have hΓ:=hsub hγ
   exact (selected_agreement_zero_iff φ F selected p w hchar γ
     (hdegree γ hΓ) (hsolution γ hΓ) (hregular γ hΓ) (x i) (u₀ i) (u₁ i)).mpr
       (Finset.mem_filter.mp hγ).2
 have hcount:=proper_cut_seed_bound_joint_R φ F G T hG hdiv hproper selected fiber
   nodes x u₀ u₁ hinj p w a e hw hchar hwa han hGdegree
   (hmixedY i hinode) (hmixedZ i hinode) (hjoint i hinode hproper)
   (fun γ hγ => hdegree γ (hsub hγ))
   (fun γ hγ => hsolution γ (hsub hγ))
   (fun γ hγ => hregular γ (hsub hγ))
   (fun γ hγ => hGpoint γ (hsub hγ)) hTpoint
   (fun γ hγ => hagreement γ (hsub hγ))
   (noLargeSelectedPencil_mono selected Γ fiber w e hsub hnoPencil)
   (capAt E) hcap
 have hδ (j:Fin 3):coordinateMixedDegree Ω G T j ≤
     mixed (degreeVector G) E (unitAt j):=
   coordinateMixedDegree_le_caps G T (degreeVector G) E (degreeVector_hasCaps G)
     (hcap i hinode) j
 have hsum:(∑ j,capAt E j*coordinateMixedDegree Ω G T j) ≤
     mixed (degreeVector G) E E:=by
   calc
     _ ≤ ∑ j,capAt E j*mixed (degreeVector G) E (unitAt j):=by
       apply Finset.sum_le_sum
       intro j _
       exact Nat.mul_le_mul_left _ (hδ j)
     _=_:=mixed_cap_sum (degreeVector G) E E
 exact hcount.trans (Nat.add_le_add (Nat.mul_le_mul_left _ hsum)
   (Nat.mul_le_mul_left _ (hδ 2)))
theorem whole_surface_seed_bound_fixed_joint_R
   (F:MvPolynomial (Fin 4) K) (G:MvPolynomial (Fin 3) Ω)
   (hG:Irreducible G) (hdiv:G∣surfaceMap φ F)
   (hr:0 < G.degreeOf 1)
   (hHproper:¬ G∣surfaceMap φ (MvPolynomial.pderiv (2:Fin 4) F))
   (hbox:F∈globalCoefficientBox K weightedCap w seedTotalCap slopeCap)
   (hGcaps:HasCaps G RCN242.surfaceVector)
   (hGjoint:∀ e∈(rationalMap Ω (Equiv.swap 0 1) G).support,
     e 0+e 1 ≤ seedTotalCap)
   (hFseed:seedDegree F ≤ seedTotalCap)
   (hY:F.degreeOf 1 ≤ yCap) (hR:F.degreeOf 2 ≤ slopeCap)
   (hZ:F.degreeOf 3 ≤ seedTotalCap)
   (selected:K → Polynomial K) (Γ:Finset K)
   (nodes:Finset ι) (x u₀ u₁:ι → K) (hinj:Set.InjOn x nodes)
   (hnodes:nodes.card=n) [CharP Ω prime]
   (hdegree:∀ γ∈Γ,(selected γ).natDegree ≤ w)
   (hsolution:∀ γ∈Γ,specialization K (selected γ) γ F=0)
   (hregular:∀ γ∈Γ,MvPolynomial.eval₂Hom (φ.comp Polynomial.C)
     (polynomialPoint (φ.comp Polynomial.C) (selected γ) γ (φ Polynomial.X))
     (MvPolynomial.pderiv (2:Fin 4) F)≠0)
   (hGpoint:∀ γ∈Γ,MvPolynomial.eval (selectedPoint φ selected γ) G=0)
   (hagreement:∀ γ∈Γ,
     agreements ≤ (nodes.filter
       (fun i => (selected γ).eval (x i)=u₀ i+γ*u₁ i)).card)
   (hnoPencil:NoLargeSelectedPencil selected Γ w errors):
   Γ.card*gap^2 ≤ wholeNumerator (degreeVector G):=by
 have hcap (i:ι):
     HasCaps (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) agreementVector:=
   fixed_agreement_caps φ F hbox hY hR hZ (x i) (u₀ i) (u₁ i)
 have hGdegree:∀ j:Fin 3,G.degreeOf j < prime:=
   fun j => (hGcaps j).trans_lt (fixed_surface_caps_below_characteristic j)
 have hmixedY (i:ι):coordinateMixedDegree Ω G
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 0 < prime:=by
   simpa only [coordinateMixedDegree_zero] using
     (fixed_agreement_nonR_characteristic_gates G _ hGcaps (hcap i)).2.1
 have hmixedZ (i:ι):coordinateMixedDegree Ω G
     (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) 2 < prime:=by
   simpa only [coordinateMixedDegree_two] using
     (fixed_agreement_nonR_characteristic_gates G _ hGcaps (hcap i)).2.2
 have hjoint (i:ι)
     (hproper:¬ G∣agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)):
     JointRProvider G
       (agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)) prime:=by
   intro P _ hGmem ht
   let order:Fin 3 ≃ Fin 3:=Equiv.swap 0 1
   let T:=agreementPolynomial φ F w (x i) (u₀ i) (u₁ i)
   have hTne:T≠0:=by
     intro hzero
     apply hproper
     change G∣T
     rw [hzero]
     exact dvd_zero G
   have hG0:G.degreeOf 0 ≤ 25:=by
     simpa [RCN242.surfaceVector,capAt,yCap,weightedCap,
       RCN051.multiplicity,agreements,w] using hGcaps 0
   have hG2:G.degreeOf 2 ≤ 176:=by
     simpa [RCN242.surfaceVector,capAt,seedTotalCap] using hGcaps 2
   have hT0:T.degreeOf 0 ≤ 6422480:=by
     have h:=hcap i 0
     change T.degreeOf 0 ≤ capAt agreementVector 0 at h
     norm_num [capAt,agreementVector,yCap,weightedCap,
       RCN051.multiplicity,agreements,w] at h
     exact h
   have hGouter:(planeMap Ω order G).natDegree ≤ 25:=by
     exact (planeMap_natDegree_le Ω order G).trans (by simpa [order] using hG0)
   have hTouter:(planeMap Ω order T).natDegree ≤ 6422480:=by
     exact (planeMap_natDegree_le Ω order T).trans (by simpa [order] using hT0)
   have hGsupport:∀ d∈(rationalMap Ω order G).support,
       d 0+d 1 ≤ 176:=by
     simpa [order,seedTotalCap] using hGjoint
   have hTsupport:∀ d∈(rationalMap Ω order T).support,
       d 0+d 1 ≤ 46136993:=by
     have h:=surfaceMap_agreement_joint_seed_cap φ F seedTotalCap w hFseed
       (fun j => (j.factorial:K)⁻¹) (x i) (u₀ i) (u₁ i)
     norm_num [seedTotalCap,w] at h
     simpa [order,T,agreementPolynomial] using
       (original_joint_support_to_rationalMap Ω T 46136993 (by
         simpa [T,agreementPolynomial,w] using h))
   have hGswapOuter:
       (planeMap Ω (swapOtherOrder order) G).natDegree ≤ 176:=by
     exact (planeMap_natDegree_le Ω (swapOtherOrder order) G).trans
       (by simpa [order,Equiv.swap_apply_def] using hG2)
   have hTswapInner:Polynomial.Bivariate.degreeX
       (planeMap Ω (swapOtherOrder order) T) ≤ 6422529:=by
     have h:=(planeMap_degreeX_le Ω (swapOtherOrder order) T).trans hT0
     exact h.trans (by norm_num)
   exact jointOrderCertificate_of_projection_data Ω order P G T prime
     25 6422480 176 46136993 2123219305 176 6422529 hG hGmem ht hTne
     hGouter hTouter hGsupport hTsupport hGswapOuter hTswapInner
     (by norm_num [prime]) (by norm_num [prime])
     (by simpa [prime] using agreement_6464_sharpY_trapezoid_cap_below_characteristic)
     (by simpa [prime] using swapped_6464_sharpY_cap_below_characteristic)
     agreement_6464_sharpY_trapezoid_budget
 have hcount:=whole_surface_seed_bound_joint_R φ F G hG hdiv hr hHproper
   selected Γ nodes x u₀ u₁ hinj prime w agreements errors
   (by norm_num [w]) (by norm_num [w,prime]) (by norm_num [w,agreements])
   (by rw [hnodes];norm_num [agreements,n]) hGdegree
   (fun i _ => hmixedY i) (fun i _ => hmixedZ i)
   (fun i _ hproper => hjoint i hproper)
   hdegree hsolution hregular hGpoint hagreement hnoPencil agreementVector
   (fun i _ => hcap i)
 calc
   Γ.card*gap^2=Γ.card*(agreements-w)^2:=rfl
   _ ≤ (nodes.card-w)*fiberNumerator nodes.card w agreements errors
       (degreeVector G) agreementVector:=hcount
   _=wholeNumerator (degreeVector G):=by
     rw [hnodes]
     unfold fiberNumerator wholeNumerator gap
     ring
end
end ProximityPrize.SubmissionLower.RCN178
