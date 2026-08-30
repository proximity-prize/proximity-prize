import ProximityPrize.SubmissionLower.BL
import ProximityPrize.SubmissionLower.B
namespace ProximityPrize.SubmissionLower.RCN087
open scoped Classical BigOperators
open RCN136 RCN231 RCN319
open RCN238 RCN065 RCN243
open RCN264 RCN159
open RCN095 RCN275
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 25000
variable {K Ω I:Type} [Field K] [Field Ω] [IsAlgClosed Ω]
variable {φ:Polynomial K →+*Ω} {Γ:Finset K} {x:I → K}
variable {p e:ℕ} [CharP Ω p]
local instance:DecidableEq K:=Classical.decEq K
local instance:DecidableEq Ω:=Classical.decEq Ω
local instance:DecidableEq I:=Classical.decEq I
def IdentityCurveCountProvider
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support) (identityDegree:ℕ):Prop:=
 ∀ i∈S.nodes,
   let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
   (hproper:¬S.G∣T) →
   let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
   ∃ cost:RegularComponent Ω S.G T (regularitySurface φ S.F)→ℕ,
     (∀ C,(componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
       (selectedPoint φ S.selected) C).card≤(e+1)*cost C)∧
     (∑ C,cost C) ≤ identityDegree
private theorem proper_node_fiber_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (identityDegree:ℕ) (hprovider:IdentityCurveCountProvider S identityDegree)
   (i:I) (hi:i∈S.nodes)
   (hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)):
   (Γ.filter (fun γ=>S.Agrees γ i)).card≤(e+1)*identityDegree:=by
 let T:=agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i)
 let Gi:=Γ.filter (fun γ=>S.Agrees γ i)
 obtain ⟨cost,hcomponent,hsum⟩:=hprovider i hi hproper
 have hsub:Gi⊆Γ:=Finset.filter_subset _ _
 have hGpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) S.G=0:=by
   intro γ hγ;exact S.on_component γ (hsub hγ)
 have hTpoint:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ) T=0:=by
   intro γ hγ
   exact (selected_agreement_zero_iff φ S.F S.selected p w S.characteristic_bound γ
     (S.degree_le γ (hsub hγ)) (S.solution γ (hsub hγ))
     (S.regular γ (hsub hγ)) (x i) (S.u0 i) (S.u1 i)).mpr
     (Finset.mem_filter.mp hγ).2
 have hHp:∀ γ∈Gi,MvPolynomial.eval (selectedPoint φ S.selected γ)
     (regularitySurface φ S.F)≠0:=by
   intro γ hγ
   change MvPolynomial.eval (selectedPoint φ S.selected γ)
     (surfaceMap φ (MvPolynomial.pderiv 2 S.F))≠0
   rw [selectedPoint_evaluation]
   exact S.regular γ (hsub hγ)
 calc
   Gi.card≤∑ C:RegularComponent Ω S.G T (regularitySurface φ S.F),
       (componentSeeds Ω S.G T (regularitySurface φ S.F) Gi
         (selectedPoint φ S.selected) C).card:=
     card_le_sum_componentSeeds Ω _ _ _ Gi _ hGpoint hTpoint hHp
   _≤∑ C,(e+1)*cost C:=Finset.sum_le_sum fun C _=>hcomponent C
   _=(e+1)*(∑ C,cost C):=by rw [Finset.mul_sum]
   _≤(e+1)*identityDegree:=Nat.mul_le_mul_left _ hsum
theorem identity_surface_seed_bound
   {flag:FlagDegree} {w:ℕ} {support:ResidualSupportParameters}
   (S:ResidualStage φ Γ x p e flag w support)
   (a identityDegree:ℕ)
   (hprovider:IdentityCurveCountProvider S identityDegree)
   (hagreement:∀ γ∈Γ,a≤(S.agreementFiber γ).card)
   (hwa:w < a) (han:a ≤ S.nodes.card) (hdegreePos:1 ≤ identityDegree):
   Γ.card*(a-w)≤(S.nodes.card-w)*(e+1)*identityDegree:=by
 classical
 letI:S.componentIdeal.IsPrime:=S.componentIdeal_isPrime
 let relation:K→I→Prop:=fun γ i=>S.Agrees γ i
 let identities:=S.identities
 by_cases hI:identities.card ≤ w
 · have hfiber:∀ i∈S.nodes\identities,
       (Γ.filter (fun γ=>relation γ i)).card≤(e+1)*identityDegree:=by
     intro i hi
     obtain ⟨hiNode,hiNot⟩:=Finset.mem_sdiff.mp hi
     have hproper:¬S.G∣agreementPolynomial φ S.F w (x i) (S.u0 i) (S.u1 i):=by
       intro hd
       exact hiNot (Finset.mem_filter.mpr ⟨hiNode,Ideal.mem_span_singleton.mpr hd⟩)
     exact proper_node_fiber_bound S identityDegree hprovider i hiNode hproper
   simpa only [mul_assoc] using RCN173.sharp_incidence_bound relation Γ S.nodes
     identities a w ((e+1)*identityDegree)
     (identityNodes_subset φ S.componentIdeal S.F S.nodes x S.u0 S.u1 w)
     hI hwa han hagreement hfiber
 · have hi:w < identities.card:=Nat.lt_of_not_ge hI
   have hvalues:∀ (t:{γ:K//γ∈Γ}) i,i∈identities→
       (S.selected t.1).eval (x i)=S.u0 i+t.1*S.u1 i:=by
     intro t
     exact selected_agrees_on_identity_nodes φ S.componentIdeal S.F S.nodes x S.u0 S.u1
       p w S.characteristic_bound (S.selected t.1) t.1 (S.degree_le t.1 t.2)
       (S.solution t.1 t.2) (S.regular t.1 t.2) (S.selected_point_ideal t.2)
   obtain ⟨P0,P1,h0,h1,_,hpencil⟩:=exists_common_pencil_of_many_identities
     φ S.componentIdeal S.F S.surface_mem_componentIdeal S.regularity_not_mem_componentIdeal
     S.nodes x S.u0 S.u1 w S.x_injective hi
     (fun t:{γ:K//γ∈Γ}=>t.1) (fun t=>S.selected t.1)
     (fun t=>S.degree_le t.1 t.2) hvalues
   have hsmall:Γ.card ≤ e+1:=by
     have hf:Γ.filter (fun γ=>S.selected γ=P0+Polynomial.C γ*P1)=Γ:=
       Finset.filter_eq_self.mpr (fun γ hγ=>hpencil ⟨γ,hγ⟩)
     simpa only [hf] using S.no_large_pencil P0 P1 h0 h1
   calc
     Γ.card*(a-w)≤(e+1)*(a-w):=Nat.mul_le_mul_right _ hsmall
     _≤(e+1)*(S.nodes.card-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _≤(S.nodes.card-w)*(e+1)*identityDegree:=by
       have h:=Nat.mul_le_mul_left ((S.nodes.card-w)*(e+1)) hdegreePos
       simpa [mul_assoc,mul_comm,mul_left_comm] using h
end
end ProximityPrize.SubmissionLower.RCN087
