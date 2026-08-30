import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.HJ
namespace ProximityPrize.SubmissionLower.ContactIncidence
theorem enlarge_exempt_card_bound
   {q n a i w M:ℕ}
   (hiw:i ≤ w) (hwa:w ≤ a) (han:a ≤ n)
   (hcount:q*(a-i) ≤ (n-i)*M):
   q*(a-w) ≤ (n-w)*M:=by
 by_cases hqM:q ≤ M
 · calc
     q*(a-w) ≤ M*(a-w):=Nat.mul_le_mul_right _ hqM
     _ ≤ M*(n-w):=
       Nat.mul_le_mul_left _ (Nat.sub_le_sub_right han w)
     _=(n-w)*M:=Nat.mul_comm _ _
 · have hMq:M ≤ q:=(Nat.lt_of_not_ge hqM).le
   have ha:a-i=(a-w)+(w-i):=by omega
   have hn:n-i=(n-w)+(w-i):=by omega
   have hcount':
       q*(a-w)+q*(w-i) ≤
         (n-w)*M+(w-i)*M:=by
     simpa only [ha,hn,Nat.mul_add,Nat.add_mul] using hcount
   have hcancel:(w-i)*M ≤ q*(w-i):=by
     calc
       (w-i)*M ≤ (w-i)*q:=Nat.mul_le_mul_left _ hMq
       _=q*(w-i):=Nat.mul_comm _ _
   omega
section FiniteIncidence
variable {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
variable (relation:Seed → Node → Prop)
variable [∀ seed node,Decidable (relation seed node)]
theorem incidence_after_exempt_nodes
   (seeds:Finset Seed) (nodes identities:Finset Node) (a M:ℕ)
   (hidentities:identities ⊆ nodes)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-identities.card) ≤
     (nodes.card-identities.card)*M:=by
 have hremaining (seed:Seed) (hseed:seed∈seeds):
     a-identities.card ≤ ((nodes \ identities).filter (relation seed)).card:=by
   have hsub:(nodes.filter (relation seed)) \ identities ⊆
       (nodes \ identities).filter (relation seed):=by
     intro node hnode
     obtain ⟨hfiltered,hnot⟩:=Finset.mem_sdiff.mp hnode
     obtain ⟨hnodes,hagree⟩:=Finset.mem_filter.mp hfiltered
     exact Finset.mem_filter.mpr
       ⟨Finset.mem_sdiff.mpr ⟨hnodes,hnot⟩,hagree⟩
   calc
     a-identities.card ≤
         (nodes.filter (relation seed)).card-identities.card:=
       Nat.sub_le_sub_right (hagreement seed hseed) identities.card
     _ ≤ ((nodes.filter (relation seed)) \ identities).card:=
       Finset.le_card_sdiff identities (nodes.filter (relation seed))
     _ ≤ ((nodes \ identities).filter (relation seed)).card:=
       Finset.card_le_card hsub
 have hdouble:seeds.card • (a-identities.card) ≤
     (nodes \ identities).card • M:=
   Finset.card_nsmul_le_card_nsmul (R:=ℕ) (r:=relation)
     (s:=seeds) (t:=nodes \ identities) hremaining hfiber
 simpa [nsmul_eq_mul,Finset.card_sdiff_of_subset hidentities] using hdouble
theorem sharp_incidence_bound
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card*(a-w) ≤ (nodes.card-w)*M:=by
 exact enlarge_exempt_card_bound hcard hwa.le han
   (incidence_after_exempt_nodes relation seeds nodes identities a M
     hidentities hagreement hfiber)
theorem card_le_sharp_incidence_quotient
   (seeds:Finset Seed) (nodes identities:Finset Node) (a w M:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a) (han:a ≤ nodes.card)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed => relation seed node)).card ≤ M):
   seeds.card ≤ ((nodes.card-w)*M)/(a-w):=by
 apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hwa)).mpr
 exact sharp_incidence_bound relation seeds nodes identities a w M
   hidentities hcard hwa han hagreement hfiber
end FiniteIncidence
end ProximityPrize.SubmissionLower.ContactIncidence
