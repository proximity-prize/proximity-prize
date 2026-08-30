import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.BX
import ProximityPrize.SubmissionLower.H
namespace ProximityPrize.SubmissionLower.RCN216
open RCN173
open RCN213
theorem stratified_incidence_bound
   {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
   (relation:Seed → Node → Prop) [∀ seed node,Decidable (relation seed node)]
   (seeds:Finset Seed) (nodes identities:Finset Node)
   (a w degreeCost unitCost U V:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed↦relation seed node)).card ≤
       (w-identities.card)*degreeCost+unitCost)
   (hdegree:
     (nodes.card-identities.card)*(a-w)*(w-identities.card) ≤
       U*(a-identities.card))
   (hunit:
     (nodes.card-identities.card)*(a-w) ≤
       V*(a-identities.card)):
   seeds.card*(a-w) ≤ U*degreeCost+V*unitCost:=by
 have hraw:=incidence_after_exempt_nodes relation seeds nodes identities a
   ((w-identities.card)*degreeCost+unitCost)
   hidentities hagreement hfiber
 exact stratified_incidence_linear seeds.card nodes.card a w identities.card
   degreeCost unitCost U V hcard hwa hraw hdegree hunit
theorem scaled_stratified_incidence_bound
   {Seed Node:Type*} [DecidableEq Seed] [DecidableEq Node]
   (relation:Seed → Node → Prop) [∀ seed node,Decidable (relation seed node)]
   (seeds:Finset Seed) (nodes identities:Finset Node)
   (a w degreeCost unitCost U V:ℕ)
   (hidentities:identities ⊆ nodes) (hcard:identities.card ≤ w)
   (hwa:w < a)
   (hagreement:∀ seed∈seeds,
     a ≤ (nodes.filter (relation seed)).card)
   (hfiber:∀ node∈nodes \ identities,
     (seeds.filter (fun seed↦relation seed node)).card*(a-w) ≤
       (w-identities.card)*degreeCost+unitCost)
   (hdegree:
     (nodes.card-identities.card)*(a-w)*(w-identities.card) ≤
       U*(a-identities.card))
   (hunit:
     (nodes.card-identities.card)*(a-w) ≤
       V*(a-identities.card)):
   seeds.card*(a-w)^2 ≤ U*degreeCost+V*unitCost:=by
 let geometricCost:=(w-identities.card)*degreeCost+unitCost
 have hgap:0 < a-w:=Nat.sub_pos_of_lt hwa
 have hfiberDiv:∀ node∈nodes \ identities,
     (seeds.filter (fun seed↦relation seed node)).card ≤
       geometricCost/(a-w):=by
   intro node hnode
   exact (Nat.le_div_iff_mul_le hgap).mpr (hfiber node hnode)
 have hraw:=incidence_after_exempt_nodes relation seeds nodes identities a
   (geometricCost/(a-w)) hidentities hagreement hfiberDiv
 have hrawScaled:
     (seeds.card*(a-w))*(a-identities.card) ≤
       (nodes.card-identities.card)*
         ((w-identities.card)*degreeCost+unitCost):=by
   calc
     (seeds.card*(a-w))*(a-identities.card)=
         (seeds.card*(a-identities.card))*(a-w):=by ring
     _ ≤ ((nodes.card-identities.card)*
         (geometricCost/(a-w)))*(a-w):=
       Nat.mul_le_mul_right (a-w) hraw
     _=(nodes.card-identities.card)*
         ((geometricCost/(a-w))*(a-w)):=by ring
     _ ≤ (nodes.card-identities.card)*geometricCost:=
       Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
     _=(nodes.card-identities.card)*
         ((w-identities.card)*degreeCost+unitCost):=rfl
 have hcompressed:=stratified_incidence_linear
   (seeds.card*(a-w)) nodes.card a w identities.card
   degreeCost unitCost U V hcard hwa hrawScaled hdegree hunit
 calc
   seeds.card*(a-w)^2=(seeds.card*(a-w))*(a-w):=by ring
   _ ≤ U*degreeCost+V*unitCost:=hcompressed
end ProximityPrize.SubmissionLower.RCN216
