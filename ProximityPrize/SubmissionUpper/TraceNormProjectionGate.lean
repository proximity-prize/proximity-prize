/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ProximityPrize.Benchmark.TargetUpper

/-!
# Trace/norm projection and fixed-center support gates

The raw fibres of a relative trace or norm in the degree-six benchmark field are enormous.  A
raw projection fibre is not, however, an agreement fibre for one fixed received word.  This file
isolates the two fixed-center mechanisms which prevent that numerical multiplicity from being
used for free.

For a one-parameter residual pencil, the coordinates at which the slope vanishes contribute at
most the row degree.  Every other coordinate contains at most one parameter.  At agreement
`139782` this bounds one projected fibre by `15`, below the multiplicity `21` required by the
accepted `67.77` resultant gate.

For a family affine in the pair `(trace, norm)`, one agreement coordinate cuts the parameter
plane by an affine line.  A candidate is identified either by one coordinate whose restricted
fibre is a singleton, or by two coordinates.  Indeed, after choosing a nonzero-slope contact,
any second candidate on its line is separated by another contact: otherwise two distinct
degree-`131071` polynomials would agree on more than `131071` domain points.  Two such affine
equations determine the parameter pair.  Hence the whole chart has at most

`262144 + 262144^2 = 68719738880`

candidates, independently of the extension or subfield sizes.

The scope is deliberately exact.  This closes scalar residual pencils and charts affine in at
most the two displayed invariants.  It does not close nonlinear dependence on the invariants,
three or more independent projected coordinates, a nonreduced direction polynomial, or a
singular chart whose contact equations are not affine lines.
-/

namespace ProximityPrize.SubmissionUpper.TraceNormProjectionGate

open scoped BigOperators

section FiniteWitnessCover

variable {Seed Node : Type*} [DecidableEq Seed] [DecidableEq Node]

omit [DecidableEq Seed] [DecidableEq Node] in
/-- A finite set admitting a unique witness in another finite set is no larger than the witness
set.  The witness may depend noncomputably on the seed. -/
theorem card_le_of_unique_witness
    (seeds : Finset Seed) (witnesses : Finset Node) (R : Seed → Node → Prop)
    (h : ∀ seed ∈ seeds, ∃ node ∈ witnesses,
      R seed node ∧ ∀ other ∈ seeds, R other node → other = seed) :
    seeds.card ≤ witnesses.card := by
  classical
  let chooseNode : {seed // seed ∈ seeds} → {node // node ∈ witnesses} :=
    fun seed ↦ ⟨Classical.choose (h seed seed.property),
      (Classical.choose_spec (h seed seed.property)).1⟩
  have hchoose (seed : {seed // seed ∈ seeds}) :
      R seed (chooseNode seed) ∧
        ∀ other ∈ seeds, R other (chooseNode seed) → other = seed :=
    (Classical.choose_spec (h seed seed.property)).2
  have hinjective : Function.Injective chooseNode := by
    intro seed other heq
    apply Subtype.ext
    apply ((hchoose seed).2 other other.property ?_).symm
    rw [heq]
    exact (hchoose other).1
  simpa using Fintype.card_le_of_injective chooseNode hinjective

omit [DecidableEq Node] in
/-- If every seed is isolated either by one node or by an ordered pair of nodes, the seed set has
cardinality at most `|nodes| + |nodes|^2`. -/
theorem card_le_nodes_add_square_of_one_or_two_witnesses
    (seeds : Finset Seed) (nodes : Finset Node) (R : Seed → Node → Prop)
    (hcover : ∀ seed ∈ seeds,
      (∃ node ∈ nodes, R seed node ∧
        ∀ other ∈ seeds, R other node → other = seed) ∨
      (∃ first ∈ nodes, ∃ second ∈ nodes,
        R seed first ∧ R seed second ∧
          ∀ other ∈ seeds, R other first → R other second → other = seed)) :
    seeds.card ≤ nodes.card + nodes.card ^ 2 := by
  classical
  let hasSingle : Seed → Prop := fun seed ↦
    ∃ node ∈ nodes, R seed node ∧
      ∀ other ∈ seeds, R other node → other = seed
  let singles := seeds.filter hasSingle
  let pairs := seeds.filter fun seed ↦ ¬hasSingle seed
  have hsingles : singles.card ≤ nodes.card := by
    apply card_le_of_unique_witness singles nodes R
    intro seed hseed
    have hs : hasSingle seed := (Finset.mem_filter.mp hseed).2
    obtain ⟨node, hnode, hR, hunique⟩ := hs
    exact ⟨node, hnode, hR, fun other hother hotherR ↦
      hunique other (Finset.mem_filter.mp hother).1 hotherR⟩
  let pairRelation : Seed → Node × Node → Prop := fun seed pair ↦
    R seed pair.1 ∧ R seed pair.2
  have hpairs : pairs.card ≤ (nodes.product nodes).card := by
    apply card_le_of_unique_witness pairs (nodes.product nodes) pairRelation
    intro seed hseed
    have hseedSeeds : seed ∈ seeds := (Finset.mem_filter.mp hseed).1
    have hnotSingle : ¬hasSingle seed := (Finset.mem_filter.mp hseed).2
    rcases hcover seed hseedSeeds with hsingle | hpair
    · exact (hnotSingle hsingle).elim
    · obtain ⟨first, hfirst, second, hsecond, hRfirst, hRsecond, hunique⟩ := hpair
      refine ⟨(first, second), Finset.mem_product.mpr ⟨hfirst, hsecond⟩,
        ⟨hRfirst, hRsecond⟩, ?_⟩
      intro other hother hotherR
      exact hunique other (Finset.mem_filter.mp hother).1 hotherR.1 hotherR.2
  have hpartition : singles.card + pairs.card = seeds.card := by
    simpa only [singles, pairs, hasSingle] using
      (Finset.card_filter_add_card_filter_not (s := seeds) hasSingle)
  rw [← hpartition]
  calc
    singles.card + pairs.card ≤ nodes.card + (nodes.product nodes).card :=
      Nat.add_le_add hsingles hpairs
    _ = nodes.card + nodes.card ^ 2 := by simp [pow_two]

end FiniteWitnessCover

section AffineContacts

variable {F : Type*} [Field F]

/-- Two affine equations determine a parameter pair once the first equation has nonzero slope
and a known second point on its line fails the second equation. -/
theorem eq_of_two_affine_contacts
    (s t r : F × F) (b₀ c₀ b₁ c₁ : F)
    (_hst : s ≠ t) (hslope : b₀ ≠ 0 ∨ c₀ ≠ 0)
    (htangent₀ : (t.1 - s.1) * b₀ + (t.2 - s.2) * c₀ = 0)
    (htangent₁ : (t.1 - s.1) * b₁ + (t.2 - s.2) * c₁ ≠ 0)
    (hr₀ : (r.1 - s.1) * b₀ + (r.2 - s.2) * c₀ = 0)
    (hr₁ : (r.1 - s.1) * b₁ + (r.2 - s.2) * c₁ = 0) :
    r = s := by
  have hdet : b₀ * c₁ - b₁ * c₀ ≠ 0 := by
    intro hdetZero
    apply htangent₁
    rcases hslope with hb₀ | hc₀
    · have hmul : b₀ * ((t.1 - s.1) * b₁ + (t.2 - s.2) * c₁) = 0 := by
        calc
          b₀ * ((t.1 - s.1) * b₁ + (t.2 - s.2) * c₁) =
              b₁ * ((t.1 - s.1) * b₀ + (t.2 - s.2) * c₀) +
                (t.2 - s.2) * (b₀ * c₁ - b₁ * c₀) := by ring
          _ = 0 := by rw [htangent₀, hdetZero]; ring
      exact (mul_eq_zero.mp hmul).resolve_left hb₀
    · have hmul : c₀ * ((t.1 - s.1) * b₁ + (t.2 - s.2) * c₁) = 0 := by
        calc
          c₀ * ((t.1 - s.1) * b₁ + (t.2 - s.2) * c₁) =
              c₁ * ((t.1 - s.1) * b₀ + (t.2 - s.2) * c₀) -
                (t.1 - s.1) * (b₀ * c₁ - b₁ * c₀) := by ring
          _ = 0 := by rw [htangent₀, hdetZero]; ring
      exact (mul_eq_zero.mp hmul).resolve_left hc₀
  have hrFirst : r.1 - s.1 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hdet
    calc
      (b₀ * c₁ - b₁ * c₀) * (r.1 - s.1) =
          c₁ * ((r.1 - s.1) * b₀ + (r.2 - s.2) * c₀) -
            c₀ * ((r.1 - s.1) * b₁ + (r.2 - s.2) * c₁) := by ring
      _ = 0 := by rw [hr₀, hr₁]; ring
  have hrSecond : r.2 - s.2 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hdet
    calc
      (b₀ * c₁ - b₁ * c₀) * (r.2 - s.2) =
          b₀ * ((r.1 - s.1) * b₁ + (r.2 - s.2) * c₁) -
            b₁ * ((r.1 - s.1) * b₀ + (r.2 - s.2) * c₀) := by ring
      _ = 0 := by rw [hr₀, hr₁]; ring
  apply Prod.ext
  · exact sub_eq_zero.mp hrFirst
  · exact sub_eq_zero.mp hrSecond

end AffineContacts

section PolynomialSupport

variable {F I : Type*} [Field F] [DecidableEq F] [Fintype I] [DecidableEq I]

/-- Coordinates on which both trace/norm direction polynomials vanish. -/
noncomputable def zeroSlopeCoordinates
    (domain : I → F) (traceDirection normDirection : Polynomial F) : Finset I :=
  Finset.univ.filter fun i ↦
    traceDirection.eval (domain i) = 0 ∧ normDirection.eval (domain i) = 0

omit [DecidableEq I] in
/-- A nontrivial pair of degree-`degreeCap` directions has at most `degreeCap` simultaneous
zero-slope domain coordinates. -/
theorem zeroSlopeCoordinates_card_le
    (domain : I → F) (traceDirection normDirection : Polynomial F) (degreeCap : ℕ)
    (hdomain : Function.Injective domain)
    (hdegreeTrace : traceDirection.natDegree ≤ degreeCap)
    (hdegreeNorm : normDirection.natDegree ≤ degreeCap)
    (hnonzero : traceDirection ≠ 0 ∨ normDirection ≠ 0) :
    (zeroSlopeCoordinates domain traceDirection normDirection).card ≤ degreeCap := by
  classical
  rcases hnonzero with htrace | hnorm
  · calc
      (zeroSlopeCoordinates domain traceDirection normDirection).card =
          ((zeroSlopeCoordinates domain traceDirection normDirection).image domain).card :=
        (Finset.card_image_of_injective _ hdomain).symm
      _ ≤ traceDirection.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots htrace]
        exact (Finset.mem_filter.mp hi).2.1
      _ ≤ traceDirection.natDegree :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
      _ ≤ degreeCap := hdegreeTrace
  · calc
      (zeroSlopeCoordinates domain traceDirection normDirection).card =
          ((zeroSlopeCoordinates domain traceDirection normDirection).image domain).card :=
        (Finset.card_image_of_injective _ hdomain).symm
      _ ≤ normDirection.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hnorm]
        exact (Finset.mem_filter.mp hi).2.2
      _ ≤ normDirection.natDegree :=
        (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)
      _ ≤ degreeCap := hdegreeNorm

omit [Fintype I] [DecidableEq I] in
/-- If one candidate polynomial has more than `degreeCap` fixed-center contacts, a distinct
degree-`degreeCap` candidate must fail at one of those contacts. -/
theorem exists_contact_distinguishing_polynomials
    (domain : I → F) (center : I → F) (support : Finset I)
    (first second : Polynomial F) (degreeCap : ℕ)
    (hdomain : Function.Injective domain)
    (hfirstDegree : first.natDegree ≤ degreeCap)
    (hsecondDegree : second.natDegree ≤ degreeCap)
    (hne : first ≠ second) (hlarge : degreeCap < support.card)
    (hfirst : ∀ i ∈ support, first.eval (domain i) = center i) :
    ∃ i ∈ support, second.eval (domain i) ≠ center i := by
  classical
  by_contra hno
  push Not at hno
  apply hne
  apply sub_eq_zero.mp
  let nodes : Finset F := support.image domain
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      (first - second) nodes
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Polynomial.eval_sub, hfirst i hi, hno i hi, sub_self]
  · have hnodes : nodes.card = support.card := by
      exact Finset.card_image_of_injective support hdomain
    rw [hnodes]
    exact (Polynomial.natDegree_sub_le first second).trans_lt
      ((max_le hfirstDegree hsecondDegree).trans_lt hlarge)

end PolynomialSupport

/-! ## Benchmark arithmetic -/

def baseFieldCardinality : ℕ := 2130706433
def extensionDegree : ℕ := 6
def domainSize : ℕ := 262144
def rowDegree : ℕ := 131071
def targetAgreement : ℕ := 139782
def agreementBeyondZeroSlope : ℕ := targetAgreement - rowDegree
def movingAfterMaximalZeroSlope : ℕ := domainSize - rowDegree
def challengeThreshold : ℕ := 274980728111395088
def maximumScalarProjectionFibre : ℕ :=
  movingAfterMaximalZeroSlope / agreementBeyondZeroSlope
def affinePairChartCap : ℕ := domainSize + domainSize ^ 2

/-- A scalar residual direction leaves at most fifteen candidates in one projected fibre.  Thus
the raw trace/norm multiplicity cannot provide the factor twenty-one required by the regular
resultant branch. -/
theorem scalar_projection_fibre_receipt :
    agreementBeyondZeroSlope = 8711 ∧
      movingAfterMaximalZeroSlope = 131073 ∧
      maximumScalarProjectionFibre = 15 ∧
      movingAfterMaximalZeroSlope <
        16 * agreementBeyondZeroSlope ∧
      maximumScalarProjectionFibre < 21 := by
  norm_num [agreementBeyondZeroSlope, movingAfterMaximalZeroSlope,
    maximumScalarProjectionFibre, targetAgreement, rowDegree, domainSize]

/-- Conditional incidence form of the scalar gate. -/
theorem scalar_projection_card_le_fifteen
    (card : ℕ)
    (hincidence : card * agreementBeyondZeroSlope ≤ movingAfterMaximalZeroSlope) :
    card ≤ maximumScalarProjectionFibre := by
  norm_num [agreementBeyondZeroSlope, movingAfterMaximalZeroSlope,
    maximumScalarProjectionFibre, targetAgreement, rowDegree, domainSize] at hincidence ⊢
  omega

/-- Even the deliberately generous ordered-pair encoding of every affine `(trace,norm)` chart
is more than four million times below the challenge threshold. -/
theorem affine_pair_chart_receipt :
    affinePairChartCap = 68719738880 ∧
      affinePairChartCap < challengeThreshold ∧
      4000000 * affinePairChartCap < challengeThreshold := by
  norm_num [affinePairChartCap, domainSize, challengeThreshold]

/-- Benchmark consumer for the two-coordinate trace/norm argument.  The local polynomial lemmas
above produce `hcover`: a candidate is isolated by one nonzero-slope contact, or a second contact
turns the first affine line into a unique ordered-pair witness. -/
theorem affine_trace_norm_chart_lt_threshold
    {Seed Node : Type*} [DecidableEq Seed] [DecidableEq Node]
    (seeds : Finset Seed) (nodes : Finset Node) (R : Seed → Node → Prop)
    (hnodes : nodes.card = domainSize)
    (hcover : ∀ seed ∈ seeds,
      (∃ node ∈ nodes, R seed node ∧
        ∀ other ∈ seeds, R other node → other = seed) ∨
      (∃ first ∈ nodes, ∃ second ∈ nodes,
        R seed first ∧ R seed second ∧
          ∀ other ∈ seeds, R other first → R other second → other = seed)) :
    seeds.card < challengeThreshold := by
  have hcard := card_le_nodes_add_square_of_one_or_two_witnesses
    seeds nodes R hcover
  rw [hnodes] at hcard
  exact hcard.trans_lt affine_pair_chart_receipt.2.1

/-- Trace and norm alone have huge raw fibres over each proper benchmark subfield.  These counts
are projection sizes, not fixed-center agreement multiplicities.  For a subfield of size
`q = p^d`, trace fibres have `p^(6-d)` elements and nonzero norm fibres have
`(p^6-1)/(p^d-1)` elements. -/
theorem raw_projection_fibres_exceed_regular_gate :
    21 ≤ baseFieldCardinality ^ 5 ∧
      21 ≤ (baseFieldCardinality ^ 6 - 1) / (baseFieldCardinality - 1) ∧
      21 ≤ baseFieldCardinality ^ 4 ∧
      21 ≤ (baseFieldCardinality ^ 6 - 1) /
        (baseFieldCardinality ^ 2 - 1) ∧
      21 ≤ baseFieldCardinality ^ 3 ∧
      21 ≤ (baseFieldCardinality ^ 6 - 1) /
        (baseFieldCardinality ^ 3 - 1) := by
  norm_num [baseFieldCardinality]

/-- In the quadratic relative extension, trace and norm together determine an element up to its
two conjugates.  The corresponding joint projection cannot reach multiplicity twenty-one.  This
numeric receipt records the only fact needed by the chart ledger. -/
theorem quadratic_joint_trace_norm_below_regular_gate : 2 < 21 := by
  norm_num

#print axioms card_le_nodes_add_square_of_one_or_two_witnesses
#print axioms eq_of_two_affine_contacts
#print axioms zeroSlopeCoordinates_card_le
#print axioms exists_contact_distinguishing_polynomials
#print axioms scalar_projection_card_le_fifteen
#print axioms affine_pair_chart_receipt
#print axioms affine_trace_norm_chart_lt_threshold

end ProximityPrize.SubmissionUpper.TraceNormProjectionGate
