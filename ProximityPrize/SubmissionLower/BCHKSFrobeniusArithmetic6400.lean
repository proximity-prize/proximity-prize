import ProximityPrize.SubmissionLower.BCHKSParameters6400

/-!
# Arithmetic ledger for the two-Frobenius score-64 pivot

This file records only the exact integer inequalities behind the new
interleaved-decoding route.  It does not assert the outstanding algebraic
matrix-space theorem.

For an error locator of degree `t`, put `R = n-k = 131072`.  In the active
range `t > R/2`, one syndrome block has `R-t` independent rows and the second
Frobenius block need supply only `2*t-R` further rows.  At the endpoint
`t = 76780`, a nonzero decoding minor therefore has degree at most

`(R-t) + p*(2*t-R) = 47915326319596`

in the challenge, where `p = 2130706433` is the KoalaBear base-field size.
-/

namespace ProximityPrize.SubmissionLower

def bchksBaseFieldCard6400 : Nat := 2130706433
def bchksRedundancy6400 : Nat := 131072
def bchksFrobeniusFirstRows6400 : Nat := 54292
def bchksFrobeniusSecondRows6400 : Nat := 22488
def bchksFrobeniusMinorDegree6400 : Nat := 47915326319596
def bchksFrobeniusLargeErrorClass6400 : Nat := 17497214803141977
def bchksFrobeniusResidualErrors6400 : Nat := 510
def bchksFrobeniusQuadraticLineClass6400 : Nat := 8211932
def bchksFrobeniusLineMinorDegree6400 : Nat := 76780

lemma bchks_frobenius_endpoint_dimensions_6400 :
    bchksRedundancy6400 - bchksErrors6400 =
        bchksFrobeniusFirstRows6400 ∧
      2 * bchksErrors6400 - bchksRedundancy6400 =
        bchksFrobeniusSecondRows6400 := by
  norm_num [bchksRedundancy6400, bchksErrors6400,
    bchksFrobeniusFirstRows6400, bchksFrobeniusSecondRows6400]

lemma bchks_frobenius_minor_degree_6400 :
    bchksFrobeniusFirstRows6400 +
        bchksBaseFieldCard6400 * bchksFrobeniusSecondRows6400 =
      bchksFrobeniusMinorDegree6400 := by
  norm_num [bchksFrobeniusFirstRows6400, bchksBaseFieldCard6400,
    bchksFrobeniusSecondRows6400, bchksFrobeniusMinorDegree6400]

/-- After reserving the entire accepted `63.99` numerator, one of the ten
remaining exact error counts has at least this many challenges. -/
lemma bchks_frobenius_large_error_class_6400 :
    bchksNumerator6400 + 1 - bchksNumerator6399 >
      10 * (bchksFrobeniusLargeErrorClass6400 - 1) := by
  norm_num [bchksNumerator6400, bchksNumerator6399,
    bchksFrobeniusLargeErrorClass6400]

lemma bchks_frobenius_large_class_exceeds_minor_6400 :
    bchksFrobeniusMinorDegree6400 <
      bchksFrobeniusLargeErrorClass6400 := by
  norm_num [bchksFrobeniusMinorDegree6400,
    bchksFrobeniusLargeErrorClass6400]

/-- If 511 non-common error roots remained in the full-rank chart, their
incidence average would force another locator evaluation numerator to have
more roots than its degree.  Thus at most 510 can remain.  The length term
`185373` is the worst case among error counts `76771,...,76780`. -/
lemma bchks_frobenius_residual_root_incidence_6400 :
    (bchksFrobeniusResidualErrors6400 + 1) *
        (bchksFrobeniusLargeErrorClass6400 -
          bchksFrobeniusMinorDegree6400) >
      bchksFrobeniusMinorDegree6400 *
        (185373 + bchksFrobeniusResidualErrors6400 + 1) := by
  norm_num [bchksFrobeniusResidualErrors6400,
    bchksFrobeniusLargeErrorClass6400,
    bchksFrobeniusMinorDegree6400]

/-- Direct form for `many_zero_obstructions_of_many_large_fibers`: among the
nonvanishing-minor challenges it forces at least `76270 = 76780 - 510`
coordinate locator numerators to vanish identically. -/
lemma bchks_frobenius_common_error_core_6400 :
    (262144 - 76780 - 76269) *
        (bchksFrobeniusLargeErrorClass6400 -
          bchksFrobeniusMinorDegree6400) >
      (262144 - 76269) * bchksFrobeniusMinorDegree6400 := by
  norm_num [bchksFrobeniusLargeErrorClass6400,
    bchksFrobeniusMinorDegree6400]

/-- After puncturing the common error core, three endpoint witnesses still
share more than `k-1` agreement coordinates. -/
lemma bchks_frobenius_triple_root_margin_6400 :
    131071 <
      262144 - bchksErrors6400 -
        2 * bchksFrobeniusResidualErrors6400 := by
  norm_num [bchksErrors6400, bchksFrobeniusResidualErrors6400]

/-- A rank-deficient two-Frobenius key matrix yields two multiplier
polynomials of degree below `22488`; the resulting exact transformed word has
degree below `153559` and hence `108585` parity constraints. -/
lemma bchks_frobenius_singular_transform_dimensions_6400 :
    2 * bchksFrobeniusSecondRows6400 = 44976 ∧
      131072 + bchksFrobeniusSecondRows6400 - 1 = 153559 ∧
      262144 - 153559 = 108585 := by
  norm_num [bchksFrobeniusSecondRows6400]

/-- Because `22488 < p`, the transformed determinant has separated base-`p`
exponents and degree far below the large exact-error class. -/
lemma bchks_frobenius_singular_determinant_margin_6400 :
    bchksFrobeniusSecondRows6400 *
        (bchksBaseFieldCard6400 + 1) <
      bchksFrobeniusLargeErrorClass6400 := by
  norm_num [bchksFrobeniusSecondRows6400,
    bchksBaseFieldCard6400, bchksFrobeniusLargeErrorClass6400]

/-- The second-block size is exactly the integer Johnson intersection scale:
`floor(t^2/n) = 22488`.  The nonzero remainder is useful when averaging
pairwise intersections of exact error supports. -/
lemma bchks_frobenius_johnson_remainder_6400 :
    bchksErrors6400 ^ 2 =
      262144 * bchksFrobeniusSecondRows6400 + 74128 := by
  norm_num [bchksErrors6400, bchksFrobeniusSecondRows6400]

/-- A common-denominator or two-compression identity of multiplier degree
below `2*h` has 9,316 degrees of root-count margin on every score-64
agreement set.  This is the same integer surplus seen by the order-five
incidence matrix. -/
lemma bchks_frobenius_rational_identity_margin_6400 :
    131072 + 2 * bchksFrobeniusSecondRows6400 + 9316 =
      262144 - bchksErrors6400 := by
  norm_num [bchksFrobeniusSecondRows6400, bchksErrors6400]

/-- The naive two-witness argument is exactly tight: the guaranteed common
agreements plus every possible root of two degree-`<h` multipliers reaches
the largest possible degree, but does not exceed it.  A structural saving,
not another relaxed inequality, is therefore required. -/
lemma bchks_frobenius_pair_boundary_6400 :
    (262144 - 2 * bchksErrors6400) +
        2 * (bchksFrobeniusSecondRows6400 - 1) =
      131072 + bchksFrobeniusSecondRows6400 - 2 := by
  norm_num [bchksErrors6400, bchksFrobeniusSecondRows6400]

/-- Three full two-row Frobenius envelopes already exceed the transformed
tail space by 26,343 dimensions.  Iterating the sextic Frobenius therefore
creates unavoidable higher-order compression relations. -/
lemma bchks_frobenius_three_envelope_excess_6400 :
    3 * (2 * bchksFrobeniusSecondRows6400) = 108585 + 26343 := by
  norm_num [bchksFrobeniusSecondRows6400]

/-- Once a singular Frobenius pencil has descended to a pair of ordinary
Reed--Solomon words, the existing finite Johnson list bound is more than
enough: even after discarding every zero of the decoding minor, some one of
the at most `300000` codeword pairs owns more than `76780` challenges. -/
lemma bchks_frobenius_descended_list_pigeonhole_6400 :
    bchksListBound6400 * (bchksErrors6400 + 1) <
      bchksFrobeniusLargeErrorClass6400 -
        bchksFrobeniusMinorDegree6400 := by
  norm_num [bchksListBound6400, bchksErrors6400,
    bchksFrobeniusLargeErrorClass6400,
    bchksFrobeniusMinorDegree6400]

/-- If the large singular class is contained in an affine copy of the
quadratic subfield, partitioning that copy into its base-field lines leaves
one line of at least this size. -/
lemma bchks_frobenius_quadratic_line_class_6400 :
    bchksBaseFieldCard6400 *
        (bchksFrobeniusQuadraticLineClass6400 - 1) <
      bchksFrobeniusLargeErrorClass6400 := by
  norm_num [bchksBaseFieldCard6400,
    bchksFrobeniusQuadraticLineClass6400,
    bchksFrobeniusLargeErrorClass6400]

/-- On a base-field affine challenge line every Frobenius conjugate is affine
in the line parameter.  Consequently a full-rank locator minor has ordinary
degree only the total number of selected rows, namely the error count. -/
lemma bchks_frobenius_line_minor_degree_6400 :
    bchksFrobeniusFirstRows6400 +
        bchksFrobeniusSecondRows6400 =
      bchksFrobeniusLineMinorDegree6400 := by
  norm_num [bchksFrobeniusFirstRows6400,
    bchksFrobeniusSecondRows6400,
    bchksFrobeniusLineMinorDegree6400]

/-- After discarding all roots of a nonzero line-chart minor, transposed
incidence forces at least `76780` coordinate locator numerators to vanish
identically.  Since an endpoint locator has exactly `76780` roots, its whole
error support is common along the chart. -/
lemma bchks_frobenius_line_full_error_core_6400 :
    (262144 - bchksErrors6400 - (bchksErrors6400 - 1)) *
        (bchksFrobeniusQuadraticLineClass6400 -
          bchksFrobeniusLineMinorDegree6400) >
      (262144 - (bchksErrors6400 - 1)) *
        bchksFrobeniusLineMinorDegree6400 := by
  norm_num [bchksErrors6400,
    bchksFrobeniusQuadraticLineClass6400,
    bchksFrobeniusLineMinorDegree6400]

/-- Exact endpoint for the deterministic syndrome-witness rank reduction of
Yuan--Zhu.  Starting with the least possible score-64 challenge population,
32 successive rank drops (from rank at most 34 down to rank two) still retain
strictly more than `e+1` witnesses. -/
lemma bchks_witness_rank_34_margin_6400 :
    (bchksNumerator6400 + 1) * (131073 - bchksErrors6400) ^ 32 >
      (bchksErrors6400 + 1) * 131073 ^ 32 := by
  norm_num [bchksNumerator6400, bchksErrors6400]

end ProximityPrize.SubmissionLower
