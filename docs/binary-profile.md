# Binary profile provenance and release contract

The benchmark uses ArkLib's existing Toy IOP and IRS extractor certificate. The original lower/upper score definitions are retained for the binary profile; the 128-bit combination-round threshold is separate from the spot-check centibit score.

## Source pins

- ArkLib main: `34a834c61c859cc04205f5f43fd237cda8fb0da4`, verified against the remote main on 2026-09-26. This is newer than the latest tagged release, `v4.34.0` (`fa14552d40e793f2ea26e65c440306aae0c08a26`), and includes the subsequent merged proofs. Lean 4.34.0 and the resolved dependencies are locked in `lake-manifest.json`.
- CompPoly: `411708c17175ab5ecaf035036608c206c4ee0878` on [`zksecurity/CompPoly@rabin-single-instance-path`](https://github.com/zksecurity/CompPoly/tree/rabin-single-instance-path), including the concrete BF64 and BF64.Ext3 presentations.

  This is upstream `df591bb8c6745126d1d72f5243faae3022b0432a` — the revision ArkLib resolves to — plus one commit making the KoalaBear Rabin certificates replay-safe. Cold kernel replay of `KoalaBear.sexticPoly_irreducible` from an empty environment, which is what Comparator does on every verification run, does not terminate at the upstream revision: the criteria applied against the `Field`-shaped goal and the certificate lemmas stated over `(ZMod p)[X]` carry different instance *terms* for the same instance, and reconciling them across a type containing `X ^ (fieldSize ^ 6)` sends the kernel into `Polynomial.pow → npowRec → Nat.rec`, one exponent step at a time. Measured on the declaration's closure: deep recursion after 34s, against 5.8s once the criteria are applied at `ZMod fieldSize` as one fully-applied term. The statements are unchanged.

  The binary tracks were never affected — `BF64` already passes `ZMod.card 2`, so it only ever had one instance path — but the pin is shared, so it moves for both. This is the same class of problem, and the same kind of fix, as the `zksecurity/CompPoly@6416946` pin that `irs-provable-v4` carries; see `lean-verifier/docs/irs-handover.md`. Upstream has since adopted that fix's *shape* (the criteria now take `hcard : Fintype.card F = q`), which is necessary but, as the measurement above shows, not sufficient.

  CompPoly has no `[[require]]` in `lakefile.toml`; this revision is recorded only in `lake-manifest.json`, pinned transitively by ArkLib. That makes it the root of the whole dependency change: `BF64.Ext3` does not exist at the CompPoly revision the previous ArkLib pin resolved to — there is no `CompPoly/Fields/Binary/BF64/` directory there at all — so CompPoly must move for the binary tracks to exist. The CompPoly revision that has it requires Lean 4.34.0, and a Lake project has exactly one `lean-toolchain`, so the toolchain bump and hence the ArkLib bump follow from that requirement. The ArkLib jump is a consequence, not the driver.
- leanVM main: `2e6fe21d605a30be50770be9c0222fe737c5a47b`, the application parameter snapshot. See `crates/flock/tests/batch_proving_hashes.rs`, `crates/pcs/src/whir_config.rs`, `crates/pcs/src/ntt/additive_ntt_f64.rs`, and `crates/primitives/src/field/gf2_64x3.rs` in that revision.

The Flock witness-bit exponent is 14+18=32. Packing reduces it by six to 26. The initial lane exponent is six, so each scalar row has dimension 2^20. Rate 1/2 gives the additive domain size 2^21. leanVM uses a novel-basis encoder spanning the same RS evaluation code; the Toy encoder and protocol remain the existing formal abstraction.

Domain indices are polynomial-basis bit patterns, constructed explicitly with `BF64.ofBitVec`. Natural-number field casts would collapse to parity in characteristic two. The protected domain embedding includes the injectivity proof. Accepted received words use the whole extension-field alphabet, not only honest packed Boolean witnesses.

### Scope of the dependency migration

Relative to dev `main` at `c5f0eea`, this changes Lean from 4.32.2 to 4.34.0, ArkLib from `e65197892890b8fd9b0dc05b8980273cf1d595cc`, and CompPoly from `641694629e4557520a1539b272ec338c9f3044c7`. The earlier CompPoly pin lacks `BF64.Ext3`; the binary field's CompPoly release requires Lean 4.34.0, so the single-toolchain project also migrates ArkLib and its resolved dependencies.

The complete ArkLib migration changes the Toy IOP sources, including the `SampleableType` assumptions on `certifiedGammaError`, `certifiedExtractorError`, and `FixedRadiusCertificateBound`. This is distinct from the final refresh from `40c6adef15d8721620eb7b7805bd2214fe27dfae` to the pin above: only that smaller refresh leaves the Toy IOP sources and inherited dependency pins unchanged. The binary sampler adapter supplies the new sampling instance. The transitive axiom audits must pass on the complete pinned environment.

## Release requirements

The binary contracts have separate immutable slugs and versions in `challenges.json`. The shared Lean/ArkLib migration also bumps the Koala challenge version, because the trusted dependency environment changes. The existing remote registrations continue to describe their old immutable versions until separately updated.

Versions are immutable **per slug** and numbered independently. Matching numbers on two slugs do not require future bumps to remain in lockstep. Allocate each next version above every version already served for that slug, using the independent verifier's history rather than dev `main`. Both Koala slugs use `irs-reduction-threshold-v20` for this migration, and the binary slugs `binary-irs-reduction-threshold-v3`. The numbers are not the first free ones, because a version number is spent the moment the registry accepts a manifest, whether or not that version ever serves traffic: v18 and binary-v1 were registered with `image.source` and `image.revision` copied from v17's bundle-built manifest rather than read off the image's own labels, and correcting them changed the manifest digest, which the registry refuses to redefine. v19 was registered correctly but could not be staged — its canary was rejected for the CompPoly replay defect described under *Source pins* above.

Allocate each next version above every version already served for that slug, using the independent verifier's history rather than dev `main`: the [review of PR #142](https://github.com/proximity-prize/proximity-prize-dev/pull/142#issuecomment-5899164885) reports that production already served the proposed v15 and advanced further on the lower slug. Read `image.source` and `image.revision` off the built image's labels and validate the whole manifest before registering, never by analogy with the previous version's manifest. Recheck each slug's served history immediately before registration; the repository's version guard checks single-sourcing, not availability in production.

### Existing leaderboard submissions

The Koala bump makes existing accepted submissions ineligible for the new versions. Their results remain attached to their original immutable versions; the new leaderboards start without those results until migrated proofs are independently accepted. The leading submissions are well ahead of the seeds, and seed validation does not establish that they migrate.

The reviewer's attempt to migrate one leading submission confirmed that the seed's added `rfl` and `Set.mem_setOf_eq` rewrite in `HalfRadiusCollision.lean` carry over. Other proofs still fail under Lean 4.34.0 with deterministic timeout and deep-recursion errors despite raised `maxHeartbeats` and `maxRecDepth`; a further limit increase ran for more than ten minutes without resolving them. The other submission is reported to be roughly one hundred times larger. These are reported migration failures, not measurements of a completed migration.

Before registering the new Koala versions, coordinate migration with the proof generators and track the affected submissions' original versions, source commits, exact claims, remaining failures, and independent-verifier results. Require successful acceptance of the migrated leading submissions at the intended release commit, or record an explicit release decision to launch with only the newly accepted submissions. Keep the existing registrations and historical results available while that work is unresolved.

Before publication, register the exact protected targets, dependency pins, candidate namespaces, import boundaries, score direction, and new unsafe-index range with the independent verifier. Its accepted result must match the exact commit, slug, version, centibit score, and radius or unsafe index. Local checked artifacts remain diagnostic and never become authoritative automatically.

The binary lower seed uses proved unique decoding at radius 1/4: the interleaved MCA term is at most 2^21/2^192, and the two-input list term is at most 1/2^192. The upper seed interpolates on every half-domain set; the cardinality comparison against the field is valid because (2^192-1)^2 is below 2^400, while the central-binomial family is larger. Both seeds must pass the transitive axiom audit.

## Executable sampling and protocol checks

CompPoly already supplies executable `BF64`/`BF64.Ext3` arithmetic, `BF64.equivFin`, and the inverse extension coordinate maps `Ext.ofVector`/`Ext.coeffs`. The sampler adapter uses VCVio's `SampleableType.ofEquiv` and independent vector sampling. No change to either dependency is required. The adapter belongs with ArkLib's probability integrations when upstreamed, alongside `ArkLib.Data.Probability.KoalaBear`; CompPoly does not depend on VCVio.

The canonical sampler draws three uniform 64-bit words in coefficient order, with a kernel-checked uniformity theorem. Mathematical `Fintype` and real-valued security quantities can remain noncomputable; the sampler and concrete protocol algorithms compile independently of those enumerations. Protected code-generation gates specialize the Toy sampler, encoder, prover, verifier, and extractors to the production profile.

`scripts/validate.sh` also runs `scripts/BinaryToyRuntime.lean`. Its deterministic sampler trace checks exactly three full-width limb queries and their coordinate order. It executes VCVio's IO sampler, extension arithmetic, honest proving, accepted/rejected transcripts, erasure decoding, and both Toy constructions' extraction paths using small code dimensions over the production field. This establishes concrete runtime coverage without claiming production-size throughput or executing the noncomputable worst-case proximity quantities.
