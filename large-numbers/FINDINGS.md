---
harness:
  generated_by: plimsoll/0.1
  run_id: r_4124609cb118
  generated_at: 2026-08-06T16:49:49Z
  regenerable: true
---

# Findings

## Established

### For R = n-state 2-symbol Turing machines, BB(1..5) = 1, 6, 21, 107, 47176870 are all proven EXACT: BB(1-2) Rado 1962, BB(3) Lin&Rado 1963, BB(4) Brady 1983, BB(5)=47,176,870 proven July 2 2024 by the bbchallenge collaboration via a machine-checked Coq proof (lead Coq author mxdys, 10+ contributors); BB(6) is only lower-bounded, not exact.

- evidence: phase0/a-bbchallenge.md; bbchallenge.org: "The search of BB(5) has been completed as of July 2nd 2024. Therefore we now know that no machine halts after more than 47,176,870 steps." Coq: "See the formal Coq proof." Confirmed by discuss.bbchallenge.org thread "[July 2nd 2024] We have proved BB(5)=47176870", Quanta 2024-07-02, and Scott Aaronson blog p=8088.
- obtained_by: WebFetch of https://bbchallenge.org and https://bbchallenge.org/story plus WebSearch, on 2026-08-06; frozen verify v_8749f2487777 passes.

### Current best BB(6) lower bound is BB(6) > 2 up up up 5 (pentation), witnessed by machine 1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE found by mxdys June 2025; halting, Coq-verified (machine-checked) and community-confirmed on bbchallenge/BusyBeaverWiki, but not journal peer-reviewed. Prior record was Kropitz 2022 BB(6) > 10 up up 15.

- evidence: BusyBeaverWiki BB(6) (updated 2026-07-28): Champion 1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE, discoverer mxdys, June 2025, S(6) > Sigma(6) > 2 up up up 5, status Verified (linked to bbchallenge with halt status). Aaronson (scottaaronson.blog/?p=8972, 2025-06-28): BB(6) > 2 up up 2 up up 2 up up 9 with a correctness proof in Coq; intermediate step in a two-week run of records. Prior: Kropitz 2022 machine 1RB0LD_1RC0RF_1LC1LA_0LE1RZ_1LF0RB_0RC0RE ~ 10 up up 15.6.
- obtained_by: WebFetch of wiki.bbchallenge.org/wiki/BB(6) and scottaaronson.blog/?p=8972 plus WebSearch, 2026-08-06, item i_505e4a6948f9; recorded in phase0/b-bb6.md

### Code Golf bignum bakeoff ('Pole Position') top entries recorded: SE #146279 'Golf a number bigger than TREE(3)' (code-golf, shortest-wins; winner Simply Beautiful Art 135B Ruby reaching Hψ(φ3(Ω+1))(9), through eaglgenes101 569B Julia Loader's-number port) plus Tromp's fixed-bit BLC leaderboard (49-bit Melo's number > Graham; 61-bit w218; bits->growth: 100 Buchholz, 111 ε0, 331 BMS/PTO(Z2), 1850 Loader/PTO(Zω)). Neither bakeoff prices kappa(R); both fix one R and rank by budget.

- evidence: phase0/c-pole-position.md written and passes frozen verify v_d505dd45b8d7 (VERIFY_PASS). TREE(3) table from osmarks 2020-04 mirror of SE#146279 (live codegolf.stackexchange.com NOT fetchable from this env); BLC table from tromp.github.io/blog/2026/01/28/largest-number-revised (2026-01-28).
- obtained_by: WebSearch + WebFetch on 2026-08-06; verify: test -f && grep -qi 'Pole Position'/status/fetched

### All three transcript byte-figures are faithfully restated and cross-check against the Pole Position (Tromp BLC) leaderboard: 49B->Buchholz and 52B->BMS are CONFIRMED transcript-faithful but are CodeParade text-message constructions ~3.9x and ~1.26x looser than Tromp's optimum (100 bits=12.5B; 331 bits=41.4B); 233B->Loader is CONFIRMED and matches Tromp's current record (1850 bits=231.25B) within rounding. No BN-function.md figure is wrong; one flagged (not applied) clarification: line ~148 "15-49 bytes of BLC" collides with the 49-BIT Graham figure the video warns is "bits not bites".

- evidence: v1 verbatim: "the Buckle's ordinal function only takes 49 bytes at most"; v2: "Pat kale who managed to fit it in under 52 bytes of BLC"; v2: "exceeds loaders number in 233 bytes". Pole Position (phase0/c-pole-position.md, Tromp 2026-01-28): Buchholz 100 bits, BMS 331 bits, Loader 1850 bits. Arithmetic: 233B*8=1864 bits vs Tromp 1850 (1.01x); 52B=416 vs 331 (1.26x); 49B=392 vs 100 (3.92x). Recorded in phase0/d-byte-crosscheck.md.
- obtained_by: Located each figure in the .srt transcripts (python dedupe+context extract), matched attributions and units against phase0/c-pole-position.md, converted bytes<->bits.

### Googology Wiki's FOOT/BIG FOOT growth-rate ranking (BIG FOOT = FOOT^10(10^100), the oodle-theory analogue of Rayo, asserted 'enormously larger than Rayo's number') is NOT backed by a cited proof: it is a construction-motivated assertion by the definition's author LittlePeng9/Wojowu; the only rigorous result in the area is P-adic (P進大好きbot)'s cited refutation that first-order oodle theory is inconsistent, hence FOOT/BIG FOOT is ill-defined.

- evidence: phase0/e-foot.md, section 2. Cross-source (all WebSearch extractions, direct fetch blocked): 'BIG FOOT ... is enormously larger than Rayo's number' (author claim, no proof cited); refutation 'for any set theory T extending ZFC, if FOOT is well-defined in T, then T is inconsistent' from user blog 'Ill-definedness of BIG FOOT, Little Bigeddon, and Sasquatch' by P進大好きbot; consequence stated on wiki: BIG FOOT ill-defined and the 'larger than Rayo' comparison 'does not make sense.'
- obtained_by: WebSearch over googology.fandom.com / googology.miraheze.org pages (BIG_FOOT, Largest_valid_googologism, LittlePeng9 and P進大好きbot user blogs); direct WebFetch of all these pages returned HTTP 402 (Fandom) / 403 (Miraheze, grokipedia, namu, web.archive.org), so wording is search-extraction, not verbatim fetch, on 2026-08-06

### In the (kappa(R), growth) table, FOOT/BIG FOOT must be entered as an ill-defined candidate R with growth = UNDEFINED: because first-order oodle theory is inconsistent by a cited proof, BN(FOOT,.) has no defined growth rate (undefined, not merely unknown), unlike the proven/leaderboard-real growth values available for R = Busy Beaver and R = BLC.

- evidence: phase0/e-foot.md sections 2-3. The cited inconsistency ('if FOOT is well-defined in T then T is inconsistent') makes FOOT ill-defined; its claimed enormous growth over Rayo rests on a refuted author assertion. Contrast: phase0/a-bbchallenge.md (BB(1..5) proven exact) and phase0/c-pole-position.md (BLC bits->growth) carry real growth values. Its well-defined neighbour Rayo remains the live ceiling in this family.
- obtained_by: Synthesis in phase0/e-foot.md from WebSearch-sourced Googology Wiki material (2026-08-06); underlying ordering/refutation evidence recorded in f_e699190ae6bf

### Googology Wiki's ranking of Rayo's-function variants (Rayo < Fish 7 < BIG FOOT < Little Bigeddon < Sasquatch, with LNGN the current well-defined ceiling) rests on NO cited domination proof: every inter-variant 'bigger than' link is a construction-motivated author assertion ratified or withheld by community consensus; the only rigorous cited results in the family are refutations (P進大好きbot's proof that first-order oodle theory is inconsistent, making BIG FOOT/Little Bigeddon/Sasquatch ill-defined = growth undefined).

- evidence: phase0/f-rayo.md sections 1-3. Cross-source WebSearch extractions (direct fetch blocked: fandom HTTP 402, miraheze HTTP 403): Fish 7 'never officially recognized ... controversy regarding whether it is significantly larger than Rayo's number'; BIG FOOT 'completely dethroned Rayo's number ... enormously larger' (author Wojowu, no proof); Little Bigeddon 'was supposed to be larger than BIG FOOT'; Sasquatch 'too difficult for anyone else ... to understand ... not officially considered the title holder'; LNGN accepted because 'it hasn't been proven that it is ill-defined, and thereby it should be considered largest.' Refutation: 'for any set theory T extending ZFC, if FOOT is well-defined in T, then T is inconsistent.'
- obtained_by: WebSearch over googology.fandom.com / googology.miraheze.org pages Largest_valid_googologism, Rayo's_number, BIG_FOOT, Little_Bigeddon, Sasquatch, Large_Number_Garden_Number, 2026-08-06; WebFetch of both hosts returned 402/403 so wording is search-extraction, not verbatim page text

### No priced (kappa(R), growth) pairs are extractable from Googology Wiki's Rayo-variant ranking beyond the isolated well-defined anchors Rayo's number and LNGN: three of six variants (BIG FOOT, Little Bigeddon, Sasquatch) are ill-defined by cited proof (growth undefined), and the surviving order (Rayo, Fish 7, LNGN) is author-assertion-plus-consensus, never a cited domination proof, so the family yields no monotone kappa-vs-growth curve.

- evidence: phase0/f-rayo.md section 4. Well-defined survivors: Rayo, LNGN (LNGN>Rayo asserted, not wiki-proven), plus contested Fish 7. Contrast phase0/a-bbchallenge.md (BB(1..5) proven exact) and phase0/c-pole-position.md (BLC bits->growth, leaderboard-real), which carry certified growth values; the Rayo family instead gives at most an ordinal-analysis growth story per well-defined R with a non-proof-grounded inter-variant ranking.
- obtained_by: Synthesis of the ranking-basis audit in phase0/f-rayo.md against the project's certified-data bar; ranking wording from 2026-08-06 WebSearch extractions of the Googology Wiki pages (direct fetch blocked 402/403)

### Googology Wiki's array-notation hierarchy orders linear < multidimensional < tetrational < pentational-and-above arrays with FGH limit ordinals ω^ω, ω^(ω^ω), ε₀; the linear and multidimensional FGH placements are backed by a CITED PROOF (Chris Bird's derivation 'The Fast-Growing Hierarchy in Terms of Bird's Array Notations'), tetrational≈f_ε0 by consensus, and pentational+ BEAF is ill-defined (Bowers never defined it) so its growth is undefined.

- evidence: phase0/g-array-notation.md. Verify v_be29ccf22e0a passes: test -f && grep 'array notation' && grep status && grep fetched -> VERIFY_PASS. Bird PDF (mrob.com, HTTP 200, pages 1-3 read directly): f_ω(n)={2,n,n-1} = lowest non-primitive-recursive, ~ single-arg Ackermann; f_{ω+1}(64) > Graham's Number; f_{ω^2}(n) > {n,n,n,n} >= Conway chained arrows (n entries); f_{ω^k}(n) > {n,n,...,n} (k+2 n's) so linear arrays span to ~f_{ω^ω}; Multi-Dimensional Array Notation [2]-separators start at f_{ω^ω}(n) > {n,n+2[2]2}. Wiki (search-extracted, fandom HTTP 402): 'linear and multidimensional array notations have limit ordinals ω^ω and ω^(ω^ω)'; 'Tetrational arrays ... growth rate of f_ε₀(n)'; 'no agreed-upon definition for the notation above tetrational arrays ... BEAF beyond tetrational arrays is ill-defined.'
- obtained_by: WebFetch of googology.fandom.com array pages returned HTTP 402; WebSearch extractions used for wiki wording; WebFetch of https://mrob.com/users/chrisb/Fast-Growing_Hierarchy.pdf returned HTTP 200, saved to disk, pages 1-3 read directly via the Read/PDF tool. Findings written to phase0/g-array-notation.md.

### All seven Phase 0 topics (a bbchallenge/BB1-5, b BB(6), c Pole Position bakeoff, d transcript byte-crosscheck, e FOOT/BIG FOOT, f Rayo variants, g array notation) are recorded and rendered in FINDINGS.md across 9 Established findings, each carrying a fetched date and an explicit status descriptor; frozen verify v_dab83685947a passes.

- evidence: grep ^### FINDINGS.md -> 9 headers spanning all 7 topics (a..g). Status descriptors present: proven x5, lower bound x1, Verified x2, CONFIRMED x3, ill-defined x9, UNDEFINED x4, consensus x3, cited x7. Fetched dates: 2026-08-06 x8 plus Tromp 2026-01-28 leaderboard date for the 0d synthesis finding. Verify: test -f FINDINGS.md && for t in bbchallenge BB(6 "Pole Position" Buchholz FOOT Rayo "array notation"; grep each; grep fetched; grep status -> VERIFY_PASS.
- obtained_by: Read FINDINGS.md and PHASE0-ITEMS-DRAFT.md (evidence contract: source/fetched/claim/status per entry); grep-audited the 9 Established blocks for per-topic coverage, fetched dates, and status tokens; ran frozen verify v_dab83685947a (exit 0, VERIFY_PASS) in the worktree on 2026-08-06.

### Phase 1 methodology fixed: kappa(R) is measured in Binary Lambda Calculus (BLC) bits as the length of a BLC interpreter for R (its parser + evaluation/reduction/proof rules, not the cost of computing any BN value), with per-family counting rules and 7 flagged definitional choices (C1-C7), all recorded in METHODOLOGY.md.

- evidence: METHODOLOGY.md written. Frozen verifies pass: v_818c41fbca35 (meta-language present) v1 PASS; v_44fe71ce0ce1 (Turing/lambda/BMS/proof/set theory all present) v2 PASS; v_bdf0089ad174 (arbitrary|definitional|conditional|this choice present) v3 PASS. Chosen meta-language = BLC because n-axis is already in BLC bits (commensurable), BLC is itself admissible/minimal, and concrete artifacts (Tromp self-interpreter, Kale BMS BLC port, loader.c) anchor Phase 2 estimates. kappa/n split: kappa = interpreter shared by all e; n = the specific machine/term/formula. Key caveat C1: absolute kappa is convention-dependent (shifts by an additive translator constant under a different meta-language per BN-function.md Section 6 invariance), so only orderings are robust; C7: BLC-as-meta-language rejects the PLAN kappa(TM)~0 convention (TM row = UTM-simulator length, not 0).
- obtained_by: Wrote METHODOLOGY.md grounded in BN-function.md (A5, Section 6 invariance), PLAN.md Phase 1, and phase0/c-pole-position.md; ran the three frozen verify grep commands in the worktree, all exit 0.

### KAPPA-TABLE.md row Turing machines (Busy Beaver): kappa(TM) estimated ~200-600 BLC bits for a universal-TM simulator (table decoder + step + halt + output readout), growth uncomputable (Rado 1962). Order-of-magnitude ESTIMATE, not a measured artifact; not zero under choice C7 (BLC meta-language, not a UTM).

- evidence: METHODOLOGY.md 2.1 (counts: universal-TM simulator; excludes the machine table and state count k, which are n) and C7 (PLAN Phase 1 kappa(TM)~0 rejected under BLC). Anchored to the ~232-bit self-interpreter of Row 2 as a lower reference; a UTM simulator is modestly larger for tape+table machinery. No canonical Phase 0 BLC UTM artifact exists, so flagged as estimate.
- obtained_by: Phase 2 synthesis in KAPPA-TABLE.md from METHODOLOGY.md 2.1/C7 and BN-function.md Section 6 (Rado uncomputability); frozen verifies v_96361455a8e7, v_8862fa7f9439, v_64469aebcbbb all pass in the worktree.

### KAPPA-TABLE.md row lambda/BLC: kappa(BLC) ~206-232 BLC bits (Tromp universal lambda term / BLC self-interpreter), or 0 bits under choice C2; growth uncomputable. Best-grounded row: a real exhibited sized artifact, not an estimate.

- evidence: METHODOLOGY.md 2.2 (counts: binary-lambda parser + beta-reduction + numeral readout) and C2 (self-reference charge: 0 vs self-interpreter length, both reported, self-interpreter primary). Tromp self-interpreter recorded in phase0/c-pole-position.md; classic ~232 bits, optimized ~206 bits.
- obtained_by: Phase 2 synthesis in KAPPA-TABLE.md from METHODOLOGY.md 2.2/C2 and Phase 0 phase0/c-pole-position.md (Tromp).

### KAPPA-TABLE.md row single-row BMS: kappa <~111 BLC bits (estimate), growth epsilon_0. Upper-bounded by multi-row (331 bits) via METHODOLOGY 2.3, and anchored (by inference, not measurement) to the epsilon_0/Goodstein landmark of 111 BLC bits since single-row BMS has epsilon_0 growth.

- evidence: METHODOLOGY.md 2.3 (single-row is a strictly smaller case set than multi-row, so kappa(single-row) < kappa(multi-row)). Phase 0 phase0/c-pole-position.md records epsilon_0 (Goodstein) reached at 111 BLC bits. No separately measured single-row-BMS BLC artifact in Phase 0, so flagged as estimate. Growth epsilon_0 per BN-function.md Section 7.
- obtained_by: Phase 2 synthesis in KAPPA-TABLE.md from METHODOLOGY.md 2.3 and Phase 0 phase0/c-pole-position.md (epsilon_0 = 111 bits).

### KAPPA-TABLE.md row multi-row BMS: kappa <~331 BLC bits, growth psi(Omega_omega) (Buchholz). Upper bound from Tromp BMS=331 bits / PTO(Z_2) landmark, read via the embed-the-evaluator argument (record term contains BMS decoder+expansion+FGH readout plus a small seed).

- evidence: Phase 0 phase0/c-pole-position.md: Bashicu Matrix System = 331 BLC bits, growth PTO(Z_2). METHODOLOGY.md 2.3 (counts: matrix decoder + expansion rule + FGH readout; Kale BLC port the named artifact). Field looseness noted: BN-function.md Section 7 assigns multi-row BMS Buchholz psi(Omega_omega) while Tromp labels 331 bits PTO(Z_2); 331 retained as the conservative upper bound either way.
- obtained_by: Phase 2 synthesis in KAPPA-TABLE.md from Phase 0 phase0/c-pole-position.md (BMS=331 bits) and METHODOLOGY.md 2.3.

### KAPPA-TABLE.md row System F / Calculus of Constructions (Loader): kappa <~1850 BLC bits, growth = PTO of System F/CoC. Upper bound from Tromp Loader landmark (record term embeds Loader D type-checker/normalizer plus seed); concrete alt artifacts loader.c and eaglgenes101 569-byte Julia port.

- evidence: Phase 0 phase0/c-pole-position.md: Loader number reached at 1850 BLC bits (Tromp), and eaglgenes101 569-byte Julia port of loader.c (569 is ASCII bytes, a real exhibited size but not a BLC-bit figure). METHODOLOGY.md 2.4 (counts: term/type parser + typing rules incl. CoC dependent product + normalization/readout). Growth per BN-function.md Section 7.
- obtained_by: Phase 2 synthesis in KAPPA-TABLE.md from Phase 0 phase0/c-pole-position.md (Loader=1850 bits; 569-byte port) and METHODOLOGY.md 2.4.

### KAPPA-TABLE.md row first-order set theory (Rayo): kappa reported INFEASIBLE to pin exactly; finite only via choice C4 (axiom schema counted as its finite template); lower-bounded by the FOL-over-in parser + Tarskian satisfaction skeleton, hence larger than the ~232-bit BLC self-interpreter (at least several hundred BLC bits). Growth uncomputable, dominates every function whose totality the theory proves.

- evidence: METHODOLOGY.md 2.5 explicit feasibility caveat (full BLC satisfaction-relation evaluator for FO set theory is a large undertaking with no exhibited Phase 0 artifact; Rayo defined via a metalinguistic SECOND-order satisfaction predicate) and C4 (without counting schemas as templates, kappa is infinite for any first-order theory). Not left as a bare placeholder, per the repo rule against reporting a guess as settled. Growth per BN-function.md Section 7.
- obtained_by: Phase 2 synthesis in KAPPA-TABLE.md from METHODOLOGY.md 2.5/C4 and BN-function.md Section 7.

### The assembled kappa(R) column shows growth rate does NOT scale smoothly/expensively with specification cost across the Turing-complete rows: a ~few-hundred-bit universal-TM simulator or a ~232-bit BLC self-interpreter already buys uncomputable, faster-than-every-computable-function growth, so the jump to uncomputable growth is paid almost entirely at the bottom of the kappa column. A genuine kappa-buys-growth gradient appears only among the sub-Turing-complete ordinal rows (single-row BMS <~111 < multi-row BMS <~331 < System F/CoC <~1850 bits), where a larger rule set tracks a strictly higher proof-theoretic ordinal.

- evidence: KAPPA-TABLE.md, "What the column does and does not support" section, built from the six per-row findings f_12d234476615, f_4197fb43ad07, f_b28eb6482e11, f_8f873b604d10, f_b62433fa66b7, f_3aee7521546d. Six data points (three estimates, one infeasible) is a sketch not a theorem; whether the sub-Turing gradient is a compactness law or just the sequence googology formalized is the open Phase 4 question (BN-function.md Section 8). Ordering robust only up to the C1/C6 slack, seed n included in the leaderboard anchors.
- obtained_by: Phase 2 synthesis across the six KAPPA-TABLE.md rows; frozen verifies v_96361455a8e7, v_8862fa7f9439, v_64469aebcbbb all pass in the worktree on 2026-08-06.

### phase3_check.py independently recomputes BB(1..5) and they agree with the Phase 0 audited ground truth (1, 6, 21, 107, 47176870); a --wrong-bb4 negative control is correctly rejected.

- evidence:

  ```
  default run: [OK] BB(1)=1, BB(2)=6 via full brute-force enumeration; BB(3)=21, BB(4)=107, BB(5)=47,176,870 via champion-witness simulation; "All recomputed Busy Beaver values agree"; exit 0.
  --wrong-bb4 run: injects BB(4)=108, simulator recomputes 107, [FAIL] mismatch, "Mismatch detected"; exit 1.
  ```

- obtained_by: /home/edward/Projects/plimsoll/.venv/bin/python3 phase3_check.py  and  ... phase3_check.py --wrong-bb4 (in worktree i_3ffda7bd4f12)

### Phase 4 conclusion (honest read, NO clean compactness law): across the six (kappa(R), growth) rows growth rate does not scale with specification cost under any single law; it splits into two regimes: (a) the Turing-complete rows (BLC ~206-232 bits or 0, universal-TM ~200-600 bits, Rayo infeasible/>a few hundred bits) all reach the same uncomputable, faster-than-every-computable-function ceiling, which SATURATES at the cheapest row, so paying more kappa buys no faster class; (b) the sub-Turing ordinal ladder (single-row BMS <~111 < multi-row BMS <~331 < System F/CoC <~1850 bits) shows a weak MONOTONE kappa-vs-PTO gradient, but it is confounded by selection (these are exactly the systems googology built as a deliberately increasing ladder, Section 8 question 2) and cannot be shown with this data to be the cheapest path to each ordinal; six data points, three of them estimates and one infeasible, is a sketch, not a theorem.

- evidence: KAPPA-TABLE.md "What the column does and does not support" (ordering: BLC ~206-232|0 < single-row BMS <~111 < multi-row BMS <~331 < System F/CoC <~1850 < Rayo infeasible; Turing machines ~200-600 estimate overlaps the low end because kappa prices only the fixed simulator, not the uncomputable growth it unlocks). Built from the six Phase-2 per-row findings f_12d234476615, f_4197fb43ad07, f_b28eb6482e11, f_8f873b604d10, f_b62433fa66b7, f_3aee7521546d. Phase 3 (phase3_check.py) independently reconfirmed BB(1..5)=1,6,21,107,47176870 with a --wrong-bb4 negative control rejected, i.e. it validates the n-axis Busy Beaver ANCHOR is real but does NOT test the kappa-vs-growth relation itself, so it neither confirms nor refutes a compactness law. Two independent obstructions to any firm law from this table: the two regimes above cannot be joined into one curve (a step-to-uncomputable plus a bounded-ordinal gradient are qualitatively different shapes), and every kappa number is a convention-dependent (choice C1) upper bound (choice C6) with estimate-level slack on 3 of 6 rows, so even the monotone sub-Turing gradient is not separable from the selection confound. Verdict recorded as "no clean law", per PLAN.md Phase 4 and the standing repo rule (PLAN.md "Explicitly out of scope": six data points is a sketch, not a theorem).
- obtained_by: Phase 4 synthesis over KAPPA-TABLE.md and BN-function.md Section 8 (the two compactness-law questions), the six Phase-2 per-row kappa findings, and the Phase-3 spot-check (phase3_check.py); no new computation, an honest read of the assembled table on 2026-08-06.

## Ruled out

Nothing ruled out yet.

## Superseded

Nothing superseded.
