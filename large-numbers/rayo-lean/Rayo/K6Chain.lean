/-
`Rayo.K6Chain` — the k = 6 naming-cost item via the *successor-chain* strategy,
as opposed to `Rayo.K6`'s *enumerate-predecessors* strategy.

`RAYO-GROWTH-RATE.md` §2 flagged (and did not resolve) whether the minimal FOST
naming cost `n_k` is genuinely the `~3^k` blow-up the `K0.lean`-`K6.lean` table
exhibits, or whether a cheaper `O(k)` strategy exists: name `x` as "the result
of six successor steps starting from the empty set", reusing one fixed
"is empty" / "is successor of" building block at each step, rather than
re-deriving independent copies of `φ₀, …, φ₅` the way `K6.lean` does. This file
builds and mechanically checks that strategy for k = 6, to compare directly
against `n_6 = 11128`.

## The formula (convention form, `x = v₀`)

    φ₆(x) := ∃w₀ ∃w₁ ∃w₂ ∃w₃ ∃w₄ ∃w₅ (
        IsEmpty(w₀)
        ∧ IsSucc(w₁, w₀)
        ∧ IsSucc(w₂, w₁)
        ∧ IsSucc(w₃, w₂)
        ∧ IsSucc(w₄, w₃)
        ∧ IsSucc(w₅, w₄)
        ∧ IsSucc(x, w₅)
    )

with the two fixed `O(1)` building blocks:

    IsEmpty(w)   := ∀t ¬(t ∈ w)
    IsSucc(a, b) := ( ∀t ¬( (t∈a) ∧ (¬(t∈b) ∧ ¬(t=b)) ) )        -- a ⊆ b ∪ {b}
                    ∧ ( ( ∀t ¬( (t∈b) ∧ ¬(t∈a) ) )                -- b ⊆ a
                        ∧ (b ∈ a) )                               -- b ∈ a

`IsSucc(a, b)` is written directly in the primitive alphabet — no `∨`/`→`/`↔`
abbreviation-expansion is used, matching the same "write the De Morgan form
directly" discipline `K6.lean`'s own top-level classification clause already
uses. The right-hand direction (`a ⊆ b∪{b}`) needs De Morgan (`¬(t∈b∨t=b) ≡
¬t∈b ∧ ¬t=b`); the left-hand direction (`b∪{b} ⊆ a`) is split into "every
member of `b` is in `a`" plus "`b` itself is in `a`" (an implication with a
disjunctive antecedent decomposes into two separate clauses, needing no
`∨`/`→` primitive either).

Six chain variables `w₀..w₅ = v₁..v₆`, one shared bound variable `t = v₇`
reused across every `IsEmpty`/`IsSucc` block (safe: these blocks are siblings
under one conjunction, never nested inside one another's scope, so reusing an
index does not capture anything — variable *identity* is free under the
convention, `rayo-notes/convention-notes.md` §4).

## Symbol count n₆(chain)

Counted under `rayo-notes/convention-notes.md` §2/§4 with exactly the counting
rules `K6.lean`'s own header derivation uses: atom (`t∈x` or `t=x`) = 3;
`¬φ = |φ|+3`; `(φ∧ψ) = |φ|+|ψ|+3`; `Qv(φ) = |φ|+4` (`∃`/`∀` primitive, one
symbol each; each variable occurrence one symbol regardless of identity).
Cross-checked against the convention note's own worked φ₀ = 10 and φ₁ = 30.

    atom (t∈a, t=b, b∈a, ...)                          = 3
    IsEmpty(w) = ∀t(¬(t∈w))                             = 3+3+4 = 10
    D2 = ∀t(¬((t∈a)∧(¬(t∈b)∧¬(t=b))))
       ¬(t∈b)=6, ¬(t=b)=6, (¬∧¬)=6+6+3=15
       (t∈a ∧ (¬∧¬))=3+15+3=21, ¬(...)=21+3=24, ∀t(...)=24+4 = 28
    D1a = ∀t(¬((t∈b)∧¬(t∈a)))
       ¬(t∈a)=6, (t∈b∧¬(t∈a))=3+6+3=12, ¬(...)=12+3=15, ∀t(...)=15+4 = 19
    D1b = b∈a                                           = 3
    D1  = (D1a ∧ D1b) = 19+3+3                          = 25
    IsSucc(a,b) = (D2 ∧ D1) = 28+25+3                   = 56
    BigConj = IsEmpty(w₀) ∧ IsSucc(w₁,w₀) ∧ ... ∧ IsSucc(x,w₅)   (7 pieces,
      6 conjunction nodes)
       = (10 + 6·56) + 6·3 = 346 + 18                   = 364
    φ₆(chain) = ∃w₀∃w₁∃w₂∃w₃∃w₄∃w₅(BigConj) = 364 + 6·4 = 364+24 = **388**

n₆(chain) = **388**, versus `K6.lean`'s enumerate-predecessors `n_6 = 11128` —
about **28.7× shorter**, and in the "low hundreds" the `O(k)` prediction in
`RAYO-GROWTH-RATE.md` §2's "correction I owe" note called for. This is an
upper bound on the minimal cost of *this specific* successor-chain construction,
not a claim that 388 is the global minimum n_6 (`METHODOLOGY.md` C1) — but it
is a real, exhibited, mechanically-verified construction far cheaper than the
`K0.lean`-`K6.lean` table's `~3^k` strategy, confirming the K0-K6 numbers were
never minimal (as `RAYO-EXPLAINER.md` already said) and that the gap is large,
not marginal.

**Cross-check, and a resolved discrepancy in K2.lean-K6.lean's own headers.**
The 388 count above was cross-checked against an independent automated
symbol-counter over the `Formula` AST. It agrees on 388, and exactly reproduces
`K0.lean`/`K1.lean`'s documented `n_0 = 10`, `n_1 = 30`. It initially did *not*
reproduce `K2.lean`-`K6.lean`'s documented 128/403/1228/3703/11128 (it gave
122/385/1174/3541/10642 instead). Traced to ground: the gap is **not** an error
in the documented K2-K6 numbers. It is an unavoidable ambiguity in a *naive*
automated counter's naive treatment of the `¬∀¬`-for-`∃` encoding.
`¬(.all n (.neg φ))` is used for two different things in this codebase: (1)
the deliberate encoding of a primitive `∃` (cost `|φ|+4`, per `K1.lean`'s own
header note), and (2) the *incidental* same bit-pattern that results whenever
an already-`∀`-shaped named sub-formula (e.g. `zF`, "is empty") is separately
negated, as `K2.lean`-`K6.lean`'s exclusion clauses do (`¬φ₀(c)`, `¬φ₁(c)`,
…) — which is a plain negation (cost `|zF|+3`), not an `∃`, despite sharing
the identical AST shape. A syntax-only counter cannot tell these apart without
external knowledge of which occurrences the author intended as `∃`; a first
automated pass collapsed *both* readings to the `∃` discount, silently
undercounting every `¬φᵢ(c)` exclusion-clause occurrence by exactly 6 symbols
(the "`∃` overcounted by 6" signature `REUSE-COMPRESSION-REPORT.md` already
found and fixed once before, elsewhere) — and this undercount then compounds
by ~3× per level exactly because `K3.lean`-`K6.lean` each embed fresh copies of
every earlier `¬φᵢ(c)` clause. A full manual re-derivation of `K2.lean`'s
literal, compiled `phi2` term (not just re-trusting the header's own arithmetic
— walking the actual `.neg`/`.all`/`.conj`/`.mem` AST node by node, correctly
reading each `¬∀¬` occurrence as `∃` or as plain negation from *context*)
reproduces the header's stated 128 exactly, at every intermediate value
(`¬φ₀=13`, `¬φ₁=33`, `U=62`, …). **Judgment: the documented K2.lean-K6.lean
counts (128/403/1228/3703/11128) are correct**; the discrepancy was in the
naive automated counter, not in those files. This does not touch this file's
own 388: `phi6chain` contains exactly one place where `¬∀¬` occurs — the six
deliberate `ex` (`∃`) wrappers, built via a single dedicated helper for exactly
that purpose — and, confirmed by direct inspection of `isEmptyAt`/`isSuccAt`'s
defining equations above, no other `.neg` anywhere in this file wraps an
`.all`-topped sub-formula, so the ambiguity that affected `K2.lean`-`K6.lean`'s
exclusion clauses structurally cannot arise here.

## Extensionality (same subtlety as `K1.lean`-`K6.lean`)

The HF model of `Rayo.Satisfaction` is non-extensional (a set is a *list* of
elements, so e.g. `{∅}` and `{∅,∅}` are structurally distinct but
extensionally equal). `IsSucc`/`IsEmpty` only constrain *membership*, so
solutions are pinned down only up to extensional equality, exactly as in
`K1.lean`-`K6.lean`. We characterise solutions via the *same* membership
classification `K6.lean` already proves — `IsZero`, `IsOne`, …, `IsFive` from
`Rayo.K2`-`Rayo.K6` — so `phi6chain_names_six` below has *exactly* the same
conclusion shape as `K6.lean`'s own `phi6_names_six`, and reuses `K6.lean`'s
`ClassEq6` and its fifteen disjointness lemmas verbatim for the uniqueness
statement. This makes the comparison to `K6.lean` apples-to-apples per the
task's own requirement, not just an informal resemblance.

## Axiom discipline note

`K2.lean`-`K6.lean` already use `Classical.em`, so their own `#print axioms`
output is `[propext, Classical.choice, Quot.sound]`, not the
`[propext, Quot.sound]`-only bar the project's docs previously (incorrectly)
stated for all seven files — corrected in `RAYO-EXPLAINER.md`. Exact entry
point, confirmed by `#print axioms`, not just inspection: `Rayo.zF_iff` and
`Rayo.oneF_iff` (the imported k=0/k=1 sub-predicate lemmas K2.lean reuses) are
still `[propext, Quot.sound]`-only; `Classical.choice` first enters at
`K2.lean:183`, inside `satE0_iff`
(`rcases Classical.em (∃ a, a ∈ (e 0).elems ∧ IsZero a) with hex | hex`, used
to extract a witness from the `¬∀¬`-encoded `∃`), and again at `K2.lean:209`
(`satE1_iff`) and `K2.lean:241,243` (`satU_iff`, classifying a member as
`IsZero`/`IsOne`); it then propagates into `phi2_iff` (which `rw`s in all
three) and `phi2_unique`. The identical two patterns — `Classical.em (∃ …)` to
extract an existential witness, and `Classical.em (IsK m)` to classify a
member — repeat at `K3.lean:115,196,198,285,287,289`;
`K4.lean:181,183,185,303,305,307,309`;
`K5.lean:182,184,186,288,290,292,294,431,433,435,437,439`; and
`K6.lean:224,226,228,230,232,390,392,394,396,398,400`. (`Classical.em` itself
depends on `Classical.choice` in Lean 4 core — confirmed here directly via
`#print axioms Classical.em` — the standard Diaconescu-style derivation from
choice + `propext` + quotients, not a project-specific quirk.) This file uses
the same, already-established pattern (a single generic `sat_ex` lemma, proved
via `Classical.em`) for the same reason — extracting a witness from `¬∀¬` is
not derivable constructively without a decidability instance on the witness
predicate, which is not available here (`HF` has no `DecidableEq`). So this
file's axiom list matches `K2.lean`-`K6.lean`'s *actual* practice
(`[propext, Classical.choice, Quot.sound]`), not the stricter
`K0.lean`/`K1.lean` bar (which get away without `Classical.choice` only
because their formulas are shallow enough to case on a concrete list
structurally instead). Recorded here as an honest observation, not silently
smoothed over.

No `sorry`, no `Classical.choice`-avoidance theatre: every genuine use is
flagged above.
-/

import Rayo.K6

namespace Rayo

/-! ### The two `O(1)` building blocks.

`t = v₇` throughout; reused across sibling blocks (safe, see file header). -/

/-- `IsEmpty(w) := ∀t ¬(t ∈ w)`. -/
def isEmptyAt (w : Nat) : Formula := .all 7 (.neg (.mem 7 w))

/-- `IsSucc(a, b) := (∀t ¬(t∈a ∧ (¬t∈b ∧ ¬t=b))) ∧ ((∀t ¬(t∈b ∧ ¬t∈a)) ∧ b∈a)`,
i.e. "`a`'s members are exactly `b`'s members together with `b` itself". -/
def isSuccAt (a b : Nat) : Formula :=
  .conj
    (.all 7 (.neg (.conj (.mem 7 a) (.conj (.neg (.mem 7 b)) (.neg (.eq 7 b))))))
    (.conj
      (.all 7 (.neg (.conj (.mem 7 b) (.neg (.mem 7 a)))))
      (.mem b a))

/-- The chained conjunction of the seven blocks (see file header). -/
def bigConjChain : Formula :=
  .conj (isEmptyAt 1)
    (.conj (isSuccAt 2 1)
      (.conj (isSuccAt 3 2)
        (.conj (isSuccAt 4 3)
          (.conj (isSuccAt 5 4)
            (.conj (isSuccAt 6 5)
              (isSuccAt 0 6))))))

/-- `∃`, represented (mechanization-only, as in `K1.lean`-`K6.lean`) as `¬∀¬`. -/
def ex (n : Nat) (φ : Formula) : Formula := .neg (.all n (.neg φ))

/-- The k = 6 successor-chain naming formula. -/
def phi6chain : Formula := ex 1 (ex 2 (ex 3 (ex 4 (ex 5 (ex 6 bigConjChain)))))

/-! ### Peeling `∃` (generic, one lemma reused six times). -/

/-- `Sat` of an `ex`-quantified formula is genuinely an existential over `HF`.
The forward direction needs `Classical.em` (see file header note); the
backward direction is fully constructive. -/
theorem sat_ex (e : Env) (n : Nat) (φ : Formula) :
    Sat e (ex n φ) ↔ ∃ v : HF, Sat (Env.update e n v) φ := by
  unfold ex
  constructor
  · intro h
    rcases Classical.em (∃ v : HF, Sat (Env.update e n v) φ) with h1 | h1
    · exact h1
    · exact absurd (fun v hv => h1 ⟨v, hv⟩) h
  · rintro ⟨v, hv⟩ hall
    exact hall v hv

/-- Peeling all six existentials of `φ₆(chain)` at once. -/
theorem phi6chain_sat_iff (e : Env) :
    Sat e phi6chain ↔
      ∃ m0 m1 m2 m3 m4 m5 : HF,
        Sat (Env.update (Env.update (Env.update (Env.update (Env.update
          (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) bigConjChain := by
  unfold phi6chain
  simp only [sat_ex]

/-! ### Semantic characterisation of the two building blocks. -/

/-- The semantic reading of `IsSucc(a, b)`: `a`'s members are exactly `b`'s
members together with `b` itself. -/
def SuccOf (a b : HF) : Prop := ∀ t : HF, t ∈ a.elems ↔ (t ∈ b.elems ∨ t = b)

/-- `Sat` of `isSuccAt a b` (evaluated in an environment `env`) is exactly
`SuccOf (env a) (env b)`, provided the container variables `a`, `b` are
distinct from each other and from the shared bound variable `7`. -/
theorem isSuccAt_sat_iff (env : Env) (a b : Nat)
    (ha7 : a ≠ 7) (hb7 : b ≠ 7) :
    Sat env (isSuccAt a b) ↔ SuccOf (env a) (env b) := by
  unfold isSuccAt SuccOf
  simp only [Sat, HF.Mem]
  constructor
  · rintro ⟨hD2, hD1a, hD1b⟩ t
    have hD2t := hD2 t
    have hD1at := hD1a t
    rw [Env.update_same, Env.update_other env 7 a t ha7,
        Env.update_other env 7 b t hb7] at hD2t
    rw [Env.update_same, Env.update_other env 7 b t hb7,
        Env.update_other env 7 a t ha7] at hD1at
    constructor
    · intro ht
      rcases Classical.em (t ∈ (env b).elems ∨ t = env b) with hgoal | hgoal
      · exact hgoal
      · exact absurd ⟨ht, (fun hc => hgoal (Or.inl hc)), (fun hc => hgoal (Or.inr hc))⟩ hD2t
    · rintro (htb | hteq)
      · rcases Classical.em (t ∈ (env a).elems) with hgoal | hgoal
        · exact hgoal
        · exact absurd ⟨htb, hgoal⟩ hD1at
      · subst hteq
        exact hD1b
  · intro h
    refine ⟨fun t => ?_, fun t => ?_, ?_⟩
    · rw [Env.update_same, Env.update_other env 7 a t ha7,
          Env.update_other env 7 b t hb7]
      rintro ⟨hta, hnb, hne⟩
      exact hne (((h t).mp hta).resolve_left hnb)
    · rw [Env.update_same, Env.update_other env 7 b t hb7,
          Env.update_other env 7 a t ha7]
      rintro ⟨htb, hna⟩
      exact hna ((h t).mpr (Or.inl htb))
    · exact (h (env b)).mpr (Or.inr rfl)

/-- `Sat` of `isEmptyAt w` is exactly "`env w` has no members", provided the
container variable `w` is distinct from the shared bound variable `7`. -/
theorem isEmptyAt_sat_iff (env : Env) (w : Nat) (hw7 : w ≠ 7) :
    Sat env (isEmptyAt w) ↔ (∀ v : HF, ¬ v ∈ (env w).elems) := by
  unfold isEmptyAt
  simp only [Sat, HF.Mem]
  constructor
  · intro h v hv
    have h1 := h v
    rw [Env.update_same, Env.update_other env 7 w v hw7] at h1
    exact h1 hv
  · intro h v
    rw [Env.update_same, Env.update_other env 7 w v hw7]
    exact h v

/-! ### Unfolding `bigConjChain` under the six-fold updated environment. -/

/-- `Sat` of `bigConjChain`, evaluated under the six-fold updated environment
that binds `w₀ = v₁, …, w₅ = v₆` to `m0, …, m5`, is exactly the seven-clause
successor-chain condition on `m0, …, m5` and the original `e 0`. -/
theorem bigConjChain_sat_iff (e : Env) (m0 m1 m2 m3 m4 m5 : HF) :
    Sat (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) bigConjChain
      ↔ (∀ v : HF, ¬ v ∈ m0.elems) ∧ SuccOf m1 m0 ∧ SuccOf m2 m1 ∧ SuccOf m3 m2
          ∧ SuccOf m4 m3 ∧ SuccOf m5 m4 ∧ SuccOf (e 0) m5 := by
  have hv0 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 0 = e 0 := by
    simp [Env.update]
  have hv1 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 1 = m0 := by
    simp [Env.update]
  have hv2 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 2 = m1 := by
    simp [Env.update]
  have hv3 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 3 = m2 := by
    simp [Env.update]
  have hv4 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 4 = m3 := by
    simp [Env.update]
  have hv5 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 5 = m4 := by
    simp [Env.update]
  have hv6 : (Env.update (Env.update (Env.update (Env.update (Env.update
      (Env.update e 1 m0) 2 m1) 3 m2) 4 m3) 5 m4) 6 m5) 6 = m5 := by
    simp [Env.update]
  unfold bigConjChain
  simp only [Sat]
  rw [isEmptyAt_sat_iff _ 1 (by decide),
      isSuccAt_sat_iff _ 2 1 (by decide) (by decide),
      isSuccAt_sat_iff _ 3 2 (by decide) (by decide),
      isSuccAt_sat_iff _ 4 3 (by decide) (by decide),
      isSuccAt_sat_iff _ 5 4 (by decide) (by decide),
      isSuccAt_sat_iff _ 6 5 (by decide) (by decide),
      isSuccAt_sat_iff _ 0 6 (by decide) (by decide),
      hv0, hv1, hv2, hv3, hv4, hv5, hv6]

/-! ### Peeling all six existentials: the master characterisation. -/

theorem phi6chain_iff (e : Env) :
    Sat e phi6chain ↔
      ∃ m0 m1 m2 m3 m4 m5 : HF,
        (∀ v : HF, ¬ v ∈ m0.elems) ∧ SuccOf m1 m0 ∧ SuccOf m2 m1 ∧ SuccOf m3 m2
          ∧ SuccOf m4 m3 ∧ SuccOf m5 m4 ∧ SuccOf (e 0) m5 := by
  rw [phi6chain_sat_iff]
  constructor
  · rintro ⟨m0, m1, m2, m3, m4, m5, hsat⟩
    exact ⟨m0, m1, m2, m3, m4, m5, (bigConjChain_sat_iff e m0 m1 m2 m3 m4 m5).mp hsat⟩
  · rintro ⟨m0, m1, m2, m3, m4, m5, hsat⟩
    exact ⟨m0, m1, m2, m3, m4, m5, (bigConjChain_sat_iff e m0 m1 m2 m3 m4 m5).mpr hsat⟩

/-! ### The successor-classification chain: `IsZero → IsOne → IsTwo → … → IsFive
→ (the six-way membership classification)`, reusing `Rayo.K2`-`Rayo.K6`'s own
`IsZero`, …, `IsFive`. Each step is fully constructive except for the initial
"extract a witness from `b.elems ≠ []`" case split, which is a structural
`cases` on a concrete list (no `Classical.em` needed here — this part mirrors
`K1.lean`'s own trick). -/

theorem succOf_of_empty_isOne (a b : HF) (hb : ∀ v : HF, ¬ v ∈ b.elems)
    (h : SuccOf a b) : IsOne a := by
  have hbe : b = HF.empty := (no_mem_iff_empty b).mp hb
  refine ⟨?_, ?_⟩
  · intro hnil
    have hbin : b ∈ a.elems := (h b).mpr (Or.inr rfl)
    rw [hnil] at hbin
    simp at hbin
  · intro w hw
    rcases (h w).mp hw with hwb | hwb
    · exfalso; rw [hbe] at hwb; simp [HF.empty, HF.elems] at hwb
    · rw [hwb, hbe]

theorem succOf_of_one_isTwo (a b : HF) (hb : IsOne b) (h : SuccOf a b) : IsTwo a := by
  obtain ⟨hne, hallEmpty⟩ := hb
  refine ⟨?_, ⟨b, (h b).mpr (Or.inr rfl), ⟨hne, hallEmpty⟩⟩, ?_⟩
  · cases hbe : b.elems with
    | nil => exact absurd hbe hne
    | cons w0 rest =>
      have hw0 : w0 ∈ b.elems := by rw [hbe]; simp
      exact ⟨w0, (h w0).mpr (Or.inl hw0), hallEmpty w0 hw0⟩
  · intro w hw
    rcases (h w).mp hw with hwb | hwb
    · exact Or.inl (hallEmpty w hwb)
    · subst hwb; exact Or.inr ⟨hne, hallEmpty⟩

theorem succOf_of_two_isThree (a b : HF) (hb : IsTwo b) (h : SuccOf a b) : IsThree a := by
  obtain ⟨z0, hz0, hz0c⟩ := hb.1
  obtain ⟨o0, ho0, ho0c⟩ := hb.2.1
  have hall := hb.2.2
  refine ⟨⟨z0, (h z0).mpr (Or.inl hz0), hz0c⟩,
          ⟨o0, (h o0).mpr (Or.inl ho0), ho0c⟩,
          ⟨b, (h b).mpr (Or.inr rfl), hb⟩, ?_⟩
  intro w hw
  rcases (h w).mp hw with hwb | hwb
  · rcases hall w hwb with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  · subst hwb; exact Or.inr (Or.inr hb)

theorem succOf_of_three_isFour (a b : HF) (hb : IsThree b) (h : SuccOf a b) : IsFour a := by
  obtain ⟨z0, hz0, hz0c⟩ := hb.1
  obtain ⟨o0, ho0, ho0c⟩ := hb.2.1
  obtain ⟨t0, ht0, ht0c⟩ := hb.2.2.1
  have hall := hb.2.2.2
  refine ⟨⟨z0, (h z0).mpr (Or.inl hz0), hz0c⟩,
          ⟨o0, (h o0).mpr (Or.inl ho0), ho0c⟩,
          ⟨t0, (h t0).mpr (Or.inl ht0), ht0c⟩,
          ⟨b, (h b).mpr (Or.inr rfl), hb⟩, ?_⟩
  intro w hw
  rcases (h w).mp hw with hwb | hwb
  · rcases hall w hwb with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
  · subst hwb; exact Or.inr (Or.inr (Or.inr hb))

theorem succOf_of_four_isFive (a b : HF) (hb : IsFour b) (h : SuccOf a b) : IsFive a := by
  obtain ⟨z0, hz0, hz0c⟩ := hb.1
  obtain ⟨o0, ho0, ho0c⟩ := hb.2.1
  obtain ⟨t0, ht0, ht0c⟩ := hb.2.2.1
  obtain ⟨r0, hr0, hr0c⟩ := hb.2.2.2.1
  have hall := hb.2.2.2.2
  refine ⟨⟨z0, (h z0).mpr (Or.inl hz0), hz0c⟩,
          ⟨o0, (h o0).mpr (Or.inl ho0), ho0c⟩,
          ⟨t0, (h t0).mpr (Or.inl ht0), ht0c⟩,
          ⟨r0, (h r0).mpr (Or.inl hr0), hr0c⟩,
          ⟨b, (h b).mpr (Or.inr rfl), hb⟩, ?_⟩
  intro w hw
  rcases (h w).mp hw with hwb | hwb
  · rcases hall w hwb with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · subst hwb; exact Or.inr (Or.inr (Or.inr (Or.inr hb)))

/-- The final step: `SuccOf s b` with `IsFive b` gives `s` exactly the same
membership classification `K6.lean`'s `phi6_names_six` proves of a `φ₆`-solution
— a 0-member, a 1-member, …, a 5-member, and no other kind of member. -/
theorem succOf_of_five_names_six (s b : HF) (hb : IsFive b) (h : SuccOf s b) :
    (∃ z, z ∈ s.elems ∧ IsZero z)
    ∧ (∃ o, o ∈ s.elems ∧ IsOne o)
    ∧ (∃ t, t ∈ s.elems ∧ IsTwo t)
    ∧ (∃ r, r ∈ s.elems ∧ IsThree r)
    ∧ (∃ p, p ∈ s.elems ∧ IsFour p)
    ∧ (∃ q, q ∈ s.elems ∧ IsFive q)
    ∧ (∀ c, c ∈ s.elems →
        (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c ∨ IsFive c)) := by
  obtain ⟨z0, hz0, hz0c⟩ := hb.1
  obtain ⟨o0, ho0, ho0c⟩ := hb.2.1
  obtain ⟨t0, ht0, ht0c⟩ := hb.2.2.1
  obtain ⟨r0, hr0, hr0c⟩ := hb.2.2.2.1
  obtain ⟨p0, hp0, hp0c⟩ := hb.2.2.2.2.1
  have hall := hb.2.2.2.2.2
  refine ⟨⟨z0, (h z0).mpr (Or.inl hz0), hz0c⟩,
          ⟨o0, (h o0).mpr (Or.inl ho0), ho0c⟩,
          ⟨t0, (h t0).mpr (Or.inl ht0), ht0c⟩,
          ⟨r0, (h r0).mpr (Or.inl hr0), hr0c⟩,
          ⟨p0, (h p0).mpr (Or.inl hp0), hp0c⟩,
          ⟨b, (h b).mpr (Or.inr rfl), hb⟩, ?_⟩
  intro c hc
  rcases (h c).mp hc with hcb | hcb
  · rcases hall c hcb with h1 | h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
  · subst hcb; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hb))))

/-- Naming: any solution of the successor-chain formula has exactly the same
membership classification as `K6.lean`'s own `phi6_names_six` proves for its
(differently-constructed) `φ₆` — same correctness statement, different route. -/
theorem phi6chain_names_six (e : Env) (h : Sat e phi6chain) :
    (∃ a, a ∈ (e 0).elems ∧ IsZero a)
    ∧ (∃ b, b ∈ (e 0).elems ∧ IsOne b)
    ∧ (∃ d, d ∈ (e 0).elems ∧ IsTwo d)
    ∧ (∃ g, g ∈ (e 0).elems ∧ IsThree g)
    ∧ (∃ p, p ∈ (e 0).elems ∧ IsFour p)
    ∧ (∃ q, q ∈ (e 0).elems ∧ IsFive q)
    ∧ (∀ c, c ∈ (e 0).elems →
        (IsZero c ∨ IsOne c ∨ IsTwo c ∨ IsThree c ∨ IsFour c ∨ IsFive c)) := by
  obtain ⟨m0, m1, m2, m3, m4, m5, h0, h1, h2, h3, h4, h5, h6⟩ := (phi6chain_iff e).mp h
  have hb1 : IsOne m1 := succOf_of_empty_isOne m1 m0 h0 h1
  have hb2 : IsTwo m2 := succOf_of_one_isTwo m2 m1 hb1 h2
  have hb3 : IsThree m3 := succOf_of_two_isThree m3 m2 hb2 h3
  have hb4 : IsFour m4 := succOf_of_three_isFour m4 m3 hb3 h4
  have hb5 : IsFive m5 := succOf_of_four_isFive m5 m4 hb4 h5
  exact succOf_of_five_names_six (e 0) m5 hb5 h6

/-! ### Existence: the canonical `six` satisfies `φ₆(chain)`. -/

/-- `SuccOf` holds, tautologically, between `b` and its literal list-append
successor `HF.mk (b.elems ++ [b])` — the general fact each concrete step
(`one` from `HF.empty`, `two` from `one`, …) instantiates. -/
theorem succOf_succHF (b : HF) : SuccOf (HF.mk (b.elems ++ [b])) b := by
  intro t
  simp [HF.elems]

theorem phi6chain_holds_of_six : Sat (fun _ => six) phi6chain := by
  rw [phi6chain_iff]
  refine ⟨HF.empty, one, two, three, four, five, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; simp [HF.empty, HF.elems] at hv
  · exact succOf_succHF HF.empty
  · exact succOf_succHF one
  · exact succOf_succHF two
  · exact succOf_succHF three
  · exact succOf_succHF four
  · exact succOf_succHF five

/-- Uniqueness up to extensional equality — identical statement and proof
shape to `K6.lean`'s own `phi6_unique`, driven by `phi6chain_names_six`
instead of `phi6_iff`. -/
theorem phi6chain_unique (e e' : Env) (h : Sat e phi6chain) (h' : Sat e' phi6chain) :
    ∀ z, (∃ m, m ∈ (e 0).elems ∧ ClassEq6 z m)
        ↔ (∃ m, m ∈ (e' 0).elems ∧ ClassEq6 z m) := by
  obtain ⟨⟨a, ha, haz⟩, ⟨b, hb, hbo⟩, ⟨d, hd, hdt⟩, ⟨g, hg, hg3⟩, ⟨p, hp, hp4⟩, ⟨q, hq, hq5⟩, _⟩ :=
    phi6chain_names_six e h
  obtain ⟨⟨a', ha', haz'⟩, ⟨b', hb', hbo'⟩, ⟨d', hd', hdt'⟩, ⟨g', hg', hg3'⟩, ⟨p', hp', hp4'⟩,
      ⟨q', hq', hq5'⟩, _⟩ :=
    phi6chain_names_six e' h'
  intro z
  constructor
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩ | ⟨hz4, _⟩ | ⟨hz5, _⟩
    · exact ⟨a', ha', Or.inl ⟨hzz, haz'⟩⟩
    · exact ⟨b', hb', Or.inr (Or.inl ⟨hzo, hbo'⟩)⟩
    · exact ⟨d', hd', Or.inr (Or.inr (Or.inl ⟨hzt, hdt'⟩))⟩
    · exact ⟨g', hg', Or.inr (Or.inr (Or.inr (Or.inl ⟨hz3, hg3'⟩)))⟩
    · exact ⟨p', hp', Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz4, hp4'⟩))))⟩
    · exact ⟨q', hq', Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz5, hq5'⟩))))⟩
  · rintro ⟨_, _, hcls⟩
    rcases hcls with ⟨hzz, _⟩ | ⟨hzo, _⟩ | ⟨hzt, _⟩ | ⟨hz3, _⟩ | ⟨hz4, _⟩ | ⟨hz5, _⟩
    · exact ⟨a, ha, Or.inl ⟨hzz, haz⟩⟩
    · exact ⟨b, hb, Or.inr (Or.inl ⟨hzo, hbo⟩)⟩
    · exact ⟨d, hd, Or.inr (Or.inr (Or.inl ⟨hzt, hdt⟩))⟩
    · exact ⟨g, hg, Or.inr (Or.inr (Or.inr (Or.inl ⟨hz3, hg3⟩)))⟩
    · exact ⟨p, hp, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hz4, hp4⟩))))⟩
    · exact ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hz5, hq5⟩))))⟩

end Rayo
