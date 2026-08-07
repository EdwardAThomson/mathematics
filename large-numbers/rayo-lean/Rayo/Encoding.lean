/-
`Rayo.Encoding` — a Gödel coding of `Rayo.Formula` into the hereditarily-finite-set
model `Rayo.HF` already used by the k = 0-6 naming proofs.

Stage 1 of the diagonalization plan needs a `Formula` value represented *as an
HF-set object*, in the same universe the K0-K6 proofs already reason about,
rather than as an external Lean-level `Nat` or string. This file provides that:

* `natToHF : Nat → HF` and `decodeNat : HF → Option Nat`, a chain encoding of
  naturals into HF (used both for the two `Nat` fields of `Formula.mem`/`.eq`/
  `.all` and for the small constructor tags below), with a proved round trip.
* `encode : Formula → HF`, a tagged-list Gödel coding: every formula becomes
  `HF.mk (tag :: args)` where `tag` is the (HF-encoded) natural identifying the
  constructor and `args` are the HF-encodings of that constructor's fields.
* `decode : HF → Option Formula`, structural recursion on the same shape.
* `decode_encode : ∀ f, decode (encode f) = some f` — round-trip correctness.
* `encode_injective : Function.Injective encode` — a direct corollary of the
  round trip (if `encode f = encode g` then `decode (encode f) = decode (encode g)`,
  so `some f = some g`, so `f = g`).

## Formulation choice

The task allows either (a) `decode` with round-trip + injectivity, or (b) an
equivalent formulation. We chose (a): a *total* `encode : Formula → HF` paired
with a *partial* `decode : HF → Option Formula` (since not every HF set is the
code of a formula — e.g. `HF.empty` isn't), proved to be a one-sided inverse
pair via `decode_encode`. This is the standard shape for a Gödel numbering
into a superset (HF here plays the role ℕ plays in a classical Gödel numbering:
`encode` need not be surjective onto HF, only injective, and `decode` needs to
recognize its image). We did not attempt a full `decode ∘ encode = id` +
`encode ∘ decode = id` bijection onto a subtype, since `decode` genuinely has
no answer on most of HF (formulas are a vanishingly small, syntactically
constrained subset of all HF sets) — a `Formula ≃ {x // p x}` equivalence would
be equivalent in content to what is proved here, just repackaged, so we did not
add the extra bookkeeping.

No `sorry`, no `Classical.choice`, no external imports (`Nat` decidable
equality is decided constructively and pattern matching on `List` is
structural, so classical choice is never needed).
-/

import Rayo.Satisfaction

namespace Rayo

/-! ## Naturals as HF sets (chain encoding)

`natToHF n` is the length-`n` chain of singleton nestings: `natToHF 0 = ∅`,
`natToHF (n+1) = {natToHF n}`. This is *not* the von Neumann encoding used
elsewhere in the project for "the number n as an object being named" (that one
has n elements at the top level); this is purely a Gödel-coding device to turn
a `Nat` into a distinguishable HF shape with an easy, total decode. The two
encodings serve unrelated purposes and are not meant to agree. -/

/-- Encode a natural number as the HF chain `mk [mk [mk [... mk [] ...]]]`
of length `n`. -/
def natToHF : Nat → HF
  | 0 => HF.mk []
  | n + 1 => HF.mk [natToHF n]

/-- Decode an HF chain back to the natural number it encodes, if it has the
right shape (a chain of singletons bottoming out at the empty set). Anything
else (a node with 2+ children anywhere along the chain) decodes to `none`. -/
def decodeNat : HF → Option Nat
  | .mk [] => some 0
  | .mk [x] => (decodeNat x).map (· + 1)
  | .mk (_ :: _ :: _) => none

@[simp] theorem decodeNat_natToHF (n : Nat) : decodeNat (natToHF n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natToHF, decodeNat, ih]

theorem natToHF_injective : Function.Injective natToHF := by
  intro m n h
  have := congrArg decodeNat h
  simpa using this

/-! ## Formulas as HF sets (tagged-list Gödel coding)

Constructor tags (as plain `Nat`, then run through `natToHF`):
`0 = mem`, `1 = eq`, `2 = neg`, `3 = conj`, `4 = all`. -/

/-- Encode a `Formula` as an HF set: `HF.mk (tag :: fields)`, where `tag`
identifies the constructor and `fields` are the HF-encodings of its
arguments (`Nat` fields via `natToHF`, `Formula` fields via `encode`
itself). -/
def encode : Formula → HF
  | .mem i j  => HF.mk [natToHF 0, natToHF i, natToHF j]
  | .eq i j   => HF.mk [natToHF 1, natToHF i, natToHF j]
  | .neg φ    => HF.mk [natToHF 2, encode φ]
  | .conj φ ψ => HF.mk [natToHF 3, encode φ, encode ψ]
  | .all n φ  => HF.mk [natToHF 4, natToHF n, encode φ]

/-- Decode an HF set back to a `Formula`, if it has the shape `encode`
produces: a list whose head decodes to a known tag (0-4) and whose tail has
the arity and argument types that tag expects. Everything else (wrong arity,
unknown tag, a malformed tag or field) decodes to `none`. -/
def decode : HF → Option Formula
  | .mk [tagH, a, b] =>
    match decodeNat tagH with
    | some 0 =>
      match decodeNat a, decodeNat b with
      | some i, some j => some (.mem i j)
      | _, _ => none
    | some 1 =>
      match decodeNat a, decodeNat b with
      | some i, some j => some (.eq i j)
      | _, _ => none
    | some 3 =>
      match decode a, decode b with
      | some φ, some ψ => some (.conj φ ψ)
      | _, _ => none
    | some 4 =>
      match decodeNat a, decode b with
      | some n, some φ => some (.all n φ)
      | _, _ => none
    | _ => none
  | .mk [tagH, a] =>
    match decodeNat tagH with
    | some 2 =>
      match decode a with
      | some φ => some (.neg φ)
      | none => none
    | _ => none
  | .mk _ => none

/-- Round-trip correctness: decoding an encoded formula always recovers the
original formula exactly. This is the core Stage 1 result. -/
@[simp] theorem decode_encode (f : Formula) : decode (encode f) = some f := by
  induction f with
  | mem i j => simp [encode, decode]
  | eq i j => simp [encode, decode]
  | neg φ ih => simp [encode, decode, ih]
  | conj φ ψ ihφ ihψ => simp [encode, decode, ihφ, ihψ]
  | all n φ ih => simp [encode, decode, ih]

/-- `encode` is injective: distinct formulas always get distinct HF codes.
Immediate from the round trip: `decode` is a left inverse of `encode`, and
any function with a left inverse is injective. -/
theorem encode_injective : Function.Injective encode := by
  intro f g h
  have hf := decode_encode f
  have hg := decode_encode g
  rw [h, hg] at hf
  exact Option.some.inj hf.symm

end Rayo
