# mathematics

Public mathematics research and write-ups.

## large-numbers/

What is the largest number you can name in n symbols, and what decides how
fast that grows? For any fixed rulebook there is a largest such number, but
no rulebook is final: adding a notion of truth the current rulebook cannot
express always gives a faster one. The main results:

- **Provable naming is Busy Beaver class.** The largest number a theory can
  provably name in n symbols lies between two Busy Beaver functions, for
  every consistent, computably axiomatized theory containing a weak base
  theory. Choosing stronger axioms only rescales n, by at most a constant times log n. Machine-checked
  in Lean 4.
- **A ladder of truth layers** above that, from arithmetic truth through
  Rayo's function and beyond, with the famous big numbers placed on it.
  Mostly paper arguments, labelled as such and not yet read by anyone
  outside the project.

Most of these results are classical in substance or unstated folklore;
what the project adds is mainly the Lean mechanization, plus a few paper
results described in the README below. Each note labels its
claims as machine-checked, paper or classical. Start with
[`large-numbers/README.md`](large-numbers/README.md).
