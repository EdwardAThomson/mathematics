# Big numbers as compression

*Essay, 2026-11-24. A plain-language companion to
[`PROVABLE-NAMING-REPORT.md`](PROVABLE-NAMING-REPORT.md),
[`THE-LADDER.md`](THE-LADDER.md) and
[`COMPLEXITY-AND-ENTROPY.md`](COMPLEXITY-AND-ENTROPY.md). It contains no new
mathematics. Where it leans on a result, it says whether that result is
machine-checked in this project, argued on paper here, or standard.*

## The contest is a compression contest

"Name the biggest number you can" sounds like a contest about size. It is
really a contest about compression. Anyone can write a bigger number by
writing more digits. The game only becomes interesting when the space is
limited: an index card, a chalkboard, N symbols. Then the question is how
much number you can pack into a small description.

Seen that way, every entry in the contest has two parts, just like a zip
file:

- a **message**: the short description you wrote down;
- a **decoder**: the shared understanding of what descriptions mean, which
  turns the message back into the number.

"10^100" is a seven-character message. The decoder is school arithmetic.
The number it unpacks to has a hundred and one digits. That is a
compression ratio of about fourteen to one, and the whole history of big
numbers is the history of improving that ratio.

## What more symbols can and cannot buy

With n symbols there are only so many different messages, roughly c^n for
some constant c. Each message unpacks to at most one number. So n symbols
can name at most about c^n different numbers, no matter how clever the
decoder is. This is the one law nothing in this subject breaks:
**n symbols carry at most n symbols' worth of information.**

Two consequences follow at once.

**Almost nothing is compressible.** Let Big(n) be the largest number
nameable in n symbols. There are Big(n) numbers below it, and only about
c^n names to go round. So nearly every number below Big(n) has no short
name at all. A typical number with a million digits needs about a million
digits to describe. This is the same reason most files cannot be zipped
smaller: there are not enough short files to stand for all the long ones.

**The contest is about the exceptions.** The numbers people compete with
are the rare ones that are both enormous and cheap to describe. Big(n) is
the most extreme exception at each budget: the single best "unpacked size
for packed size" that any message of n symbols achieves.

So the description-to-number map is one-to-one in the forward direction,
but it is nothing like a re-encoding of all numbers. It reaches a
vanishingly thin scattering of them. What the contest measures is not how
well numbers in general compress. It measures the upper limit of what
compression can ever yield.

## Average case and best case

Shannon's theory of information is about the average case. For a source
that produces messages at random, you cannot, on average, encode them in
fewer bits than the source's entropy. For numbers picked uniformly with a
million digits, that means about a million digits each. No scheme beats it.

Big(n) is about the best case. It asks: among all messages of n symbols,
which one unpacks furthest? The gap between the two is the entire subject.
On average, compression gains nothing. In the best case, the gain is
beyond any function a computer can calculate.

These two facts do not conflict. Shannon's limit is paid for by the
overwhelming majority of numbers that do not compress at all. The big
numbers are the few that got all the benefit.

## The decoder is where the power is

If messages are limited to n symbols, the only thing left to improve is
the decoder. This is what the ladder in this project is: a ranking of
decoders by strength.

| decoder | what it is allowed to do | best case, Big(n) |
|---|---|---|
| a fixed recipe | run one terminating procedure | a computable function: exponentials, Ackermann, Graham's construction, TREE |
| any program | run the message as a program and wait for it to finish | Busy Beaver |
| a proof checker | accept the number if some proof, in a chosen theory, pins it down | Busy Beaver again, whichever theory is chosen |
| a halting oracle | also knows which programs halt | the next Busy Beaver level |
| arithmetic truth | knows every true statement about whole numbers | beyond every Busy Beaver level |
| set-theoretic truth | knows what is true in the universe of sets | Rayo's function |

A practical compressor such as zip needs a decoder that runs quickly. Drop
the speed requirement and allow any decoder that eventually finishes, and
you reach the theoretical limit of ordinary compression. That limit is
called Kolmogorov complexity: the length of the shortest program that
prints a given object. Its best case is the Busy Beaver function.
*(Standard.)*

This project's main result is the third row. A proof checker looks like a
different and possibly stronger kind of decoder than a program runner, and
one might expect a stronger theory to give a better decoder. It does not.
Proof-based naming lands in the Busy Beaver class for every consistent,
computably axiomatized theory, from one with no induction at all up to set
theory. *(Machine-checked here, up to a rescaling of the symbol budget
whose exact size is on paper.)* In compression terms: **once the decoder
may run any program, adding axioms does not improve the compression
ratio.**

To do better you must give the decoder knowledge no computation can
produce: first which programs halt, then which statements with one "for
all" are true, then two, and so on. Each "for all" buys exactly one level.
*(Lowest levels machine-checked here; the general statement is a paper
proof in [`MIDDLE-RUNGS.md`](MIDDLE-RUNGS.md), not yet independently
checked.)*

## There is no best decoder

Could there be a strongest decoder, and so a true largest number in n
symbols? No, and the reason is a compression argument.

Suppose a decoder D could unpack the message "the best that D can do with
n symbols, plus one". Writing n in binary, that message is only about
log n symbols long, far shorter than n. So D would unpack a message of
fewer than n symbols to a number bigger than its own record for n symbols.
That is a contradiction. So no decoder can understand a description of its
own record. *(Machine-checked here, in an abstract setting.)*

But a second decoder that knows how D works can understand that
description. So it beats D, using a message of about log n symbols.
*(Machine-checked here in the abstract, and for the step from Busy Beaver
to the next level.)*

Every decoder can be beaten by one that understands it. The toll for each
step is the same every time: about log n symbols. And each step requires
that the stronger decoder actually exist, which is a mathematical
commitment that grows heavier as you climb. Rayo's decoder already needs
more than standard set theory supplies. BIG FOOT described a decoder that
turned out to be self-contradictory, and so named nothing.

So the price of a better compression ratio is never paid in symbols. It is
paid in what you are prepared to assume.

## What is inside the number

A last point, which runs against intuition. If Big(n) is produced from n
symbols, it contains at most n symbols of information, however long it is
when written out. Per digit, its information content is as close to zero
as anything can be. A random number is the opposite: every digit is news.

Yet those few symbols are not worthless. On the Busy Beaver rung, knowing
Big(n) would let you decide, for every program up to about size n, whether
it ever halts: run each one for that many steps and see. That is roughly n
bits of knowledge which no computer can ever work out. *(Standard, going
back to Chaitin.)* And a theory cannot prove even one exact value of its
own Big function, though it can prove lower bounds forever. *(Paper
argument here; apparently not stated in the literature.)*

So one of these numbers is a strange object: an unimaginably long string
that is nearly all padding, wrapped around a handful of bits that are
impossible to compute. Its size is the least interesting thing about it.

## In one paragraph

Naming big numbers is compression with a fixed message length. Message
length caps the information, so almost no numbers compress and the contest
is about the extreme exceptions. With messages fixed, all the power is in
the decoder. Decoders that compute, however cleverly, top out at Busy
Beaver, and choosing stronger axioms for a proof-checking decoder does not
help. Decoders that know truths no computation can reach form an endless
ladder, each rung beating the last for a toll of log n symbols, with the
real cost paid in assumptions. There is no best decoder, and so no largest
number in n symbols.
