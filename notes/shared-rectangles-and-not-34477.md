# Shared raw disjunctions and redundant NOT gates on L-meta-34477

The exact desk question is whether one NOT can shorten the eight-input edge detector. The [earlier research note](eight-vertex-one-not-34477.md) records a 14-gate AND/OR circuit and a sufficient signed lower bound for a seven-input restriction. The unrestricted question remains open.

## Sharing the raw disjunctions

The [rectangle replay](shared-biclique-34477.cjs) allows any number of complete bipartite terms. Each term is an AND of two raw disjunctions. The final output is an OR of the terms. The raw disjunctions can share arbitrary intermediate OR gates, including gates whose two operand supports overlap.

For a chosen cover, the cost is twice the number of terms minus one, plus the number of distinct nonsingleton disjunctions computed. For each disjunction, the replay tries every pair of proper nonempty submasks with the required union. Processing larger masks first accounts for every helper and permits reuse. A repeated raw disjunction can always share a wire. Redundant terms can be removed, so it suffices to enumerate irredundant covers. The cover search picks an uncovered edge and visits every possible term covering it. Its pruning counts only already required terms and already required nonsingleton disjunctions.

The exact minimum in this class is 14 for the full graph and 12 after pinning input 1 to zero. The replay finds matching constructions and evaluates them on the entire Boolean cube. An early 11-operation sketch for the restriction misses edge 0–7. The twelve-operation signed lower bound therefore remains a separate, unresolved question.

## A same-size replacement for a redundant NOT

The [Lean proof](OneNotExtrema34477.lean) replaces one selected gate by a nullary constant. The original circuit lies pointwise between its forced-zero and forced-one versions, since all gates after the selected gate are monotone. Both forced versions are monotone if the surrounding gates are AND/OR. Their gate count equals the original count.

Every true incidence input contains a flag, and every false input is contained in a maximal independent set. If the NOT output is false on every flag, the forced-zero circuit agrees on flags and cannot create false positives. If the NOT output is true on every maximal independent set, the forced-one circuit agrees there and cannot lose positives. Monotonicity then extends either equality to the entire Boolean cube. A useful NOT must therefore have a source which is false on some flag and true on some maximal independent set.

The [boundary replay](one-not-extrema-34477.cjs) checks all 256 inputs against the 12 flags and seven maximal independent sets. It classifies every distinct raw-input monotone formula through three gates by its least formula size. At costs one, two and three the test rules out 12 of 56, 75 of 448 and 720 of 3,640 candidate NOT inputs, respectively. In particular the AND of two adjacent vertices is always ruled out.

The [local edit replay](one-not-local-edits-34477.cjs) separately tried 406 one-gate bypasses of two exact 14-gate circuits. It then checked 1,182,272 AND/OR replacements and 73,892 NOT replacements of a retained gate. These edits produced no 13-gate witness. The bounded signed-frontier trials also ended without a complete verdict.
