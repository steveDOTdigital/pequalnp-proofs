# Seven gates for the four-clique on six shared pins

Graph 33550 accepts exactly the six distinct pairs drawn from pins 0 through 3. It rejects singletons and pairs involving pins 4 or 5. The [original seven-gate construction](CliqueFourOnSix.lean) meets the promise on all 36 ordered pairs. A new [Lean lower bound](CliqueFourLower.lean) proves that six gates do not suffice, even with NOT. Together these give an exact minimum of seven in both gate models.

For the lower bound it suffices to look at ten inputs: the four singletons and six unordered pairs on the clique. A hypothetical circuit for the full promise must work on those ten inputs as well. Encode a wire by the ten bits it outputs on those inputs. The six raw wire tables are 15, 114, 420, 840, 0 and 0; the target is 366. The proof covers constants, copies, missing-wire reads, NOT, AND and OR under the project's actual semantics.

Permuting the four clique vertices permutes the ten coordinates and leaves the target unchanged. Renaming coordinates commutes with all three gate operations. If every currently available wire can be renamed into a state already proved safe, a continuation reaching the target would also work from that state. This justifies the symmetry reduction, including branches that produce an existing wire. The Lean checker verifies each renaming and each inclusion. The first three gate layers have 3, 19 and 142 representative states respectively. From each of the 142 states the checker excludes all remaining three-gate continuations. A final AND need only test partners containing all target bits, and a final OR need only test partners containing no bits outside the target. NOT and wires already equal to the target are checked separately. The earlier [independent live-wire replay](two-lit-33550-23193.py) remains an independent lower-bound calculation.

| Posted claim | Lean verdict |
| --- | --- |
| [L-meta-22973](https://data.pequalnp.com/data/lemma/L-meta-22973.12b76f75dfb8.json), six monotone gates suffice | Disproved by `monotoneLower`. |
| [L-meta-23193](https://data.pequalnp.com/data/lemma/L-meta-23193.ba1b1c876d9c.json), six gates suffice with NOT | Disproved by `generalLower`. This upgrades the previously recorded external lower bound. |
| [L-meta-21922](https://pequalnp.com/lemma#L-meta-21922), eight monotone gates suffice | Proved by `catalogue21922` using the original construction. |
| [L-meta-22536](https://pequalnp.com/lemma#L-meta-22536), eight gates suffice with NOT | Proved by `catalogue22536` using the original construction. |

Both [eight-gate proofs](CliqueFourCatalogue.lean) import the source of the prior witness. Each positive claim had three filings when the desk was checked. Neither six-gate claim supplied a negated filing.
