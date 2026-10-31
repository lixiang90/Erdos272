# Reading the formal proof

Start with [PublicResults.lean](PublicResults.lean). It contains all six definitions of the original extremal problem and five public results. The problem is about intersections of distinct members; `IsAP` excludes the empty set. No common point is assumed in the public upper bound.

## The paper's simpler proof

1. [Construction/Construction45.lean](Erdos272/Construction/Construction45.lean) proves the matching construction for every positive `N`.
2. [Resources/StarBound30.lean](Erdos272/Resources/StarBound30.lean) assembles the common-point upper bound from intrinsic private pairs and the complete staircase inequality.
3. [Counting/MiddleDeficit52.lean](Erdos272/Counting/MiddleDeficit52.lean) prepares the same original family, possibly reflected, with a root for retained crooked members and an endpoint deficit.
4. [Global/EndpointStability53.lean](Erdos272/Global/EndpointStability53.lean) derives the explicit logarithmic and geometric payments for every `N ≥ 2^49`.
5. [Global/NonInterval53.lean](Erdos272/Global/NonInterval53.lean) forces all retained members avoiding that root to be intervals.
6. [Retention/Terminal36.lean](Erdos272/Retention/Terminal36.lean) and [Retention/JointFringe44.lean](Erdos272/Retention/JointFringe44.lean) count the retained family and restore the deleted members using their common long core.
7. [Global/GlobalUpper53.lean](Erdos272/Global/GlobalUpper53.lean) assembles the original-family theorem. `PublicResults.paper_exact_value` uses this route directly.

## The refined public result

[Global/Global642498218.lean](Erdos272/Global/Global642498218.lean) is the final assembly for every `N ≥ 642498`. It combines the large-order theorem with the refined common-root and recovery certificates for the lower window. Its public conclusions assume only the numerical threshold and legality of the actual family.

The development contains 1,300 project modules, including the public entry. The directories group the main mathematical arguments and their arithmetic certificates.

## Build and check the proof

From this directory, run:

```sh
lake exe cache get
lake build
```

Use the committed Lean toolchain and Lake manifest. Finite certificates are discharged by ordinary Lean proof terms. `PublicResults.lean` prints the five public theorem types and their axiom dependencies, which use only `propext`, `Classical.choice`, and `Quot.sound`.

The arithmetic certificates can make a full build demanding. With limited resources, compile project modules sequentially in dependency order, reuse already compiled dependencies, and set process, thread, memory, and CPU limits suited to your machine.
