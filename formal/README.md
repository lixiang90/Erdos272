# Reading the formal proof

Start with [PublicResults.lean](PublicResults.lean). It contains all six definitions of the original extremal problem and five public results. The upper bound, exact value, optimal family, and exact-value statement in the form used by the paper hold for every `N ≥ 19227`. The construction holds for every positive `N`. The problem is about intersections of distinct members, and `IsAP` requires a nonempty set.

## The final assembly and the first finite window

[Global/N19227/Global19227.lean](Erdos272/Global/N19227/Global19227.lean) proves the upper bound on the original family for every `N ≥ 19227`. The matching construction yields the exact value and an optimal family.

- For `19227 ≤ N ≤ 20257`, the proof splits on whether the retained nonprogression members have a common point. [RootedFamily20258.lean](Erdos272/Global/N20258/RootedFamily20258.lean) handles the common-point case. It bounds an entirely rooted retained family directly and otherwise restores the original family from a one-sided start.
- [Unrooted19227.lean](Erdos272/Global/N19227/Unrooted19227.lean) uses the first sparse cutoff in the other case. Arithmetic certificates for `19227–19682` reuse individual price proofs and check population bands against the ground interval endpoints. The [bridge](Erdos272/Global/N19227/CutBridge19227.lean) reuses the same cutoff argument and price tables over `19683–20257`.
- [Global20258.lean](Erdos272/Global/N20258/Global20258.lean) covers `N ≥ 20258`. Its finite-window argument connects to [Global40000.lean](Erdos272/Global/N40000/Global40000.lean) and the larger-order proofs.

## The large-order part of the paper

1. [Construction/Construction45.lean](Erdos272/Construction/Construction45.lean) proves the matching construction for every positive `N`.
2. [Resources/StarBound30.lean](Erdos272/Resources/StarBound30.lean) assembles the common-point upper bound from intrinsic private pairs and the complete staircase inequality.
3. [Counting/MiddleDeficit52.lean](Erdos272/Counting/MiddleDeficit52.lean) prepares the same original family, possibly reflected, with a root for retained crooked members and an endpoint deficit.
4. [Global/EndpointStability53.lean](Erdos272/Global/EndpointStability53.lean) derives the explicit logarithmic and geometric payments for every `N ≥ 2^49`.
5. [Global/NonInterval53.lean](Erdos272/Global/NonInterval53.lean) forces all retained members avoiding that root to be intervals.
6. [Retention/Terminal36.lean](Erdos272/Retention/Terminal36.lean) and [Retention/JointFringe44.lean](Erdos272/Retention/JointFringe44.lean) count the retained family and restore the deleted members using their common long core.
7. [Global/GlobalUpper53.lean](Erdos272/Global/GlobalUpper53.lean) assembles the original-family large-order theorem.

## The earlier 200000 theorem

[Global/N200000/Global200000.lean](Erdos272/Global/N200000/Global200000.lean) assembles the earlier theorem for every `N ≥ 200000`. Its public conclusions assume the numerical threshold and legality of the actual family.

1. [Core/N200000/CoreUnionSource200000.lean](Erdos272/Core/N200000/CoreUnionSource200000.lean) proves the longest-AP source for the actual member and step denominator.
2. [Core/N200000/MixedCore200000.lean](Erdos272/Core/N200000/MixedCore200000.lean) splits on the actual defect and combines that source with certified totient floors.
3. [Arithmetic/N200000/SourceQueryData200000.lean](Erdos272/Arithmetic/N200000/SourceQueryData200000.lean) records 150 source plans. The neighboring modules certify their finite prefixes, cleanup steps, and geometry.
4. [Resources/N200000/Layer200000.lean](Erdos272/Resources/N200000/Layer200000.lean) pays the actual near families. Its three source-payment modules include the empty initial potential layer.
5. [Global/N200000/CommonRoot200000.lean](Erdos272/Global/N200000/CommonRoot200000.lean) combines the three windows with the AP joint response and both remaining root branches.
6. [Retention/N200000/RecoveryChain200000.lean](Erdos272/Retention/N200000/RecoveryChain200000.lean) performs the two symbolic preparations, and [Restore200000.lean](Erdos272/Retention/N200000/Restore200000.lean) restores the original family.
7. Supporting windows are grouped under `N233811`, `N243614`, `N250262`, and `N291012` within the same mathematical topic directories.

Every project import names its physical path beneath this directory. Lake resolves the hierarchy directly. The six public definitions elaborate using their Mathlib imports alone, and the theorem proofs come from the project modules.

## Module and certificate organization

The sources use Lean 4.35's native `module` format, `public import` paths, and exposed public definitions. These definitions support the reductions used in kernel-checked arithmetic certificates and in the public model's definitional equality.

[Foundation/ProofTactics.lean](Erdos272/Foundation/ProofTactics.lean) gathers the tactics used by the combinatorial and arithmetic arguments. The mathematical theory imports appear in the modules that use them.

The staircase data's 757 declarations are grouped into 18 source files under [Certificates/Staircase249Data](Erdos272/Certificates/Staircase249Data). Their declaration payload is preserved byte for byte. [Foundation/Staircase249Data.lean](Erdos272/Foundation/Staircase249Data.lean) re-exports the declarations in their established namespace.

The prefix certificates use the arithmetic-only [PrefixChecks291012.lean](Erdos272/Arithmetic/N291012/PrefixChecks291012.lean) and [PrefixLookup291012.lean](Erdos272/Arithmetic/N291012/PrefixLookup291012.lean). The lookup and prefix certificates share the packed words in [TotientWords208.lean](Erdos272/Arithmetic/TotientWords208.lean). Their interpretation in the totient source is proved in [PrefixTableSound291012.lean](Erdos272/Arithmetic/N291012/PrefixTableSound291012.lean), including the identity with the established lookup.

## Build and check the proof

From this directory, run the following commands.

```sh
lake exe cache get
lake build
```

Use the committed Lean toolchain and Lake manifest. Finite certificates are discharged by ordinary Lean proof terms. `PublicResults.lean` prints the five public theorem types and their axiom dependencies, which use only `propext`, `Classical.choice`, and `Quot.sound`.

For a serial build with a Lean memory setting of 4096 MiB per invocation, run the following after fetching the mathlib cache.

```sh
lake env python check_public.py --memory 4096
```

The script follows the public file's imports in dependency order and runs one single-threaded Lean process at a time. It caches project objects by source and dependency fingerprints in `.lake/checked-public`. A full build includes several thousand project modules and can take substantial time.
