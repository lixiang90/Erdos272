# Erdős problem 272 — partial results

Author: **Li Xiang**.

This project studies families of distinct subsets of `{1, …, N}` whose intersections of **distinct** members are nonempty arithmetic progressions. Singletons and pairs count as arithmetic progressions. The members themselves need not be progressions.

If `v(N)` is the maximum size of such a family, the conjectured value is

$$
v(N)=\binom{N}{2}+1+\left\lfloor\frac{N-1}{4}\right\rfloor.
$$

The problem is [Erdős #272](https://www.erdosproblems.com/272), also listed as JSP-000233 in the [Justin Sun Prize](https://github.com/TheJustinSunPrize/awards).

## Results in this repository

**Theorem.** Let $N\ge200000$ be an integer. Among all families $\mathcal F$ of distinct subsets of $[N]=\{1,\ldots,N\}$ such that $A\cap B$ is a nonempty arithmetic progression for every pair of distinct members $A,B\in\mathcal F$, the maximum possible cardinality is

$$
\max |\mathcal F|=\binom{N}{2}+1+\left\lfloor\frac{N-1}{4}\right\rfloor.
$$

Singletons and two-element sets count as arithmetic progressions. Every such family satisfies this upper bound, and for every $N\ge200000$ a family attaining equality exists.

The following table gives the individual results, their ranges, and the corresponding Lean declarations.

| Result | Scope | Entry |
|---|---|---|
| Szabó's matching construction | Every `N ≥ 1` | `lower_bound` |
| The paper's theorem | Every `N ≥ 200000` | `paper_exact_value` |
| Formal upper bound and exact value | Every `N ≥ 200000` | `upper_bound`, `exact_value` |
| Existence of an attaining optimal family | Every `N ≥ 200000` | `optimal_family` |

All five public theorems are in [formal/PublicResults.lean](formal/PublicResults.lean), in namespace `JSP233.PublicResults`. The six problem definitions are written directly in that file. Their correspondence with the internal model is checked by Lean through definitional equality.

The [English paper (PDF)](paper/erdos272.pdf) and its [LaTeX source](paper/erdos272.tex) present the computer-assisted result for `N ≥ 200000`. They develop the explicit large-order argument and describe the mixed-source finite-window certificates and symbolic recovery. The complete structural proofs and finite certificates form the Lean electronic supplement.

The remaining finite range is `1 ≤ N < 200000`.

## Dated formalization milestones

The dates below use UTC+8 and record completed formal checks of the original problem. The numerical threshold is the start of the proved infinite range.

| Date | Proved range | Toolchain and milestone |
|---|---|---|
| 2026-10-31 | `N ≥ 642498` | Initial public release, Lean and mathlib 4.35.0 |
| 2026-11-08 | `N ≥ 291012` | Research development, Lean 4.32.2 |
| 2026-11-08 | `N ≥ 250262` | Research development, Lean 4.32.2 |
| 2026-11-08 | `N ≥ 243614` | Research development, Lean 4.32.2 |
| 2026-11-08 | `N ≥ 233811` | Research development, Lean 4.32.2 |
| 2026-11-09 | `N ≥ 200000` | Mixed-source proof and public migration to Lean and mathlib 4.35.0 |

## Check the proofs

Install [elan](https://github.com/leanprover/elan) and run the following commands.

```sh
git clone --branch dev https://github.com/lixiang90/Erdos272.git
cd Erdos272/formal
lake exe cache get
lake build
```

The project uses **Lean 4.35.0** and **mathlib v4.35.0**. Exact dependency commits are pinned in [formal/lake-manifest.json](formal/lake-manifest.json).

The public entry prints the theorem types and their axiom dependencies. The proofs use only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Finite arithmetic certificates are checked by Lean's kernel.

The public import closure was checked sequentially with one Lean thread and a 6 GiB aggregate committed-memory cap, reusing the pinned mathlib cache. A full build can take substantial time. On machines with limited resources, compile project modules one at a time in dependency order and limit concurrent Lean processes.

## Layout

```text
paper/
  erdos272.tex, erdos272.pdf    English paper and compiled PDF
formal/
  PublicResults.lean           Definitions and public theorem statements
  Erdos272/
    Foundation/, Core/         Finite-set model and basic structural facts
    Construction/              Szabó's construction and the extremal value
    Staircase/, Capacity/      Common-point counting
    Counting/, Geometry/       Private pairs and endpoint geometry
    Traces/, Retention/        Deletion, long traces, and restoration
    Resources/, Arithmetic/   Joint counts and exact arithmetic certificates
    Certificates/             Finite proof data
    Global/                   Assembly of the universal upper bounds
    */N200000/                Mixed-source certificates and final assembly
    */N233811/, */N243614/     Intermediate source and recovery windows
    */N250262/, */N291012/     Supporting finite-window certificates
```

See [formal/README.md](formal/README.md) for a reading route through the proof.

## Build the paper

Use the following commands with a standard TeX distribution.

```sh
cd paper
pdflatex -interaction=nonstopmode -halt-on-error erdos272.tex
pdflatex -interaction=nonstopmode -halt-on-error erdos272.tex
```

## Attribution and collaboration

The lower construction is due to Tibor Szabó. The common-point, private-pair, and staircase methods are developed in Zhanfu Yang's [preprint](https://arxiv.org/abs/2607.23004v1). The structural route also draws on work by J. Kohlmeyer and L. Kruer; the paper gives a fixed source reference. Research, coding, and review included AI assistance.

**Contributions that close the remaining finite gap are welcome. If you build on these results, please acknowledge this project, the earlier authors, and each contributor's specific work. Please contact the project through a GitHub issue to coordinate a joint application for the Justin Sun Prize.**

When reporting a new bound, state whether it is a mathematical argument, an independently checked computation, or a complete Lean theorem, and provide reproducible evidence for that scope.
