# lean-branching-processes

A Lean 4 formalisation library for **branching processes** and **probability generating functions (PGFs)**, built on top of [Mathlib4](https://github.com/leanprover-community/mathlib4).

## Objectives

1. **Probability Generating Functions (`PGF`):**
   - Measure-theoretic PGF definition $G_X(z) = \mathbb{E}[z^X]$ for $\mathbb{N}$-valued random variables.
   - Power series / PMF equivalence: $G_X(z) = \sum_{n=0}^\infty \mathbb{P}(X=n) z^n$.
   - MGF bridge: $G_X(z) = M_X(\ln z)$ for $z > 0$.
   - Compound sums & composition law: $G_{\sum_{i=1}^N X_i}(z) = G_N(G_X(z))$.
   - Moment recursions & Faà di Bruno derivative extraction at $z=1^-$.

2. **Branching Processes:**
   - **Galton–Watson Processes:** Generation-by-generation discrete branching $Z_{n+1} = \sum_{i=1}^{Z_n} X_{n,i}$, fixed-point extinction probability $q = G(q)$, and limit theorems.
   - **Bellman–Harris (Age-Dependent) Branching Processes:** Lifetime distributions, forward integral equation $\phi(u) = \int f(\phi(u e^{-y})) g(y) \, dy$, existence and asymptotic properties of the limit distribution $W$.

## Build & Usage

```sh
lake exe cache get
lake build
```

## Structure

- `LeanBranchingProcesses/PGF/Basic.lean` — Basic PGF definitions, convergence on $|z| \le 1$, and MGF bridge.
- `LeanBranchingProcesses/PGF/Composition.lean` — Compound sums and PGF composition.
- `LeanBranchingProcesses/GaltonWatson/Basic.lean` — Galton–Watson processes and extinction probabilities.
- `LeanBranchingProcesses.lean` — Library entrypoint.
