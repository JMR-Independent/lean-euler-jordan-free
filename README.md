# Euler for planar graphs without Jordan curve theorem

Experimental Lean 4 + Mathlib repo trying to prove

    geometric embedding of a graph ⟹ V - E + F = 2

without formalizing the Jordan curve theorem. Approach: Van Staudt's
interdigitating dual spanning trees.

Self-contained: defines a minimal computable CombinatorialMap and
builds the proof bottom-up.

Stable production version: https://github.com/JMR-Independent/lean-euler-formula

## Build

    lake build
