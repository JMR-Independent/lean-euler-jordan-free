# Euler for planar combinatorial maps without Jordan curve theorem

Experimental repo exploring whether the theorem

    geometric embedding of a planar graph ⟹ V - E + F = 2

can be proved in Lean 4 + Mathlib without formalizing the Jordan curve
theorem. The approach is Van Staudt's interdigitating spanning trees.

Status: work in progress. The stable production version is at
https://github.com/JMR-Independent/lean-euler-formula

## Plan

1. Block 1: RotationEmbedding with rotation system consistency
2. Block 2: spanning tree of a CombinatorialMap
3. Block 3: dual graph of a CombinatorialMap
4. Block 4: Van Staudt argument closing the main theorem

## Build

    lake build
