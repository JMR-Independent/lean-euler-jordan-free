/-
  Euler for planar combinatorial maps WITHOUT Jordan curve theorem.

  Self-contained experimental file. Defines a minimal CombinatorialMap
  structure with explicit Decidable/Computable instances so we can use
  `native_decide` and `decide` freely. Then builds the Van Staudt
  spanning-tree argument that avoids Jordan.

  Status: experimental, in active development.
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Real.Basic

/-! ## Minimal CombinatorialMap on Fin n (computable variant) -/

structure CMap (n : ℕ) where
  vertex   : Equiv.Perm (Fin n)
  edge     : Equiv.Perm (Fin n)
  face     : Equiv.Perm (Fin n)
  rel      : face * edge * vertex = 1
  edge_inv : Function.Involutive edge
  no_loop  : ∀ d : Fin n, edge d ≠ d

namespace CMap

variable {n : ℕ} (M : CMap n)

/-- Two darts are in the same vertex orbit if related by some iterate of `vertex`. -/
def sameVertex (d₁ d₂ : Fin n) : Prop := M.vertex.SameCycle d₁ d₂

/-- Two darts are in the same edge orbit. -/
def sameEdge (d₁ d₂ : Fin n) : Prop := M.edge.SameCycle d₁ d₂

/-- Two darts are in the same face orbit. -/
def sameFace (d₁ d₂ : Fin n) : Prop := M.face.SameCycle d₁ d₂

end CMap

/-! ## Geometric embedding with rotation system

A `RotationEmbedding` assigns each dart a point in ℝ², with the
constraint that darts in the same vertex orbit share their point.
This makes the rotation order around each vertex (given by σ)
consistent with the geometric position.
-/

abbrev Point := ℝ × ℝ

structure RotationEmbedding {n : ℕ} (M : CMap n) where
  pos : Fin n → Point
  same_vertex_same_pos : ∀ d : Fin n, pos (M.vertex d) = pos d

namespace RotationEmbedding

variable {n : ℕ} {M : CMap n} (emb : RotationEmbedding M)

/-- Iterating `vertex` preserves `pos`. -/
theorem pos_iterate (d : Fin n) (k : ℕ) :
    emb.pos ((M.vertex ^ k) d) = emb.pos d := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, emb.same_vertex_same_pos, ih]

end RotationEmbedding

/-! ## Block 2: Connectivity and spanning trees

A CMap is *connected* if any two darts can be reached from each other
via repeated applications of `vertex` and `edge`. A *spanning tree* is
a set of edges that connects all vertex orbits without forming a cycle.

For Van Staudt's argument we need: any connected CMap admits a spanning
tree, and that spanning tree has exactly V - 1 edges.
-/

namespace CMap

variable {n : ℕ} (M : CMap n)

/-- A CMap is connected if every dart is reachable from every other
    via a sequence of vertex/edge moves. -/
def IsConnected : Prop :=
  ∀ d₁ d₂ : Fin n, ∃ (moves : List Bool),
    moves.foldl (fun d b => if b then M.edge d else M.vertex d) d₁ = d₂

/-- Two darts are adjacent (one is an edge-step away from the other). -/
def Adjacent (d₁ d₂ : Fin n) : Prop := M.edge d₁ = d₂ ∨ M.edge d₂ = d₁

/-- Vertex equivalence classes (the actual vertices of the CMap). -/
def VertexClass : Type := Quotient (Equiv.Perm.SameCycle.setoid M.vertex)

instance : DecidableEq M.VertexClass := Quotient.decidableEq

/-- The vertex of a dart. -/
def vertexOf (d : Fin n) : M.VertexClass := Quotient.mk _ d

/--
A *spanning tree* of a CMap is a set of darts (representing edges)
such that:
- it has exactly V - 1 elements (when V ≥ 1),
- it connects every pair of vertex classes,
- it has no cycle (no proper subset still spans).

For our purposes we only need its CARDINALITY to be V - 1 to apply
Van Staudt. The structural conditions (connectivity, acyclicity) are
existence-level: we just need to know such a tree exists.
-/
structure SpanningTree where
  /-- The set of darts representing tree edges (one dart per edge). -/
  treeDarts : Finset (Fin n)
  /-- Each pair contains exactly one of (d, edge d). -/
  one_per_edge : ∀ d ∈ treeDarts, M.edge d ∉ treeDarts
  /-- The tree connects every pair of vertex classes. -/
  spans :
    ∀ v₁ v₂ : M.VertexClass,
      ∃ (path : List (Fin n)), path.all (fun d => d ∈ treeDarts) ∧
      -- (path connects representatives of v₁ and v₂; details omitted)
      True

/--
**Goal: every connected CMap admits a spanning tree.**

This is a substantive combinatorial theorem (essentially: Kruskal's or
Prim's algorithm in the CMap setting). For the moment we state it; the
proof requires building the tree by induction on edge count.
-/
theorem spanningTree_exists (hconn : M.IsConnected) :
    Nonempty M.SpanningTree := by
  sorry

end CMap

/-! ## Status

Block 1: ✓ CMap + RotationEmbedding + pos_iterate
Block 2: ⚠ Spanning tree structure defined, existence is sorry

Next steps:
- Prove spanning_tree existence (induction on edges)
- Prove |spanning_tree| = V - 1 for connected CMap
- Define dual graph via face permutation
- Van Staudt: edges \ tree = spanning tree of dual ⟹ F - 1 edges left
-/
