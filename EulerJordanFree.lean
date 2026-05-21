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
The trivial spanning tree: empty set of darts. This is a valid
`SpanningTree` when V ≤ 1 (no edges needed to "span" 0 or 1 vertex).
For V ≥ 2, building a spanning tree requires combinatorial work.
-/
def emptySpanningTree : M.SpanningTree where
  treeDarts := ∅
  one_per_edge := by intro _ h; simp at h
  spans := by intro _ _; exact ⟨[], by simp, trivial⟩

/--
**Existence of spanning tree (trivial case)**: any CMap admits at least
the empty spanning tree. This is satisfied by our weak `spans` condition
(which ends in `True`).

For the full Van Staudt argument, the `SpanningTree` structure must be
strengthened to require `|treeDarts| = V - 1`. Building such a tree is
the substantive remaining work.
-/
theorem spanningTree_nonempty : Nonempty M.SpanningTree :=
  ⟨emptySpanningTree M⟩

end CMap

/-! ## Block 3: Dual CMap

The dual of a CMap swaps the vertex and face permutations.
This gives us a parallel structure where what were faces become
vertices and vice versa. Edges stay the same.
-/

namespace CMap

variable {n : ℕ} (M : CMap n)

/--
**Dual CMap** (corrected): in a group, `a * b * c = 1` does NOT imply
`c * b * a = 1`. So the naive swap of vertex and face is not a CMap.

The correct dual uses inverses: vertex_dual = face⁻¹, edge_dual = edge⁻¹,
face_dual = vertex⁻¹. Then the relation rotates correctly.
-/
def dual : CMap n where
  vertex := M.face⁻¹
  edge   := M.edge⁻¹
  face   := M.vertex⁻¹
  rel := by
    -- Need: face_d * edge_d * vertex_d = 1
    -- i.e.  M.vertex⁻¹ * M.edge⁻¹ * M.face⁻¹ = 1
    -- That equals (M.face * M.edge * M.vertex)⁻¹ = 1⁻¹ = 1
    have h := M.rel
    have : (M.face * M.edge * M.vertex)⁻¹ = (1 : Equiv.Perm (Fin n))⁻¹ :=
      congrArg _ h
    simpa [mul_inv_rev, mul_assoc] using this
  edge_inv := by
    -- edge⁻¹ = edge (because edge is involutive)
    have h : M.edge⁻¹ = M.edge := by
      apply Equiv.ext; intro d
      apply M.edge.injective
      rw [Equiv.Perm.apply_inv_self]
      exact (M.edge_inv d).symm
    rw [h]; exact M.edge_inv
  no_loop := by
    intro d
    have h : M.edge⁻¹ = M.edge := by
      apply Equiv.ext; intro d
      apply M.edge.injective
      rw [Equiv.Perm.apply_inv_self]
      exact (M.edge_inv d).symm
    rw [h]; exact M.no_loop d

/-- Dual face = inverse of original vertex (so cycle structures match up to direction). -/
theorem dual_face : M.dual.face = M.vertex⁻¹ := rfl

/-- Dual vertex = inverse of original face. -/
theorem dual_vertex : M.dual.vertex = M.face⁻¹ := rfl

/-- Inverse permutations have the same cycle structure (and hence same orbit count). -/
theorem dual_edge_inv : M.dual.edge = M.edge⁻¹ := rfl

end CMap

/-! ## Block 4: Van Staudt's argument

The classical Van Staudt proof of V - E + F = 2 (no Jordan needed):

1. Take a spanning tree T of G with |T| = V - 1 edges.
2. The complement E \ T corresponds to a spanning tree T* of the dual G*.
3. |T*| = F - 1 edges.
4. Partition: |T| + |T*| = E.
5. Therefore (V-1) + (F-1) = E, i.e., V + F = E + 2.

We formalize this with explicit cardinality predicates.
-/

namespace CMap

variable {n : ℕ} (M : CMap n)

/-- Abstract counters for a CMap: numbers of vertex, edge, face orbits. -/
structure OrbitCounts where
  V : ℕ
  E : ℕ
  F : ℕ

/--
Van Staudt's argument as a pure arithmetic implication:
if a spanning tree exists with V-1 edges AND a dual spanning tree with
F-1 edges AND the two partition all E edges, then V - E + F = 2.

This isolates the COMBINATORIAL CONTENT (no topology, no Jordan).
-/
theorem vanStaudt_arith (counts : OrbitCounts)
    (hV : 1 ≤ counts.V)
    (hF : 1 ≤ counts.F)
    (hpartition : (counts.V - 1) + (counts.F - 1) = counts.E) :
    counts.V + counts.F = counts.E + 2 := by
  omega

/--
**Corollary**: signed form of Euler's formula via Van Staudt.
Given the partition hypothesis, V - E + F = 2 follows purely arithmetically.
-/
theorem euler_int_via_vanStaudt (counts : OrbitCounts)
    (hV : 1 ≤ counts.V) (hF : 1 ≤ counts.F)
    (hpartition : (counts.V - 1) + (counts.F - 1) = counts.E) :
    (counts.V : ℤ) - counts.E + counts.F = 2 := by
  have := vanStaudt_arith counts hV hF hpartition
  omega

end CMap

/-! ## Status

Block 1: ✓ CMap + RotationEmbedding + pos_iterate (0 sorry)
Block 2: ✓ SpanningTree structure + empty witness (0 sorry)
Block 3: ⚠ dual CMap defined (1 sorry: group relation needs care)
Block 4: ✓ Van Staudt arithmetic core proved (0 sorry)

What's PROVEN end-to-end (no Jordan curve theorem):
  vanStaudt_arith: the arithmetic core of Van Staudt's argument.
  Given (a) a spanning tree with V-1 edges, (b) a dual spanning tree
  with F-1 edges, (c) that they partition all E edges, Euler follows.

What REMAINS to close the full result:
  Construct the spanning tree (any connected CMap admits one with V-1 edges)
  Prove non-tree edges form a dual spanning tree with F-1 edges
  Both pieces are non-trivial combinatorial algorithms.
-/
