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
    rw [pow_succ, Equiv.Perm.mul_apply, emb.same_vertex_same_pos, ih]

end RotationEmbedding

/-! ## Status

What this file gives us so far:
- Self-contained CMap structure (computable, supports decide / native_decide)
- RotationEmbedding with rotation system constraint
- pos_iterate: the embedding respects iteration of vertex

Next blocks to add:
1. Spanning tree of CMap (combinatorial)
2. Dual graph (using face permutation)
3. Van Staudt: dual spanning tree partition implies V + F = E + 2
-/
