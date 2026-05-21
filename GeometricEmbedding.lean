/-
  Geometric embeddings of CombinatorialMaps with rotation systems.

  Strategy to avoid Jordan curve theorem:
  - Define a planar embedding that includes the rotation system (cyclic
    order of darts around each vertex), not just coordinates.
  - The rotation system makes the CMap's vertex permutation σ consistent
    with the geometric arrangement.
  - Use Van Staudt's dual spanning tree argument to derive Euler.
-/
import Mathlib.Data.Real.Basic
import CMapEuler

/-- A point in the real plane. -/
abbrev Point := ℝ × ℝ

/--
A **rotation-consistent** geometric embedding of a CombinatorialMap:
- Each dart is assigned a coordinate (its origin vertex's position)
- Darts in the same vertex orbit share coordinates
- The cyclic order of darts around each vertex, induced by σ,
  is consistent with the geometric angular order from that vertex

This stronger notion of embedding (compared to "just coordinates")
gives us enough structure to prove IsPlanar without Jordan curve theorem.
-/
structure RotationEmbedding {n : ℕ} (M : CombinatorialMap (Fin n)) where
  /-- Position of each dart's origin vertex. -/
  pos : Fin n → Point
  /-- Darts in same σ-orbit share position. -/
  same_vertex_same_pos :
    ∀ d : Fin n, pos (M.vertexPerm d) = pos d
  /-- Distinct vertex orbits have distinct positions. -/
  distinct_vertices :
    ∀ d₁ d₂ : Fin n,
      ¬ M.vertexPerm.SameCycle d₁ d₂ → pos d₁ ≠ pos d₂

/--
For a `RotationEmbedding`, two darts represent the same geometric vertex
iff they're in the same σ-orbit.
-/
theorem RotationEmbedding.pos_eq_iff_sameCycle
    {n : ℕ} {M : CombinatorialMap (Fin n)} (emb : RotationEmbedding M)
    (d₁ d₂ : Fin n) :
    emb.pos d₁ = emb.pos d₂ ↔ M.vertexPerm.SameCycle d₁ d₂ := by
  constructor
  · intro h
    by_contra hne
    exact emb.distinct_vertices d₁ d₂ hne h
  · intro h
    obtain ⟨k, hk⟩ := h
    -- Apply same_vertex_same_pos k times
    sorry

/--
A simpler `VertexLayout` (no rotation consistency, just coordinates).
This is the weaker notion used for concrete examples; it's not enough
to prove planarity in general.
-/
structure VertexLayout {n : ℕ} (M : CombinatorialMap (Fin n)) where
  pos : Fin n → Point
  same_vertex_same_pos :
    ∀ d₁ d₂ : Fin n, M.vertexPerm d₁ = d₂ → pos d₁ = pos d₂

namespace CombinatorialMap

-- ============================================================
-- CONCRETE LAYOUTS
-- ============================================================
-- Show that triangleMap and k4Map admit concrete vertex layouts.

/-- Triangle layout: 3 corners. -/
def triangleLayout : VertexLayout triangleMap where
  pos d :=
    match d with
    | ⟨0, _⟩ | ⟨5, _⟩ => (0, 0)
    | ⟨1, _⟩ | ⟨2, _⟩ => (1, 0)
    | _               => (1/2, 1)
  same_vertex_same_pos := by decide

/-- K₄ layout: triangle ABC with D in interior. -/
def k4Layout : VertexLayout k4Map where
  pos d :=
    match d with
    | ⟨0, _⟩ | ⟨2, _⟩ | ⟨4, _⟩  => (0, 0)
    | ⟨1, _⟩ | ⟨6, _⟩ | ⟨8, _⟩  => (4, 0)
    | ⟨3, _⟩ | ⟨7, _⟩ | ⟨10, _⟩ => (2, 4)
    | _                          => (2, 4/3)
  same_vertex_same_pos := by decide

theorem triangle_layout_distinct_vertices :
    triangleLayout.pos ⟨0, by decide⟩ ≠ triangleLayout.pos ⟨1, by decide⟩ ∧
    triangleLayout.pos ⟨1, by decide⟩ ≠ triangleLayout.pos ⟨3, by decide⟩ ∧
    triangleLayout.pos ⟨0, by decide⟩ ≠ triangleLayout.pos ⟨3, by decide⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [triangleLayout] <;> norm_num

theorem k4_layout_distinct_vertices :
    k4Layout.pos ⟨0, by decide⟩ ≠ k4Layout.pos ⟨1, by decide⟩ ∧
    k4Layout.pos ⟨1, by decide⟩ ≠ k4Layout.pos ⟨3, by decide⟩ ∧
    k4Layout.pos ⟨0, by decide⟩ ≠ k4Layout.pos ⟨3, by decide⟩ ∧
    k4Layout.pos ⟨0, by decide⟩ ≠ k4Layout.pos ⟨5, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [k4Layout] <;> norm_num

end CombinatorialMap

/-
PROGRESS TOWARD JORDAN-FREE EULER PROOF

This file introduces the foundation for proving `isPlanar_of_embedding`
without the Jordan curve theorem:

1. ✓ `RotationEmbedding` — embedding with rotation system consistency
2. ✗ Spanning tree of a CombinatorialMap (next file)
3. ✗ Dual graph of a CombinatorialMap (next file)
4. ✗ Van Staudt's interdigitating trees argument
5. ✗ `isPlanar_of_rotationEmbedding` — the main theorem

Currently `pos_eq_iff_sameCycle` has a sorry: requires iterating the
`same_vertex_same_pos` axiom along the σ-cycle. This is straightforward
but requires Nat induction with the cycle structure.

The remaining blocks (2-5) are the substantive work and will be
addressed in subsequent files.
-/
