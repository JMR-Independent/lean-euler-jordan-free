/-
  Combinatorial Maps + Euler's Formula
  Bridges PR #16074 (CombinatorialMap infrastructure) with our
  PlanarGraph inductive proof of Euler's formula.

  This file:
  1. Reproduces the CombinatorialMap structure from PR #16074 verbatim
  2. Defines IsSpherical — a CMap is spherical if its orbit counts
     match a PlanarGraph witness
  3. Proves eulerCharacteristic = 2 for any spherical CMap
  4. Verifies concrete maps (triangle, K₄) by computation

  The key gap in PR #16074: IsPlanar is defined as eulerCharacteristic = 2
  but no map is ever shown to satisfy it. This file fills that gap.
-/
import Mathlib.GroupTheory.Perm.Cycle.Basic
import EulerMathlib

-- ============================================================
-- COMBINATORIAL MAP  (verbatim from PR #16074 by Rida Hamadani)
-- ============================================================

/--
A two-dimensional combinatorial map: darts `D` with three permutations
satisfying `facePerm * edgePerm * vertexPerm = 1`.
`edgePerm` is a fixed-point-free involution (pairs each dart with its
edge-partner; no loops).
-/
structure CombinatorialMap (D : Type*) where
  vertexPerm : Equiv.Perm D
  edgePerm   : Equiv.Perm D
  facePerm   : Equiv.Perm D
  face_mul_edge_mul_vertex_eq_one : facePerm * edgePerm * vertexPerm = 1
  edgePerm_involutive : Function.Involutive edgePerm
  isEmpty_fixedPoints_edgePerm : IsEmpty (Function.fixedPoints edgePerm)

namespace CombinatorialMap

variable {D : Type*} (M : CombinatorialMap D)

-- Vertices, Edges, Faces as orbit quotients (from PR #16074)
abbrev Vertex := Quotient (Equiv.Perm.SameCycle.setoid M.vertexPerm)
abbrev Edge   := Quotient (Equiv.Perm.SameCycle.setoid M.edgePerm)
abbrev Face   := Quotient (Equiv.Perm.SameCycle.setoid M.facePerm)

noncomputable instance [Fintype D] : Fintype M.Vertex := Fintype.ofFinite M.Vertex
noncomputable instance [Fintype D] : Fintype M.Edge   := Fintype.ofFinite M.Edge
noncomputable instance [Fintype D] : Fintype M.Face   := Fintype.ofFinite M.Face

/-- Euler characteristic: V - E + F -/
noncomputable def eulerCharacteristic [Fintype D] : ℤ :=
  Fintype.card M.Vertex - Fintype.card M.Edge + Fintype.card M.Face

/-- Planarity (PR #16074 definition): Euler characteristic equals 2 -/
def IsPlanar [Fintype D] : Prop := M.eulerCharacteristic = 2

-- ============================================================
-- SPHERICAL MAPS: THE BRIDGE
-- ============================================================

/--
A `CombinatorialMap` is **spherical** if its vertex, edge, and face counts
match those of some `PlanarGraph` witness.

This is the key bridge: `PlanarGraph` is our constructive characterization
of sphere maps, proved to satisfy Euler's formula. A spherical CMap
inherits this.
-/
def IsSpherical [Fintype D] : Prop :=
  ∃ v e f : ℕ,
    PlanarGraph v e f ∧
    Fintype.card M.Vertex = v ∧
    Fintype.card M.Edge   = e ∧
    Fintype.card M.Face   = f

/--
**Main theorem**: every spherical `CombinatorialMap` is planar,
i.e. its Euler characteristic equals 2.

Proof: the `PlanarGraph` witness satisfies `euler_int` (V - E + F = 2),
and the sphericality condition gives equal orbit counts.
-/
theorem eulerChar_of_spherical [Fintype D]
    (h : M.IsSpherical) : M.IsPlanar := by
  obtain ⟨v, e, f, hpg, hV, hE, hF⟩ := h
  simp only [IsPlanar, eulerCharacteristic, hV, hE, hF]
  exact PlanarGraph.euler_int hpg

end CombinatorialMap

-- ============================================================
-- CONCRETE EXAMPLE: TRIANGLE MAP
-- ============================================================
-- 6 darts: edge pairs {0,1}, {2,3}, {4,5}
-- vertexPerm: vertex A={0,5}, vertex B={1,2}, vertex C={3,4}
-- facePerm determined by the relation facePerm * edgePerm * vertexPerm = 1

/-- Triangle combinatorial map on Fin 6 -/
def triangleMap : CombinatorialMap (Fin 6) where
  -- edgePerm: 0↔1, 2↔3, 4↔5
  edgePerm := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5
  -- vertexPerm: cycles (0 5)(1 2)(3 4)
  vertexPerm :=
    Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 4
  -- facePerm determined by the group relation
  facePerm :=
    (Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 4)⁻¹ *
    (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5)⁻¹
  face_mul_edge_mul_vertex_eq_one := by
    simp [mul_assoc, mul_inv_cancel]
  edgePerm_involutive := by
    intro d; fin_cases d <;> simp [Equiv.swap, Equiv.Perm.mul_apply]
  isEmpty_fixedPoints_edgePerm := by
    refine ⟨fun ⟨d, hd⟩ => ?_⟩
    fin_cases d <;> simp [Function.fixedPoints, Equiv.swap] at hd

-- Verify orbit counts by computation
-- (These establish the IsSpherical witness)
-- Note: native_decide can compute these for Fin 6
example : Fintype.card (triangleMap.Vertex) = 3 := by native_decide
example : Fintype.card (triangleMap.Edge)   = 3 := by native_decide
example : Fintype.card (triangleMap.Face)   = 2 := by native_decide

/-- The triangle map is spherical: its orbit counts match PlanarGraph 3 3 2 -/
theorem triangleMap_isSpherical : triangleMap.IsSpherical :=
  ⟨3, 3, 2, PlanarGraph.triangle,
    by native_decide, by native_decide, by native_decide⟩

/-- The triangle map is planar (eulerCharacteristic = 2) -/
theorem triangleMap_isPlanar : triangleMap.IsPlanar :=
  triangleMap.eulerChar_of_spherical triangleMap_isSpherical

-- ============================================================
-- CONCRETE EXAMPLE: K₄ MAP
-- ============================================================
-- 12 darts: 2 per edge × 6 edges
-- Dart labeling: edge AB={0,1}, AC={2,3}, AD={4,5},
--               BC={6,7}, BD={8,9}, CD={10,11}
-- (dart 0 from A→B, dart 1 from B→A, etc.)
--
-- Planar embedding: D inside triangle ABC
-- Rotation at each vertex (CCW order of leaving darts):
--   A: 0→4→2→0  (toward B, D, C)  → 3-cycle (0 4 2)
--   B: 1→6→8→1  (toward A, C, D)  → 3-cycle (1 6 8)
--   C: 3→10→7→3 (toward A, D, B)  → 3-cycle (3 10 7)
--   D: 5→9→11→5 (toward A, B, C)  → 3-cycle (5 9 11)
--
-- Face orbits of φ = σ⁻¹ ∘ α:
--   {0,8,5}  = triangle ABD  ✓
--   {2,7,1}  = triangle ACB (outer) ✓
--   {4,11,3} = triangle ACD ✓
--   {6,10,9} = triangle BCD ✓  →  F=4

/-- K₄ combinatorial map: V=4, E=6, F=4 on 12 darts -/
def k4Map : CombinatorialMap (Fin 12) where
  -- edgePerm: (0↔1)(2↔3)(4↔5)(6↔7)(8↔9)(10↔11)
  edgePerm :=
    Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 *
    Equiv.swap 6 7 * Equiv.swap 8 9 * Equiv.swap 10 11
  -- vertexPerm: 3-cycles (0 4 2)(1 6 8)(3 10 7)(5 9 11)
  -- 3-cycle (a b c) = Equiv.swap a b * Equiv.swap b c
  vertexPerm :=
    Equiv.swap 0 4 * Equiv.swap 4 2 *
    Equiv.swap 1 6 * Equiv.swap 6 8 *
    Equiv.swap 3 10 * Equiv.swap 10 7 *
    Equiv.swap 5 9 * Equiv.swap 9 11
  -- facePerm: 3-cycles (0 8 5)(2 7 1)(4 11 3)(6 10 9)
  -- Derived from φ = σ⁻¹ ∘ α, verified by the table above
  facePerm :=
    Equiv.swap 0 8 * Equiv.swap 8 5 *
    Equiv.swap 2 7 * Equiv.swap 7 1 *
    Equiv.swap 4 11 * Equiv.swap 11 3 *
    Equiv.swap 6 10 * Equiv.swap 10 9
  face_mul_edge_mul_vertex_eq_one := by native_decide
  edgePerm_involutive              := by native_decide
  isEmpty_fixedPoints_edgePerm     := by
    refine ⟨fun ⟨d, hd⟩ => ?_⟩
    fin_cases d <;> simp [Function.fixedPoints] at hd

-- Verify orbit counts
example : Fintype.card (k4Map.Vertex) = 4 := by native_decide
example : Fintype.card (k4Map.Edge)   = 6 := by native_decide
example : Fintype.card (k4Map.Face)   = 4 := by native_decide

/-- The K₄ map is spherical: orbit counts match PlanarGraph 4 6 4 -/
theorem k4Map_isSpherical : k4Map.IsSpherical :=
  ⟨4, 6, 4, PlanarGraph.k4,
    by native_decide, by native_decide, by native_decide⟩

/-- K₄ is planar: eulerCharacteristic = 4 - 6 + 4 = 2 ✓ -/
theorem k4Map_isPlanar : k4Map.IsPlanar :=
  k4Map.eulerChar_of_spherical k4Map_isSpherical
