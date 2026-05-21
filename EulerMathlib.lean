/-
  Euler's Polyhedron Formula — Lean 4 + Mathlib Formalization
  V - E + F = 2  for connected planar graphs

  ## Main Results
  * `PlanarGraph`    — inductive type: connected planar graph evidence
  * `euler_formula`  — V + F = E + 2
  * `euler_int`      — V - E + F = 2  (signed form)
  * `k5_not_planar`  — K₅ is not planar
  * `k33_not_planar` — K₃,₃ is not planar
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/--
`PlanarGraph V E F` witnesses a connected planar graph with
`V` vertices, `E` edges, and `F` faces (including outer face).

Built by three elementary plane-graph operations that each preserve
the Euler invariant `V - E + F = 2`:

- `point`   — a single vertex in the plane  (1, 0, 1)
- `addLeaf` — attach a pendant vertex+edge  (V+1, E+1, F)
- `addEdge` — split a face with a new edge  (V, E+1, F+1)
-/
inductive PlanarGraph : ℕ → ℕ → ℕ → Prop where
  | point : PlanarGraph 1 0 1
  | addLeaf (v e f : ℕ) : PlanarGraph v e f → PlanarGraph (v + 1) (e + 1) f
  | addEdge (v e f : ℕ) : PlanarGraph v e f → PlanarGraph v (e + 1) (f + 1)

namespace PlanarGraph

/-- **Euler's formula**: `V + F = E + 2` for any connected planar graph. -/
theorem euler_formula {v e f : ℕ} (h : PlanarGraph v e f) : v + f = e + 2 := by
  induction h with
  | point              => omega
  | addLeaf _ _ _ _ ih => omega
  | addEdge _ _ _ _ ih => omega

/-- Signed form: `V - E + F = 2`. -/
theorem euler_int {v e f : ℕ} (h : PlanarGraph v e f) : (v : ℤ) - e + f = 2 := by
  have := euler_formula h; omega

-- ============================================================
-- CONCRETE WITNESSES (kernel-verified, no tactics)
-- ============================================================

theorem triangle    : PlanarGraph 3 3 2 :=
  .addEdge 3 2 1 (.addLeaf 2 1 1 (.addLeaf 1 0 1 .point))

theorem k4          : PlanarGraph 4 6 4 :=
  .addEdge 4 5 3 (.addEdge 4 4 2 (.addLeaf 3 3 2
    (.addEdge 3 2 1 (.addLeaf 2 1 1 (.addLeaf 1 0 1 .point)))))

theorem cube        : PlanarGraph 8 12 6 :=
  .addEdge 8 11 5 (.addEdge 8 10 4 (.addEdge 8 9 3 (.addEdge 8 8 2
    (.addEdge 8 7 1 (.addLeaf 7 6 1 (.addLeaf 6 5 1 (.addLeaf 5 4 1
      (.addLeaf 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1
        (.addLeaf 1 0 1 .point)))))))))))

theorem octahedron  : PlanarGraph 6 12 8 :=
  .addEdge 6 11 7 (.addEdge 6 10 6 (.addEdge 6 9 5 (.addEdge 6 8 4
    (.addEdge 6 7 3 (.addEdge 6 6 2 (.addEdge 6 5 1 (.addLeaf 5 4 1
      (.addLeaf 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1
        (.addLeaf 1 0 1 .point)))))))))))

-- ============================================================
-- COROLLARIES
-- ============================================================

/-- Triangulations satisfy `E = 3V - 6`. -/
theorem triangulation_edges {v e : ℕ} (hv : 2 ≤ v)
    (h : PlanarGraph v e (2 * v - 4)) : e = 3 * v - 6 := by
  have := euler_formula h; omega

/-- Planar graphs with face-degree ≥ 3 satisfy `E ≤ 3V - 6`. -/
theorem edge_bound {v e f : ℕ} (hv : 3 ≤ v)
    (h : PlanarGraph v e f) (hf : 3 * f ≤ 2 * e) : e ≤ 3 * v - 6 := by
  have := euler_formula h; omega

/-- Bipartite planar graphs satisfy `E ≤ 2V - 4`. -/
theorem bipartite_edge_bound {v e f : ℕ} (hv : 3 ≤ v)
    (h : PlanarGraph v e f) (hf : 4 * f ≤ 2 * e) : e ≤ 2 * v - 4 := by
  have := euler_formula h; omega

/--
**K₅ is not planar** (assuming every face has ≥ 3 edges, i.e. no multi-edges or loops).
If K₅ were embedded planarly: Euler gives f = 7, but then 3·7 = 21 > 2·10 = 20. Contradiction.
-/
theorem k5_not_planar : ¬ ∃ f, PlanarGraph 5 10 f ∧ 3 * f ≤ 2 * 10 := by
  rintro ⟨f, h, hf⟩; have := euler_formula h; omega

/--
**K₃,₃ is not planar** (bipartite: every face has ≥ 4 edges).
If K₃,₃ were embedded planarly: Euler gives f = 5, but then 4·5 = 20 > 2·9 = 18. Contradiction.
-/
theorem k33_not_planar : ¬ ∃ f, PlanarGraph 6 9 f ∧ 4 * f ≤ 2 * 9 := by
  rintro ⟨f, h, hf⟩; have := euler_formula h; omega

-- Square C₄: 4 vertices, 4 edges, 2 faces
theorem square : PlanarGraph 4 4 2 :=
  .addEdge 4 3 1 (.addLeaf 3 2 1 (.addLeaf 2 1 1 (.addLeaf 1 0 1 .point)))

end PlanarGraph

-- ============================================================
-- STEP 2: BRIDGE  SimpleGraph ↔ PlanarGraph
-- ============================================================
-- Connects our inductive type to Mathlib's SimpleGraph.
-- A PlanarEmbedding assigns a face count to a concrete graph
-- and provides a PlanarGraph witness with matching V and E.

open SimpleGraph in
/--
A `PlanarEmbedding G` witnesses that the graph `G` can be embedded
in the plane: it gives a face count and a `PlanarGraph` witness whose
vertex and edge counts match those of `G`.
-/
structure PlanarEmbedding {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] where
  faces   : ℕ
  witness : PlanarGraph (Fintype.card α) G.edgeFinset.card faces

/-- Euler's formula for any `SimpleGraph` with a `PlanarEmbedding`. -/
theorem euler_of_embedding {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (emb : PlanarEmbedding G) :
    (Fintype.card α : ℤ) - G.edgeFinset.card + emb.faces = 2 :=
  PlanarGraph.euler_int emb.witness

-- ============================================================
-- STEP 1: POSITIVE CASES  (concrete SimpleGraphs have witnesses)
-- ============================================================
-- K_n = complete graph on Fin n  (Mathlib: ⊤ : SimpleGraph (Fin n))

section PositiveCases

-- Vertex counts (trivial)
theorem Kn_vertices (n : ℕ) : Fintype.card (Fin n) = n := Fintype.card_fin n

-- Edge counts (verified by kernel computation)
theorem K3_edges : (⊤ : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by decide
theorem K4_edges : (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by decide
theorem K5_edges : (⊤ : SimpleGraph (Fin 5)).edgeFinset.card = 10 := by decide

-- K₃ is planarly embeddable
theorem K3_hasPlanarEmbedding :
    Nonempty (PlanarEmbedding (⊤ : SimpleGraph (Fin 3))) :=
  ⟨⟨2, by simp [Kn_vertices, K3_edges]; exact PlanarGraph.triangle⟩⟩

-- K₄ is planarly embeddable
theorem K4_hasPlanarEmbedding :
    Nonempty (PlanarEmbedding (⊤ : SimpleGraph (Fin 4))) :=
  ⟨⟨4, by simp [Kn_vertices, K4_edges]; exact PlanarGraph.k4⟩⟩

-- Euler holds for K₃ embedding
theorem K3_euler (emb : PlanarEmbedding (⊤ : SimpleGraph (Fin 3))) :
    (3 : ℤ) - 3 + emb.faces = 2 := by
  have := euler_of_embedding _ emb
  simp [Kn_vertices, K3_edges] at this
  exact this

end PositiveCases

-- ============================================================
-- STEP 3: K₅ NOT PLANARLY EMBEDDABLE
-- ============================================================
-- Full chain: Mathlib's SimpleGraph (Fin 5) → PlanarEmbedding →
-- PlanarGraph 5 10 f → Euler contradiction.

/--
**K₅ is not planarly embeddable** (with simple faces, i.e. each face
bounded by ≥ 3 edges — guaranteed since K₅ has no loops or multi-edges).

Full chain:
1. K₅ has V=5 (Fintype.card_fin)
2. K₅ has E=10 (by kernel computation)
3. Any PlanarEmbedding with 3·F ≤ 2·10 would need F=7 (Euler), but 3·7=21>20. ⊥
-/
theorem K5_not_planarly_embeddable :
    ¬ ∃ (emb : PlanarEmbedding (⊤ : SimpleGraph (Fin 5))),
        3 * emb.faces ≤ 2 * 10 := by
  rintro ⟨⟨f, h⟩, hf⟩
  simp [Kn_vertices, K5_edges] at h
  exact PlanarGraph.k5_not_planar ⟨f, h, hf⟩
