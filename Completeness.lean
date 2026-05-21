/-
  Completeness: every connected CombinatorialMap satisfies eulerCharacteristic = 2

  Strategy:
  1. edge_count_eq: Fintype.card M.Edge = Fintype.card D / 2
     (fixed-point-free involution → every orbit has size 2)
  2. vertex_face_count_eq: Fintype.card M.Vertex + Fintype.card M.Face = Fintype.card D / 2 + 2
     (induction on darts: contraction-deletion)
  3. Combine: eulerCharacteristic = V - E + F = 2
-/
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Data.Fintype.Card
import CMapEuler

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

-- ============================================================
-- STEP 1: EDGE COUNT
-- ============================================================
-- For a fixed-point-free involution, every orbit has exactly 2 elements.
-- So the number of orbits = |D| / 2.

/-- No dart is a fixed point of edgePerm. -/
lemma edgePerm_no_fixedPoint (d : D) : M.edgePerm d ≠ d :=
  fun h => M.isEmpty_fixedPoints_edgePerm.false ⟨d, h⟩

/-- edgePerm has empty support complement: every dart is moved. -/
lemma edgePerm_support_eq_univ : M.edgePerm.support = Finset.univ := by
  ext d; simp [Equiv.Perm.mem_support, M.edgePerm_no_fixedPoint d]

/-- edgePerm is order-2 (squaring gives identity). -/
lemma edgePerm_sq : M.edgePerm ^ 2 = 1 := by
  ext d; simp [sq, Equiv.Perm.mul_apply, M.edgePerm_involutive]

/-- All cycle lengths of a fixed-point-free involution are 2. -/
lemma edgePerm_cycleType_mem (k : ℕ) (hk : k ∈ M.edgePerm.cycleType) : k = 2 := by
  -- k is a cycle length → k divides orderOf edgePerm = 2 → k ∈ {1, 2}
  -- k ≥ 2 since no fixed points → k = 2
  have hdvd : k ∣ M.edgePerm.orderOf := Equiv.Perm.dvd_orderOf_of_mem_cycleType hk
  have hord : M.edgePerm.orderOf ∣ 2 := by
    rw [← Equiv.Perm.orderOf_eq_card_pow_eq_one]
    exact orderOf_dvd_of_pow_eq_one M.edgePerm_sq
  have hle : k ∣ 2 := dvd_trans hdvd hord
  have hne1 : k ≠ 1 := by
    intro heq; subst heq
    -- A cycle of length 1 is a fixed point, contradicting hfp
    have := Equiv.Perm.one_mem_cycleType_iff.mp hk
    exact M.edgePerm_no_fixedPoint this.choose this.choose_spec
  interval_cases k <;> omega

/-- Sum of edgePerm cycleType = |D|. -/
lemma edgePerm_cycleType_sum :
    M.edgePerm.cycleType.sum = Fintype.card D := by
  rw [Equiv.Perm.sum_cycleType, M.edgePerm_support_eq_univ, Finset.card_univ]

/-- For a fixed-point-free involution, |D| = 2 * number_of_edges. -/
lemma dart_count_eq_twice_edges :
    Fintype.card D = 2 * M.edgePerm.cycleType.card := by
  have hsum := M.edgePerm_cycleType_sum
  have hall := fun k hk => M.edgePerm_cycleType_mem k hk
  -- cycleType is a multiset of 2s, so sum = 2 * card
  rw [← hsum]
  rw [show M.edgePerm.cycleType = Multiset.replicate M.edgePerm.cycleType.card 2 from by
    rw [Multiset.eq_replicate]
    exact ⟨rfl, hall⟩]
  simp [Multiset.sum_replicate]

/-- For a fixed-point-free involution, SameCycle d₀ d ↔ d = d₀ ∨ d = edgePerm d₀. -/
lemma edgePerm_sameCycle_iff (d₀ d : D) :
    M.edgePerm.SameCycle d₀ d ↔ d = d₀ ∨ d = M.edgePerm d₀ := by
  constructor
  · intro ⟨n, hn⟩
    -- edgePerm^2 = 1, so edgePerm^n = id (n even) or edgePerm (n odd)
    have h2 : M.edgePerm ^ (2 : ℤ) = 1 := by
      ext x; simp [zpow_succ, zpow_zero, Equiv.Perm.mul_apply, M.edgePerm_involutive x]
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · left
      have : (M.edgePerm ^ (2 * k)) d₀ = d₀ := by
        rw [zpow_mul]; simp [h2]
      rw [this] at hn; exact hn.symm
    · right
      have : (M.edgePerm ^ (2 * k + 1)) d₀ = M.edgePerm d₀ := by
        rw [zpow_add, zpow_mul, zpow_one]; simp [h2]
      rw [this] at hn; exact hn.symm
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

/-- Each edge-orbit (fiber) contains exactly 2 darts. -/
lemma edgePerm_fiber_card (e : M.Edge) :
    Fintype.card {d : D // (⟦d⟧ : M.Edge) = e} = 2 := by
  obtain ⟨d₀, rfl⟩ := Quotient.exists_rep e
  have hne : d₀ ≠ M.edgePerm d₀ := (M.edgePerm_no_fixedPoint d₀).symm
  -- Fiber = {d₀, edgePerm d₀} exactly
  have hfiber : ∀ d : D, (⟦d⟧ : M.Edge) = ⟦d₀⟧ ↔ d = d₀ ∨ d = M.edgePerm d₀ := by
    intro d; rw [Quotient.eq']; exact M.edgePerm_sameCycle_iff d₀ d
  -- Count the elements
  have : Fintype.card {d : D // (⟦d⟧ : M.Edge) = ⟦d₀⟧} =
         ({d₀, M.edgePerm d₀} : Finset D).card := by
    apply Fintype.card_congr
    exact {
      toFun  := fun ⟨d, hd⟩ => ⟨d, by
        simp [Finset.mem_insert, Finset.mem_singleton]; exact (hfiber d).mp hd⟩
      invFun := fun ⟨d, hd⟩ => ⟨d, by
        simp [Finset.mem_insert, Finset.mem_singleton] at hd
        exact (hfiber d).mpr hd⟩
      left_inv  := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [this, Finset.card_pair hne]

/-- For a fixed-point-free involution: |D| = 2 * |Edge|, so |Edge| = |D|/2. -/
theorem edge_count_eq :
    Fintype.card M.Edge = Fintype.card D / 2 := by
  -- Use the fiber decomposition: D = Σ e : M.Edge, fiber(e)
  -- Each fiber has size 2 → |D| = 2 * |M.Edge| → |M.Edge| = |D|/2
  have hfib := M.edgePerm_fiber_card
  have hbij : (Σ e : M.Edge, {d : D // (⟦d⟧ : M.Edge) = e}) ≃ D :=
    Equiv.sigmaFibEquiv (Quotient.mk _)
  have hcard : Fintype.card D = 2 * Fintype.card M.Edge := by
    rw [← Fintype.card_congr hbij, Fintype.card_sigma]
    simp [hfib, Finset.sum_const, Finset.card_univ]
  omega

-- ============================================================
-- STEP 2: VERTEX + FACE COUNT (the hard part)
-- ============================================================
-- For a connected CMap, V + F = |D|/2 + 2.
-- Proof: induction on |D| using contraction-deletion.

/-- Connected combinatorial map: ⟨vertexPerm, edgePerm⟩ acts transitively -/
def IsConnected : Prop :=
  ∀ d₁ d₂ : D, ∃ (moves : List Bool),
    moves.foldl (fun d b => if b then M.edgePerm d else M.vertexPerm d) d₁ = d₂

/--
**For a connected CMap, V + F = |D|/2 + 2.**

Proof sketch (induction on |D|):

Base (|D| = 2): One edge {d₀, d₁}. Two sub-cases:
  - vertexPerm = id: V=2, F=1, 2+1 = 1+2 ✓
  - vertexPerm = swap: V=1, F=2, 1+2 = 1+2 ✓

Inductive step (|D| ≥ 4): pick dart d, let d' = edgePerm d.
  Case A: d and d' in different σ-orbits (edge between distinct vertices).
    Contract {d, d'}: V→V-1, E→E-1, F unchanged.
    IH on |D|-2 darts gives (V-1)+F = (|D|-2)/2 + 2.
    So V+F = |D|/2 + 2 ✓

  Case B: d and d' in same σ-orbit (loop at one vertex).
    Delete {d, d'}: V unchanged, E→E-1, F→F-1.
    IH on |D|-2 darts gives V+(F-1) = (|D|-2)/2 + 2.
    So V+F = |D|/2 + 2 ✓

The remaining implementation challenge: formally defining the
contracted/deleted CMap on D \ {d, d'} ≃ Fin (|D|-2) and showing
its orbit counts change as stated. This is the only remaining sorry.
-/
-- Helper: the group relation implies facePerm = vertexPerm⁻¹ * edgePerm⁻¹
lemma facePerm_eq_inv_mul :
    M.facePerm = M.vertexPerm⁻¹ * M.edgePerm⁻¹ := by
  have h := M.face_mul_edge_mul_vertex_eq_one
  have := congr_arg (· * M.vertexPerm⁻¹ * M.edgePerm⁻¹) h
  simp [mul_assoc, mul_inv_cancel, inv_mul_cancel] at this
  exact this

-- ============================================================
-- COUNTEREXAMPLE: THE TORUS MAP
-- ============================================================
-- The theorem "every connected CMap has V + F = |D|/2 + 2" is FALSE.
-- Connectivity alone does not imply Euler characteristic = 2.
-- A torus map is connected but has V - E + F = 0 (genus 1), not 2.
--
-- Torus CMap on Fin 4:
--   edgePerm:   (0 1)(2 3)  — two edges, E = 2
--   vertexPerm: (0 2 1 3)   — one vertex containing all 4 darts, V = 1
--   facePerm:   (0 2 1 3)⁻¹ * (0 1)(2 3) = 0→2→1→3→0 — one face, F = 1
--
-- V + F = 1 + 1 = 2  ≠  |D|/2 + 2 = 4/2 + 2 = 4
-- This is a torus: V - E + F = 1 - 2 + 1 = 0 = 2 - 2·genus where genus = 1.
--
-- The CMap is valid: all axioms satisfied (distinct_neighbors, involutive, etc.)
-- The CMap is connected: ⟨edgePerm, vertexPerm⟩ acts transitively on Fin 4.

/-- A valid connected CMap on the torus satisfying all CombinatorialMap axioms. -/
def torusCMap : CombinatorialMap (Fin 4) where
  -- edgePerm: (0 1)(2 3)
  edgePerm | ⟨0,_⟩ => ⟨1,by decide⟩ | ⟨1,_⟩ => ⟨0,by decide⟩
            | ⟨2,_⟩ => ⟨3,by decide⟩ | ⟨_,_⟩ => ⟨2,by decide⟩
  -- vertexPerm: (0 2 1 3) — one vertex, degree 4
  vertexPerm | ⟨0,_⟩ => ⟨2,by decide⟩ | ⟨1,_⟩ => ⟨3,by decide⟩
              | ⟨2,_⟩ => ⟨1,by decide⟩ | ⟨_,_⟩ => ⟨0,by decide⟩
  -- facePerm: σ⁻¹ ∘ α = (0 3 1 2) ∘ (0 1)(2 3) = 0→2→1→3→0, one face
  facePerm | ⟨0,_⟩ => ⟨2,by decide⟩ | ⟨1,_⟩ => ⟨3,by decide⟩
            | ⟨2,_⟩ => ⟨1,by decide⟩ | ⟨_,_⟩ => ⟨0,by decide⟩
  face_mul_edge_mul_vertex_eq_one    := by decide
  edgePerm_involutive                := by decide
  isEmpty_fixedPoints_edgePerm       := by
    refine ⟨fun ⟨d, hd⟩ => ?_⟩
    fin_cases d <;> simp [Function.fixedPoints] at hd

-- V = 1, E = 2, F = 1: verified by the kernel
example : Fintype.card (torusCMap.Vertex) = 1 := by native_decide
example : Fintype.card (torusCMap.Edge)   = 2 := by native_decide
example : Fintype.card (torusCMap.Face)   = 1 := by native_decide

-- The torus CMap is connected
theorem torusCMap_connected : torusCMap.IsConnected := by native_decide

-- Its Euler characteristic is 0, not 2 — it is NOT planar
-- V - E + F = 1 - 2 + 1 = 0  (genus 1 torus)
-- V + F = 2  ≠  |D|/2 + 2 = 4
example : torusCMap.eulerCharacteristic = 0 := by native_decide
example : ¬ torusCMap.IsPlanar          := by native_decide

-- ============================================================
-- CONCLUSION: THE CORRECT COMPLETENESS THEOREM
-- ============================================================
-- The theorem "every connected CMap has V + F = |D|/2 + 2" requires
-- a planarity / genus-0 hypothesis. Connectivity alone is insufficient.
--
-- The CORRECT completeness theorem is:
--   IsSpherical M → M.IsPlanar   (= eulerChar_of_spherical, already proved)
--
-- The remaining open question: which connected CMaps are IsSpherical?
-- This is equivalent to: which CMaps have genus 0?
-- The answer requires planarity theory (Jordan curve theorem or equivalent).
--
-- What we have proved:
-- ✓ euler_formula: PlanarGraph → V + F = E + 2  (complete)
-- ✓ edge_count_eq: |Edge| = |D|/2 for any CMap  (complete)
-- ✓ eulerChar_of_spherical: IsSpherical → IsPlanar  (complete)
-- ✓ Concrete examples: triangle, K₄ are IsPlanar  (complete)
-- ✓ Torus CMap: connected but NOT IsPlanar  (counterexample, complete)
-- ✗ "All sphere-embedded CMaps are IsSpherical" — requires planarity theory

end CombinatorialMap
