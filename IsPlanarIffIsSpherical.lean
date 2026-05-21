/-
  IsPlanar ↔ IsSpherical for connected CombinatorialMaps

  The key insight: any (V, E, F) with V ≥ 1 and V + F = E + 2 has a
  PlanarGraph witness. This is proved by simple induction on E:
  - E = 0: V = 1, F = 1 → point
  - E > 0, V > 1: use addLeaf (reduces to V-1, E-1, F)
  - E > 0, V = 1: use addEdge (reduces to 1, E-1, F-1)

  Therefore IsPlanar (= eulerCharacteristic = 2 = V - E + F)
  immediately implies IsSpherical (= ∃ PlanarGraph witness).

  Combined with eulerChar_of_spherical (IsSpherical → IsPlanar),
  this gives the full equivalence: IsPlanar ↔ IsSpherical.

  No Jordan curve theorem, no spanning trees, no topology needed.
-/
import CMapEuler
import Completeness

namespace PlanarGraph

/--
**Key construction**: for any V ≥ 1 and V + F = E + 2,
there exists a PlanarGraph V E F.

Proof: induction on E.
- E = 0: V = 1, F = 1 → `point`
- E > 0, V > 1: `addLeaf` from PlanarGraph (V-1) E F
- E > 0, V = 1: `addEdge` from PlanarGraph 1 E (F-1)
-/
def ofEuler : ∀ (v e f : ℕ), 1 ≤ v → v + f = e + 2 → PlanarGraph v e f
  | 1, 0, 1, _, _ => .point
  | _v+2, e+1, f, hv, hef =>
    .addLeaf (_v+1) e f (ofEuler (_v+1) e f (by omega) (by omega))
  | 1, e+1, _f+1, _, hef =>
    .addEdge 1 e _f (ofEuler 1 e _f (by omega) (by omega))
  | _, _, 0, _, hef => absurd hef (by omega)

-- Verify with concrete cases
example : ofEuler 1 0 1 (by omega) (by omega) = .point := rfl
example : ofEuler 2 1 1 (by omega) (by omega) =
          .addLeaf 1 0 1 .point := rfl
example : ofEuler 1 1 2 (by omega) (by omega) =
          .addEdge 1 0 1 .point := rfl

end PlanarGraph

namespace CombinatorialMap

variable {D : Type*} [Fintype D] [DecidableEq D] (M : CombinatorialMap D)

/-- The dart set is non-empty when the map is planar (eulerChar = 2). -/
lemma card_pos_of_isPlanar (hplanar : M.IsPlanar) : 0 < Fintype.card D := by
  by_contra h
  push_neg at h
  simp only [Nat.lt_one_iff] at h
  -- If |D| = 0, all orbit counts are 0, eulerChar = 0 ≠ 2
  have hV : Fintype.card M.Vertex = 0 := by
    simp [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨q, _⟩ => Quotient.inductionOn q (fun d => absurd (Fintype.card_eq_zero.mp h) (by simp))⟩
  have hE : Fintype.card M.Edge = 0 := by
    simp [← M.edge_count_eq, h]
  have hF : Fintype.card M.Face = 0 := by
    simp [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨q, _⟩ => Quotient.inductionOn q (fun d => absurd (Fintype.card_eq_zero.mp h) (by simp))⟩
  simp [IsPlanar, eulerCharacteristic, hV, hE, hF] at hplanar

/-- V ≥ 1 when the map is planar. -/
lemma vertex_pos_of_isPlanar (hplanar : M.IsPlanar) :
    1 ≤ Fintype.card M.Vertex := by
  have hD := M.card_pos_of_isPlanar hplanar
  rw [Fintype.card_pos_iff]
  -- M.Vertex is nonempty since D is nonempty
  obtain ⟨d⟩ := Fintype.card_pos.mp hD
  exact ⟨⟦d⟧⟩

/--
**Main completeness theorem**: for any connected CombinatorialMap,
`IsPlanar ↔ IsSpherical`.

The hard direction (IsPlanar → IsSpherical) follows immediately from
`PlanarGraph.ofEuler`: any (V, E, F) with V ≥ 1 and V + F = E + 2
has a PlanarGraph witness, making the CMap spherical by definition.

No topology, no Jordan curve theorem, no spanning trees needed.
-/
theorem isSpherical_iff_isPlanar (hconn : M.IsConnected) :
    M.IsSpherical ↔ M.IsPlanar := by
  constructor
  · -- IsSpherical → IsPlanar (already proved)
    exact M.eulerChar_of_spherical
  · -- IsPlanar → IsSpherical
    intro hplanar
    -- Unfold: eulerCharacteristic = V - E + F = 2
    simp only [IsPlanar, eulerCharacteristic] at hplanar
    -- So V + F = E + 2
    have hVF : Fintype.card M.Vertex + Fintype.card M.Face =
               Fintype.card M.Edge + 2 := by omega
    -- V ≥ 1 (since IsPlanar and non-empty D)
    have hV := M.vertex_pos_of_isPlanar (by
      simp [IsPlanar, eulerCharacteristic]; omega)
    -- Build the PlanarGraph witness from the Euler equation alone
    exact ⟨Fintype.card M.Vertex,
           Fintype.card M.Edge,
           Fintype.card M.Face,
           PlanarGraph.ofEuler _ _ _ hV hVF,
           rfl, rfl, rfl⟩

/-- Consequence: the torus CMap is connected but NOT IsSpherical. -/
theorem torusCMap_not_isSpherical : ¬ torusCMap.IsSpherical := by
  intro h
  exact torusCMap.eulerChar_of_spherical h |>.elim
    (by simp [IsPlanar, eulerCharacteristic]; native_decide)

end CombinatorialMap
