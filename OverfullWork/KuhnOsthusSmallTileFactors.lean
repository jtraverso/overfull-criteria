module

public import OverfullWork.SuperregularTileFactors

@[expose] public section


/-! The two bounded patterns used in Kühn–Osthus Lemmas 4.13,
10.3 and Corollary 4.15. The shifts have distinct signed differences
on the required pairs of slots. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

def triangleTileEdges (a b : Fin 3) : Bool := decide (a < b)
def rectangleTileEdges (a b : Fin 4) : Bool := decide (a.val < 2 ∧ 2 ≤ b.val)

private def triangleTileShift : Fin 3 → Fin 7 := ![0,1,3]
private def rectangleTileShift : Fin 4 → Fin 15 := ![0,1,3,7]

private theorem triangleTileShift_valid : TileShiftPattern triangleTileEdges triangleTileShift := by
  constructor
  · change ∀ a b : Fin 3, (triangleTileEdges a b = true ∨ triangleTileEdges b a = true) →
      triangleTileShift a ≠ triangleTileShift b
    decide
  · change ∀ a b c d : Fin 3, (triangleTileEdges a b = true ∨ triangleTileEdges b a = true) →
      (triangleTileEdges c d = true ∨ triangleTileEdges d c = true) →
      triangleTileShift b - triangleTileShift a = triangleTileShift d - triangleTileShift c →
      a = c ∧ b = d
    decide

private theorem rectangleTileShift_valid : TileShiftPattern rectangleTileEdges rectangleTileShift := by
  constructor
  · change ∀ a b : Fin 4, (rectangleTileEdges a b = true ∨ rectangleTileEdges b a = true) →
      rectangleTileShift a ≠ rectangleTileShift b
    decide
  · change ∀ a b c d : Fin 4, (rectangleTileEdges a b = true ∨ rectangleTileEdges b a = true) →
      (rectangleTileEdges c d = true ∨ rectangleTileEdges d c = true) →
      rectangleTileShift b - rectangleTileShift a = rectangleTileShift d - rectangleTileShift c →
      a = c ∧ b = d
    decide

private def orderedTilePairs {p : ℕ} (R : Fin p → Fin p → Digraph V) (a b : Fin p) : Digraph V :=
  if a < b then R a b else if b < a then reverseArcs (R b a) else ⊥

omit [Fintype V] in
private theorem orderedTilePairs_symm {p : ℕ} (R : Fin p → Fin p → Digraph V)
    (a b : Fin p) (x y : V) : (orderedTilePairs R a b).Adj x y ↔ (orderedTilePairs R b a).Adj y x := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · simp only [orderedTilePairs,if_pos hab,if_neg (not_lt_of_gt hab)]
    rfl
  · simp [orderedTilePairs]
  · simp only [orderedTilePairs,if_pos hba,if_neg (not_lt_of_gt hba)]
    rfl

private theorem tile_factor_of_ordered_pairs {p h m : ℕ} (X : Fin p → Finset V)
    (E : Fin p → Fin p → Bool) (R : Fin p → Fin p → Digraph V)
    (shift : Fin p → Fin (h+1)) (S : TileShiftPattern E shift)
    (r : ℕ) (η δ small : ℝ)
    (hr : 0 < r) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : δ ≤ 1)
    (hSmall : 0 ≤ small) (hSeed : 0 ≤ δ*(m:ℝ)-small)
    (hAdd : ((p*r+p : ℕ):ℝ) < η^p*small)
    (hRepair : ((h*r+h : ℕ):ℝ) < η^h*(δ*(m:ℝ)-small))
    (hSize : ∀ a, (X a).card = m)
    (hDis : ∀ a b, a ≠ b → Disjoint (X a) (X b))
    (hOrder : ∀ a b, E a b = true → a < b)
    (hRects : ∀ a b, E a b = true → TileRectangleBound (R a b) (X a) (X b) r η)
    (hOut : ∀ a b, E a b = true → ∀ v ∈ X a, δ*(m:ℝ) ≤ (outTo (R a b) (X b) v:ℝ))
    (hIn : ∀ a b, E a b = true → ∀ v ∈ X b, δ*(m:ℝ) ≤ (inNeighbours (R a b) (X a) v:ℝ)) :
    Nonempty (LayeredTilePacking X E R m) := by
  let D := orderedTilePairs R
  have hRect (a b : Fin p) (hab : tilesTouch E a b) : TileRectangleBound (D a b) (X a) (X b) r η := by
    rcases hab with ha | hb
    · simpa only [D,orderedTilePairs,if_pos (hOrder a b ha)] using hRects a b ha
    · have hba := hOrder b a hb
      simpa only [D,orderedTilePairs,if_pos hba,if_neg (not_lt_of_gt hba)] using (hRects b a hb).reverse
  have hDegree (a b : Fin p) (hab : tilesTouch E a b) (v : V) (hv : v ∈ X a) :
      δ*(m:ℝ) ≤ (outTo (D a b) (X b) v:ℝ) := by
    rcases hab with ha | hb
    · simpa only [D,orderedTilePairs,if_pos (hOrder a b ha)] using hOut a b ha v hv
    · have hba := hOrder b a hb
      simpa only [D,orderedTilePairs,if_pos hba,if_neg (not_lt_of_gt hba),reverseArcs_outTo] using
        hIn b a hb v hv
  obtain ⟨P⟩ := exists_spanning_layered_tile_packing X E D shift S r η δ small hr hη hη₁ hδ
    hSmall hSeed hAdd hRepair hSize hDis hOrder (orderedTilePairs_symm R) hRect hDegree
  exact ⟨⟨P.vertices,P.mem,fun i a b hab => by
    simpa only [D,orderedTilePairs,if_pos (hOrder a b hab)] using P.edge i a b hab⟩⟩

/-- A factor of triangles with one vertex in each of three parts. -/
theorem exists_superregular_triangle_tile_factor {m : ℕ}
    (X : Fin 3 → Finset V) (R : Fin 3 → Fin 3 → Digraph V)
    (r : ℕ) (η δ small : ℝ)
    (hr : 0 < r) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : δ ≤ 1)
    (hSmall : 0 ≤ small) (hSeed : 0 ≤ δ*(m:ℝ)-small)
    (hAdd : ((3*r+3 : ℕ):ℝ) < η^3*small)
    (hRepair : ((6*r+6 : ℕ):ℝ) < η^6*(δ*(m:ℝ)-small))
    (hSize : ∀ a, (X a).card = m)
    (hDis : ∀ a b, a ≠ b → Disjoint (X a) (X b))
    (hRects : ∀ a b, a < b → TileRectangleBound (R a b) (X a) (X b) r η)
    (hOut : ∀ a b, a < b → ∀ v ∈ X a, δ*(m:ℝ) ≤ (outTo (R a b) (X b) v:ℝ))
    (hIn : ∀ a b, a < b → ∀ v ∈ X b, δ*(m:ℝ) ≤ (inNeighbours (R a b) (X a) v:ℝ)) :
    Nonempty (LayeredTilePacking X triangleTileEdges R m) := by
  have hOrder (a b : Fin 3) (hab : triangleTileEdges a b = true) : a < b := of_decide_eq_true hab
  exact tile_factor_of_ordered_pairs X triangleTileEdges R triangleTileShift triangleTileShift_valid
    r η δ small hr hη hη₁ hδ hSmall hSeed hAdd hRepair hSize hDis hOrder
    (fun a b h => hRects a b (hOrder a b h))
    (fun a b h => hOut a b (hOrder a b h))
    (fun a b h => hIn a b (hOrder a b h))

/-- A factor of oriented C₄ switches on four equal parts, joined by
the four cross pairs between slots {0,1} and {2,3}. -/
theorem exists_superregular_rectangle_tile_factor {m : ℕ}
    (X : Fin 4 → Finset V) (G : Digraph V) (r : ℕ) (η δ small : ℝ)
    (hr : 0 < r) (hη : 0 ≤ η) (hη₁ : η ≤ 1) (hδ : δ ≤ 1)
    (hSmall : 0 ≤ small) (hSeed : 0 ≤ δ*(m:ℝ)-small)
    (hAdd : ((4*r+4 : ℕ):ℝ) < η^4*small)
    (hRepair : ((14*r+14 : ℕ):ℝ) < η^14*(δ*(m:ℝ)-small))
    (hSize : ∀ a, (X a).card = m)
    (hDis : ∀ a b, a ≠ b → Disjoint (X a) (X b))
    (hRects : ∀ a b, rectangleTileEdges a b = true → TileRectangleBound G (X a) (X b) r η)
    (hOut : ∀ a b, rectangleTileEdges a b = true → ∀ v ∈ X a, δ*(m:ℝ) ≤ (outTo G (X b) v:ℝ))
    (hIn : ∀ a b, rectangleTileEdges a b = true → ∀ v ∈ X b, δ*(m:ℝ) ≤ (inNeighbours G (X a) v:ℝ)) :
    Nonempty (LayeredTilePacking X rectangleTileEdges (fun _ _ => G) m) := by
  have hOrder (a b : Fin 4) (hab : rectangleTileEdges a b = true) : a < b := by
    have he : a.val < 2 ∧ 2 ≤ b.val := of_decide_eq_true hab
    change a.val < b.val
    omega
  exact tile_factor_of_ordered_pairs X rectangleTileEdges (fun _ _ => G) rectangleTileShift
    rectangleTileShift_valid r η δ small hr hη hη₁ hδ hSmall hSeed hAdd hRepair hSize hDis
    hOrder hRects hOut hIn

end OverfullWork.DirectedRobustExpansion
