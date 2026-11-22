module

public import OverfullWork.OsthusStadenSliceRegularity
public import OverfullWork.OsthusStadenNestedRefinement

@[expose] public section


/-! Assemble the disjoint initial slices from labelled nested refinements.
Exceptional edges are added after this step in §5.5–§5.9. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- All in- and out-neighbourhoods of the physical copies, with room for
any other input digraphs that need the same refinement. -/
noncomputable def arcProfiles {G : Type*} (D : G → Digraph V) : G × Bool × V → Finset V
  | (g,false,x) => inProfile (D g) x
  | (g,true,x) => outProfile (D g) x

theorem UniformProfileCell.inProfile {G : Type*} {D : G → Digraph V}
    {P A : Finset V} {k : ℕ} {ε : ℝ}
    (h : UniformProfileCell (arcProfiles D) P A k ε) (g : G) :
    UniformProfileCell (inProfile (D g)) P A k ε := fun x => h (g,false,x)

theorem UniformProfileCell.outProfile {G : Type*} {D : G → Digraph V}
    {P A : Finset V} {k : ℕ} {ε : ℝ}
    (h : UniformProfileCell (arcProfiles D) P A k ε) (g : G) :
    UniformProfileCell (outProfile (D g)) P A k ε := fun x => h (g,true,x)

/-- The initial slices are pairwise arc-disjoint, and every successor
pair is superregular in the physical slice. Both refine the same
original copy and preserve its prescribed density. -/
theorem prepared_slices_are_disjoint_and_superregular {U G : Type*} {r s p : ℕ}
    (D : G → Digraph V) (index : Fin r → U → G)
    (parent : Fin r → U → Finset V)
    (cell : Fin r → RefinedVertex U s p → Finset V)
    (label : Fin r → V → Option (RefinedVertex U s p))
    (σ : Fin r → Equiv.Perm U)
    (F : RefinedFactorIndex r s p → Equiv.Perm (RefinedVertex U s p))
    (k : ℕ) (ε θ η d : ℝ)
    (hProj : ∀ j a, (F j a).1.1 = σ j.1 a.1.1)
    (hSect : ∀ i a a' b b', (a,b) ≠ (a',b') → ∀ x, F (i,a,b) x ≠ F (i,a',b') x)
    (hCopy : ∀ i j, i ≠ j → ∀ u v, Disjoint (D (index i u)) (D (index j v)))
    (hParent : ∀ i u, IsSuperregularPair (D (index i u)) ε d (parent i u) (parent i (σ i u)))
    (hCell : ∀ i a, cell i a ⊆ parent i a.1.1 ∧
      (parent i a.1.1).card = k*(cell i a).card ∧
      UniformProfileCell (arcProfiles D) (parent i a.1.1) (cell i a) k θ)
    (hLabel : ∀ i a x, x ∈ cell i a → label i x = some a)
    (hk : 0 < k) (hθ : 0 ≤ θ) (hFloor : θ ≤ d-ε)
    (hη : max (2*ε) (ε+θ) ≤ η) (hη1 : η ≤ 1) (hScale : (k : ℝ)*ε ≤ η) :
    let slices := unwoundSlice (fun i u => D (index i u)) label F
    (∀ i j, i ≠ j → Disjoint (slices i) (slices j)) ∧
    ∀ j a, IsSuperregularPair (slices j) η d (cell j.1 a) (cell j.1 (F j a)) := by
  refine ⟨disjoint_unwoundSlices _ _ _ hCopy hSect,?_⟩
  intro j a
  have hA := hCell j.1 a
  have hB := hCell j.1 (F j a)
  rw [hProj] at hB
  apply superregular_unwoundSlice_pair _ _ _ _ a _ _ _ _
    (hLabel j.1 a) (hLabel j.1 (F j a))
  apply IsSuperregularPair.on_profile_cells _
    (hParent j.1 a.1.1) hA.1 hB.1 hA.2.1 hB.2.1 hk hk
    (hA.2.2.inProfile _) (hB.2.2.outProfile _) hθ hFloor hη hη1
  · have he : ((parent j.1 a.1.1).card : ℝ) = (k : ℝ)*(cell j.1 a).card := by exact_mod_cast hA.2.1
    rw [he,mul_right_comm,mul_comm _ η]
    exact mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg _)
  · have he : ((parent j.1 (σ j.1 a.1.1)).card : ℝ) = (k : ℝ)*(cell j.1 (F j a)).card :=
      by exact_mod_cast hB.2.1
    rw [he,mul_right_comm,mul_comm _ η]
    exact mul_le_mul_of_nonneg_right hScale (Nat.cast_nonneg _)

end OverfullWork.DirectedRobustExpansion
