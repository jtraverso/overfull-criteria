module

public import OverfullWork.KuhnOsthusCommonWoundFactors
public import OverfullWork.KuhnOsthusLemma86

@[expose] public section


/-! Pass the first application of Lemma 7.6 to Lemma 8.6 on the
very same fifty-style cells. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Recover the style label of each ordinary vertex from its unique cell.
The preprocessing factors have exactly the same original arcs as
the winding intervals. In particular the degrees and disjointness
needed by Lemma 8.6 are inherited from the chosen intervals. -/
theorem winding_preprocessing_inputs {V : Type*} [Fintype V] {l q r : ℕ}
    (G : Digraph V) (Z : Finset V) (C : Fin 50 × Fin (l*q) → Finset V)
    (m : ℕ) (hl : 2 ≤ l) (hq : 0 < q)
    (hSize : ∀ i, (C i).card = m)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hOrd : ∀ i, Disjoint (C i) Z)
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ C i) :
    let next := (Equiv.refl (Fin 50)).prodCongr (finRotate l)
    let U (j : Fin 50 × Fin l) :=
      (univ : Finset (Fin q)).biUnion (fun i => C (j.1,intervalPosition j.2 i))
    let S (j : Fin 50 × Fin l) := C (j.1,intervalPosition j.2 ⟨0,hq⟩)
    ∀ F : Fin r → ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
    Pairwise (fun i j => Disjoint (⨆ a, (F i a).digraph) (⨆ a, (F j a).digraph)) →
    ∃ (label : V → Fin 50) (Q : Fin r → OriginalExceptionalFactor label Z l),
      (∀ i x, x ∈ C i → label x = i.1) ∧
      (∀ i, (Q i).digraph = ⨆ j, (F i j).digraph) ∧ (∀ i, (Q i).digraph ≤ G) ∧
      Pairwise (fun i j => Disjoint (Q i).digraph (Q j).digraph) ∧
      ∀ x ∉ Z, inDegree (⨆ i, (Q i).digraph) x = r ∧ outDegree (⨆ i, (Q i).digraph) x = r := by
  classical
  intro next U S F hF
  let owner (x : V) (hx : x ∉ Z) := (hCover x hx).choose
  let label (x : V) : Fin 50 := if hx : x ∉ Z then (owner x hx).1 else 0
  have hLabel (i : Fin 50 × Fin (l*q)) (x : V) (hx : x ∈ C i) : label x = i.1 := by
    have hz : x ∉ Z := fun hz => disjoint_left.mp (hOrd i) hx hz
    have hOwner : x ∈ C (owner x hz) := (hCover x hz).choose_spec
    have he : owner x hz = i := by
      by_contra h
      exact disjoint_left.mp (hDis (owner x hz) i h) hOwner hx
    simp only [label, dif_pos hz, he]
  obtain ⟨Q,hQ,hLe⟩ :=
    assemble_preprocessing_factors_from_wound_intervals G Z label C m hl hq
      hDis hCover hSize hLabel F
  refine ⟨label,Q,hLabel,hQ,hLe,?_,?_⟩
  · intro i j hij
    rw [hQ,hQ]
    exact hF hij
  · intro x hx
    simp only [hQ]
    simpa only [if_neg hx] using
      winding_exceptional_reserve_exact_semidegrees C hq hl m hSize hDis hCover F hF x

end OverfullWork.DirectedRobustExpansion
