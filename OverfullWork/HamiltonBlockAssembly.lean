module

public import OverfullWork.OsthusStadenCorridors

@[expose] public section


/-! Assemble the separate batches of Osthus–Staden §5.11.
Across blocks, the sets of modified sources are disjoint and reserve
arcs are separate from the original factors. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V B : Type*} [Fintype V] [Fintype B]

omit [Fintype V] [Fintype B] in
theorem disjoint_successors_of_separate_merge_blocks (k : B → ℕ) (S : B → Finset V)
    (σ ρ : (Σ b, Fin (k b)) → Equiv.Perm V) (R : B → Digraph V)
    (hOriginal : ∀ i j, i ≠ j → ∀ v, σ i v ≠ σ j v)
    (hSame : ∀ b (i j : Fin (k b)), i ≠ j → ∀ v, ρ ⟨b,i⟩ v ≠ ρ ⟨b,j⟩ v)
    (hDis : ∀ b c, b ≠ c → Disjoint (S b) (S c))
    (hAway : ∀ i v, v ∉ S i.1 → ρ i v = σ i v)
    (hUse : ∀ i v, v ∈ S i.1 → (R i.1).Adj v (ρ i v))
    (hFresh : ∀ b i v, ¬(R b).Adj v (σ i v)) :
    ∀ i j, i ≠ j → ∀ v, ρ i v ≠ ρ j v := by
  intro ⟨b,i⟩ ⟨c,j⟩ hij v he
  by_cases hbc : b = c
  · subst c
    exact hSame b i j (fun h => hij (by cases h; rfl)) v he
  by_cases hb : v ∈ S b
  · have hc : v ∉ S c := fun h => disjoint_left.mp (hDis b c hbc) hb h
    have h := hUse ⟨b,i⟩ v hb
    rw [he,hAway ⟨c,j⟩ v hc] at h
    exact hFresh b ⟨c,j⟩ v h
  by_cases hc : v ∈ S c
  · have h := hUse ⟨c,j⟩ v hc
    rw [←he,hAway ⟨b,i⟩ v hb] at h
    exact hFresh c ⟨b,i⟩ v h
  exact hOriginal ⟨b,i⟩ ⟨c,j⟩ hij v
    ((hAway ⟨b,i⟩ v hb).symm.trans (he.trans (hAway ⟨c,j⟩ v hc)))

/-- A full pack of spanning successors in a regular host partitions
its arcs. This is the counting step after the final residue is absorbed. -/
noncomputable def hamilton_decomposition_of_full_pack (D : Digraph V) (r : ℕ)
    (σ : Fin r → Equiv.Perm V) (hr : ∀ v, outDegree D v = r)
    (hAdj : ∀ i v, D.Adj v (σ i v))
    (hDis : ∀ i j, i ≠ j → ∀ v, σ i v ≠ σ j v)
    (hCycle : ∀ i, HasSpanningCycle (fun v w => σ i v = w)) :
    DirectedHamiltonDecomposition D r := by
  let F (i : Fin r) : Digraph V := ⟨fun v w => σ i v = w⟩
  refine ⟨F,?_,?_,?_,hCycle⟩
  · intro i v w h
    change σ i v = w at h
    exact h ▸ hAdj i v
  · intro v w hw
    let A := (univ : Finset (Fin r)).image (fun i => σ i v)
    let B := (univ : Finset V).filter (fun x => D.Adj v x)
    have hSub : A ⊆ B := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact mem_filter.mpr ⟨mem_univ _,hAdj i v⟩
    have hA : A.card = r := by
      rw [show A = (univ : Finset (Fin r)).image (fun i => σ i v) from rfl,
        card_image_of_injective _ (fun i j h => by
          by_contra hn
          exact hDis i j hn v h),card_univ,Fintype.card_fin]
    have hB : B.card = r := hr v
    have hAB := eq_of_subset_of_card_le hSub (by omega)
    obtain ⟨i,_,hi⟩ := mem_image.mp (hAB ▸ mem_filter.mpr ⟨mem_univ _,hw⟩ : w ∈ A)
    refine ⟨i,hi,?_⟩
    intro j hj
    by_contra hn
    exact hDis j i hn v ((show σ j v = w from hj).trans hi.symm)
  · intro i v
    have hO : ((univ : Finset V).filter (fun w => σ i v = w)) = {σ i v} := by ext; simp [eq_comm]
    have hI : ((univ : Finset V).filter (fun w => σ i w = v)) = {(σ i).symm v} := by
      ext w
      simp [← (σ i).eq_symm_apply]
    constructor
    · simpa only [outDegree, F,card_singleton] using congrArg Finset.card hO
    · simpa only [inDegree,inNeighbours,F,card_singleton] using congrArg Finset.card hI

end OverfullWork.DirectedRobustExpansion
