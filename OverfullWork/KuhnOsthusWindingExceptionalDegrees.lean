module

public import OverfullWork.KuhnOsthusWindingExceptionalPacking
public import OverfullWork.KuhnOsthusExceptionalContraction

@[expose] public section


/-! Exact degrees of the original exceptional factors, with any number
of interval styles as in Kühn–Osthus Lemma 7.6. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedSpanningConfiguration
open scoped Classical
variable {V J : Type*} [Fintype V] [Fintype J]

/-- Inside a single winding factor the original intervals have
disjoint arcs, with a unique ordinary slot in each direction. -/
theorem winding_interval_factor_exact_semidegrees {G : Digraph V} {Z : Finset V}
    {f q : ℕ} (C : J × Fin (f*q) → Finset V) (hq : 0 < q) (hf : 2 ≤ f)
    (m : ℕ) (hSize : ∀ i, (C i).card = m)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ C i) :
    let next : Equiv.Perm (J × Fin f) := (Equiv.refl J).prodCongr (finRotate f)
    let U (i : J × Fin f) := univ.biUnion (fun p => C (i.1,intervalPosition i.2 p))
    let S (i : J × Fin f) := C (i.1,intervalPosition i.2 ⟨0,hq⟩)
    ∀ P : ∀ i, OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i)),
      Pairwise (fun i j => Disjoint (P i).digraph (P j).digraph) ∧
      ∀ x, let d := if x ∈ Z then Fintype.card J*f else 1
        inDegree (⨆ i, (P i).digraph) x = d ∧ outDegree (⨆ i, (P i).digraph) x = d := by
  intro next U S P
  obtain ⟨hPart,hApart,hUnion⟩ := winding_styled_interval_partition C hf hq m hDis hSize
  obtain ⟨hSlots,hIn⟩ := exceptional_interval_slot_owners next U S
    (fun i => (hPart i).2.1) (fun i => (hPart i).2.2.1) hApart
  have hU (x : V) (hx : x ∉ Z) : ∃ i, x ∈ U i := (hUnion x).mpr (hCover x hx)
  have hOut (x : V) (hx : x ∉ Z) : ∃! i, x ∈ (U i ∪ S (next i)) \ S (next i) := by
    obtain ⟨i,hi⟩ := hU x hx
    refine ⟨i,?_,?_⟩
    · change x ∈ (U i ∪ S (next i)) \ S (next i)
      rwa [hSlots i]
    intro j hj
    change x ∈ (U j ∪ S (next j)) \ S (next j) at hj
    rw [hSlots j] at hj
    by_contra hne
    exact disjoint_left.mp (hApart j i hne) hj hi
  obtain ⟨hDisj,hDeg⟩ := original_interval_factor_exact_semidegrees P hOut
    (fun x hx => hIn x (hU x hx))
  refine ⟨hDisj,fun x => ?_⟩
  simpa only [Fintype.card_prod,Fintype.card_fin] using hDeg x

/-- The packing of original exceptional systems on canonical winding
intervals has exact degrees. This yields the contribution of
the exceptional factors to (9.1). -/
theorem winding_exceptional_reserve_exact_semidegrees {G : Digraph V} {Z : Finset V}
    {f q r : ℕ} (C : J × Fin (f*q) → Finset V) (hq : 0 < q) (hf : 2 ≤ f)
    (m : ℕ) (hSize : ∀ i, (C i).card = m)
    (hDis : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hCover : ∀ x ∉ Z, ∃ i, x ∈ C i) :
    let next : Equiv.Perm (J × Fin f) := (Equiv.refl J).prodCongr (finRotate f)
    let U (i : J × Fin f) := univ.biUnion (fun p => C (i.1,intervalPosition i.2 p))
    let S (i : J × Fin f) := C (i.1,intervalPosition i.2 ⟨0,hq⟩)
    ∀ P : Fin r → ∀ i, OriginalInterval G Z (U i ∪ S (next i)) (S i) (S (next i)),
      let F (a : Fin r) := ⨆ i, (P a i).digraph
      Pairwise (fun a b => Disjoint (F a) (F b)) →
      ∀ x, let d := if x ∈ Z then (Fintype.card J*f)*r else r
        inDegree (⨆ a, F a) x = d ∧ outDegree (⨆ a, F a) x = d := by
  intro next U S P F hF x d
  have hDeg (a : Fin r) := (winding_interval_factor_exact_semidegrees C hq hf m hSize hDis hCover (P a)).2 x
  rw [inDegree_iSup_of_disjoint F hF,outDegree_iSup_of_disjoint F hF]
  change (∑ a, inDegree (⨆ i, (P a i).digraph) x) = d ∧
    (∑ a, outDegree (⨆ i, (P a i).digraph) x) = d
  by_cases hx : x ∈ Z
  · simp [d,hx,(hDeg _).1,(hDeg _).2,mul_left_comm,mul_comm]
  · simp [d,hx,(hDeg _).1,(hDeg _).2]

end OverfullWork.DirectedRobustExpansion
