module

public import OverfullWork.KuhnOsthusAugmentedChordBalance
public import OverfullWork.KuhnOsthusWalkCoordinates

@[expose] public section


/-! Transport the augmented chord blocks to the ordered physical walk. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The same enumeration of the universal walk supplies the equal
parent multiplicities and the block balance used in Lemmas 9.5–9.7. -/
theorem indexed_walk_chord_blocks {I : Type*} [Fintype I] {L w : ℕ}
    (s : Equiv.Perm I) (l : I → List I) (root : I) (F : Fin L → Equiv.Perm I)
    (order : Fin w ≃ Fin L × I)
    (hStep : ∀ a, (order (finRotate w a)).2 = F (order a).1 (order a).2)
    (hEnd : ∀ j, (j :: l j).getLast? = some (s j))
    (hMult : ∀ x y, ((univ : Finset (Fin L)).filter (fun j => F j x = y)).card =
      elementaryChordMultiplicity s l x y +
        if s x = y then L - (∑ z, elementaryChordMultiplicity s l x z) else 0) :
    let parent (a : Fin w) := (order a).2
    (∀ x, (finiteSatisfying (fun a => parent a = x)).card = L) ∧
    ∃ owner : Fin w → I, ∀ j x,
      (∑ a, if owner a = j ∧ parent a = x then (1:ℕ) else 0) + (if j = x then 1 else 0) =
      (∑ a, if owner a = j ∧ parent (finRotate w a) = s x then (1:ℕ) else 0) +
        (if j = s x then 1 else 0) := by
  intro parent
  refine ⟨?_,?_⟩
  · intro x
    have hCard : (finiteSatisfying (fun a => parent a = x)).card = (univ : Finset (Fin L)).card := by
      apply card_bij (fun a _ => (order a).1)
      · exact fun _ _ => mem_univ _
      · intro a ha b hb h
        exact order.injective (Prod.ext h ((mem_finiteSatisfying.mp ha).trans (mem_finiteSatisfying.mp hb).symm))
      · intro i _
        have h := order.apply_symm_apply (i,x)
        exact ⟨order.symm (i,x),mem_finiteSatisfying.mpr (congrArg Prod.snd h),congrArg Prod.fst h⟩
    simpa only [card_univ,Fintype.card_fin] using hCard
  · obtain ⟨owner,hOwner⟩ := exists_augmented_chord_block_labels s l root F hEnd hMult
    refine ⟨owner ∘ order,fun j x => ?_⟩
    have hL : (∑ a, if owner (order a) = j ∧ parent a = x then (1:ℕ) else 0) =
        ∑ e : Fin L × I, if owner e = j ∧ e.2 = x then (1:ℕ) else 0 :=
      Equiv.sum_comp order (fun e => if owner e = j ∧ e.2 = x then (1:ℕ) else 0)
    have hR : (∑ a, if owner (order a) = j ∧ parent (finRotate w a) = s x then (1:ℕ) else 0) =
        ∑ e : Fin L × I, if owner e = j ∧ F e.1 e.2 = s x then (1:ℕ) else 0 := by
      have hParent (a : Fin w) : parent (finRotate w a) = F (order a).1 (order a).2 := hStep a
      simp only [hParent]
      exact Equiv.sum_comp order (fun e => if owner e = j ∧ F e.1 e.2 = s x then (1:ℕ) else 0)
    simpa only [Function.comp_apply,hL,hR] using hOwner j x

/-- Equal quarter sizes and equal parent multiplicities give the
exact coarse cluster sizes on the original vertices. -/
theorem physical_walk_quarter_cluster_card {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]
    (rank : V → J) (quarter : V → Fin 4) (parent : J → I) (Q : J × Fin 4 → Finset V)
    (ell a : ℕ) (hFibre : ∀ x, (finiteSatisfying (fun j => parent j = x)).card = ell)
    (hCover : ∀ v, ∃ j, v ∈ Q j) (hRank : ∀ j v, v ∈ Q j → rank v = j.1 ∧ quarter v = j.2)
    (hSize : ∀ j, (Q j).card = a) (x : I) :
    (finiteSatisfying (fun v => parent (rank v) = x)).card = 4*ell*a := by
  let A := (finiteSatisfying (fun j => parent j = x)) ×ˢ (univ : Finset (Fin 4))
  have hA : A.biUnion Q = finiteSatisfying (fun v => parent (rank v) = x) := by
    ext v
    simp only [mem_biUnion,mem_finiteSatisfying,A,mem_product,mem_univ,and_true]
    constructor
    · rintro ⟨j,hj,hv⟩
      rw [(hRank j v hv).1]
      exact hj
    · intro hv
      obtain ⟨j,hj⟩ := hCover v
      exact ⟨j,(hRank j v hj).1 ▸ hv,hj⟩
  have hDis : (↑A : Set (J × Fin 4)).PairwiseDisjoint Q := by
    intro i _ j _ hij
    exact disjoint_left.mpr (fun v hi hj => hij (Prod.ext
      (((hRank i v hi).1).symm.trans (hRank j v hj).1)
      (((hRank i v hi).2).symm.trans (hRank j v hj).2)))
  rw [←hA,card_biUnion hDis]
  simp only [hSize,sum_const,Nat.nsmul_eq_mul,A,card_product,hFibre,card_univ,Fintype.card_fin]
  rw [Nat.mul_comm ell 4]

end OverfullWork.DirectedRobustExpansion
