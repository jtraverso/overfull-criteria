module

public import OverfullWork.CMSOperation41AuxiliaryLayout
public import Mathlib.Combinatorics.Hall.Basic

@[expose] public section


/-! Choose both connector vertices in every round. Separate systems
of distinct representatives bound the total usage at a vertex by two. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset
open scoped Classical

variable {V J : Type*} [Fintype V] [Fintype J] [DecidableEq V]

theorem exists_connectors_of_small_forbidden (B : J → Finset V)
    (hRoom : ∀ j,Fintype.card J+(B j).card+1 ≤ Fintype.card V) :
    ∃ x y : J ↪ V, (∀ j,x j ≠ y j ∧ x j ∉ B j ∧ y j ∉ B j) ∧
      ∀ v : V, ((univ : Finset (J × Bool)).filter
        (fun p => (if p.2 then y p.1 else x p.1) = v)).card ≤ 2 := by
  have hPick (A : J → Finset V) (hAvailable : ∀ j,Fintype.card J ≤ (A j).card) :
      ∃ x : J ↪ V, ∀ j,x j ∈ A j := by
    have hHall : ∀ S : Finset J,S.card ≤ (S.biUnion A).card := by
      intro S
      rcases S.eq_empty_or_nonempty with rfl|⟨j,hj⟩
      · simp
      · exact (card_le_univ S).trans ((hAvailable j).trans
          (card_le_card (fun v hv => mem_biUnion.mpr ⟨j,hj,hv⟩)))
    obtain ⟨x,hInject,hMem⟩ := (all_card_le_biUnion_card_iff_exists_injective A).mp hHall
    exact ⟨⟨x,hInject⟩,hMem⟩
  obtain ⟨x,hx⟩ := hPick (fun j => (B j)ᶜ) (fun j => by
    rw [card_compl]
    have hh := hRoom j
    omega)
  obtain ⟨y,hy⟩ := hPick (fun j => (insert (x j) (B j))ᶜ) (fun j => by
    rw [card_compl]
    have hCard := card_insert_le (x j) (B j)
    have hh := hRoom j
    omega)
  refine ⟨x,y,?_,?_⟩
  · intro j
    have hy' := mem_compl.mp (hy j)
    exact ⟨fun h => hy' (by simp [h]),mem_compl.mp (hx j),fun h => hy' (mem_insert_of_mem h)⟩
  · intro v
    have hOne (z : J ↪ V) : ((univ : Finset J).filter (fun j => z j = v)).card ≤ 1 := by
      apply card_le_one.mpr
      intro j hj k hk
      exact z.injective ((mem_filter.mp hj).2.trans (mem_filter.mp hk).2.symm)
    have h := Nat.add_le_add (hOne y) (hOne x)
    simp only [card_filter] at h ⊢
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool,if_true,if_false,sum_add_distrib]
    exact h

end OverfullWork.DirectedSpanningConfiguration
