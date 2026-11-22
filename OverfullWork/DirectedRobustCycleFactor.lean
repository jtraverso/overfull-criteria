module

public import OverfullWork.RealDirectedRobustExpansion
public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section


/-! The directed 1-factor of Lo–Patel, Lemma 5.1, represented by its
successor permutation. Hall is applied to outgoing neighbourhoods. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

theorem exists_cycle_factor (D : Digraph V) (r t : ℕ)
    (hRobust : IsRobustAt D r t) (hr : 0 < r)
    (hIn : ∀ v,t < inDegree D v) (hOut : ∀ v,t ≤ outDegree D v) :
    ∃ σ : Equiv.Perm V,∀ v,D.Adj v (σ v) := by
  let N := fun v => univ.filter (D.Adj v)
  have hHall : ∀ S : Finset V,S.card ≤ (S.biUnion N).card := by
    intro S
    by_cases hSmall : S.card ≤ t
    · refine S.eq_empty_or_nonempty.elim (fun h => by simp [h]) ?_
      intro h
      obtain ⟨v,hv⟩ := h
      have hs : N v ⊆ S.biUnion N := fun x hx => mem_biUnion.mpr ⟨v,hv,hx⟩
      exact (hSmall.trans (hOut v)).trans (card_le_card hs)
    by_cases hLarge : Fintype.card V < S.card+t
    · have hAll : S.biUnion N=univ := by
        apply eq_univ_iff_forall.mpr
        intro v
        let I : Finset V := univ.filter (fun u => D.Adj u v)
        have hI : t < I.card := hIn v
        have he := card_union_add_card_inter S I
        have hb := card_le_univ (S∪I)
        obtain ⟨u,hu⟩ := card_pos.mp (show 0 < (S∩I).card by omega)
        obtain ⟨huS,huI⟩ := mem_inter.mp hu
        exact mem_biUnion.mpr ⟨u,huS,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp huI).2⟩⟩
      rw [hAll]
      exact card_le_univ S
    have hSub : neighbourhood D r S ⊆ S.biUnion N := by
      intro v hv
      have hp : 0 < inNeighbours D S v := hr.trans_le (mem_filter.mp hv).2
      obtain ⟨u,hu⟩ := card_pos.mp hp
      obtain ⟨huS,huD⟩ := mem_filter.mp hu
      exact mem_biUnion.mpr ⟨u,huS,mem_filter.mpr ⟨mem_univ _,huD⟩⟩
    exact (Nat.le_add_right _ _).trans
      ((hRobust S (by omega) (by omega)).trans (card_le_card hSub))
  obtain ⟨σ,hInject,hAdj⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨Equiv.ofBijective σ ⟨hInject,Finite.surjective_of_injective hInject⟩,
    fun v => (mem_filter.mp (hAdj v)).2⟩

/-- The real normalized version with an explicit unit of ceiling slack. -/
theorem exists_real_cycle_factor (D : Digraph V) (ν τ : ℝ)
    (hRobust : IsRealRobust D ν τ) (hν : 0 < ν*(Fintype.card V:ℝ)) (hτ : 0 ≤ τ)
    (hIn : ∀ v,τ*(Fintype.card V:ℝ)+1 ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,τ*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)) :
    ∃ σ : Equiv.Perm V,∀ v,D.Adj v (σ v) := by
  have hPos : 0 < ν := pos_of_mul_pos_left hν (Nat.cast_nonneg _)
  apply exists_cycle_factor D ⌈ν*(Fintype.card V:ℝ)⌉₊ ⌈τ*(Fintype.card V:ℝ)⌉₊
    (integer_of_real D ν τ hPos.le hRobust) (Nat.ceil_pos.mpr hν)
  · intro v
    exact_mod_cast (Nat.ceil_lt_add_one (mul_nonneg hτ (Nat.cast_nonneg _))).trans_le (hIn v)
  · intro v
    exact Nat.ceil_le.mpr (hOut v)

end OverfullWork.DirectedRobustExpansion
