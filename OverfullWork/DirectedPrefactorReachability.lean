module

public import OverfullWork.DirectedPrefactorGrowth

@[expose] public section


/-! Reachability of almost all termini, Lo–Patel Lemma 5.2 with
explicit finite budgets for the first step and the subsequent growth. -/
namespace OverfullWork.DirectedPrefactor
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}

theorem first_termini_budget (B : Prefactor D x → Finset V) (F₀ : Prefactor D x) :
    outDegree D (terminus F₀) ≤ (reachableTermini B F₀ 1).card+(B F₀).card+1 := by
  let N : Finset V := univ.filter (D.Adj (terminus F₀))
  let Q := N.image F₀.successor.symm
  have hN : Q.card=outDegree D (terminus F₀) :=
    card_image_of_injective N F₀.successor.symm.injective
  have hSub : Q ⊆ (reachableTermini B F₀ 1 ∪ B F₀) ∪ {terminus F₀} := by
    intro w hw
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hw
    by_cases hx : z=x
    · subst z
      exact mem_union_right _ (mem_singleton_self _)
    by_cases hBad : F₀.successor.symm z ∈ B F₀
    · exact mem_union_left _ (mem_union_right _ hBad)
    have ha : D.Adj (terminus F₀) z := (mem_filter.mp hz).2
    exact mem_union_left _ (mem_union_left _ (mem_reachableTermini.mpr
      ⟨_,Reach.step Reach.zero z hx ha hBad,terminus_extend F₀ z hx ha⟩))
  have hCount := (card_le_card hSub).trans (card_union_le _ _)
  have hUnion := card_union_le (reachableTermini B F₀ 1) (B F₀)
  simp only [card_singleton] at hCount
  omega

theorem most_termini_reachable (B : Prefactor D x → Finset V) (F₀ : Prefactor D x)
    (r t b j g K : ℕ) (hB : ∀ F,(B F).card ≤ b)
    (hRobust : IsRobustAt D r t) (hOut : t+b+1 ≤ outDegree D (terminus F₀))
    (hBudget : Fintype.card V*(b+K) < (j+1)*r) (hGain : g+j+1 ≤ r)
    (hSteps : Fintype.card V < t+K*g) :
    Fintype.card V < (reachableTermini B F₀ (K+1)).card+t := by
  have hFirst := first_termini_budget B F₀
  have hB₀ := hB F₀
  have hIter : ∀ k ≤ K,
      Fintype.card V < (reachableTermini B F₀ (k+1)).card+t ∨
      t+k*g ≤ (reachableTermini B F₀ (k+1)).card := by
    intro k
    induction k with
    | zero =>
      intro _
      right
      simp only [zero_mul,add_zero,zero_add]
      omega
    | succ k ih =>
      intro hk
      have hMono := card_le_card (reachableTermini_mono B F₀ (k+1))
      rcases ih (by omega) with hDone|hLower
      · left; omega
      by_cases hDone : Fintype.card V < (reachableTermini B F₀ (k+1)).card+t
      · left; omega
      have hPay :
          (reachableTermini B F₀ (k+1)).card*(b+(k+1)) < (j+1)*r :=
        (Nat.mul_le_mul (card_le_univ _) (by omega)).trans_lt hBudget
      have hNext := growth_of_prefactor_termini B F₀ (k+1) r t b j hB hRobust
        (by omega) (by omega) hPay
      right
      rw [Nat.succ_mul]
      omega
  rcases hIter K le_rfl with h|h
  · exact h
  · have hn := card_le_univ (reachableTermini B F₀ (K+1))
    omega

end OverfullWork.DirectedPrefactor
