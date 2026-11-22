module

public import OverfullWork.KuhnOsthusExceptionalAssignment

@[expose] public section


/-! Count the conflicts between exceptional systems in Lemma 9.6.
A system occupies one style in an interval and may use its terminal
boundary, which belongs to the next interval. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V S : Type*} [Fintype S]

/-- Counting also the system itself gives at most three intervals'
worth of conflicts from the same style. -/
theorem card_exceptional_interval_conflicts {f t : ℕ}
    (s : Equiv.Perm (Fin f)) (cell : Fin f × S → Finset V)
    (Q : Fin f × (S × Fin t) → Finset V)
    (hCell : ∀ a b, a ≠ b → Disjoint (cell a) (cell b))
    (hQ : ∀ e, Q e ⊆ cell (e.1,e.2.1) ∪ cell (s e.1,e.2.1))
    (e : Fin f × (S × Fin t)) :
    (finiteSatisfying (fun e' => ¬ Disjoint (Q e) (Q e'))).card ≤ 3*t := by
  let F : Finset (Fin f) := {e.1,s e.1,s.symm e.1}
  let T := (F ×ˢ ({e.2.1} : Finset S)) ×ˢ (univ : Finset (Fin t))
  have hF : F.card ≤ 3 :=
    (card_insert_le _ _).trans (Nat.add_le_add_right ((card_insert_le _ _).trans_eq (by simp)) 1)
  have hT : T.card ≤ 3*t := by
    simp only [T,card_product,card_singleton, mul_one,card_univ,Fintype.card_fin]
    exact Nat.mul_le_mul_right t hF
  refine (card_le_card_of_injOn (fun e' : Fin f × (S × Fin t) => ((e'.1,e'.2.1),e'.2.2))
    (t := T) ?_ ?_).trans hT
  · intro e' he'
    obtain ⟨v,hv,hv'⟩ := not_disjoint_iff.mp ((mem_finiteSatisfying (p := fun e' => ¬ Disjoint (Q e) (Q e'))).mp he')
    have hWhere (p : Fin f × (S × Fin t)) (hp : v ∈ Q p) :
        ∃ j, (j = p.1 ∨ j = s p.1) ∧ v ∈ cell (j,p.2.1) := by
      rcases mem_union.mp (hQ p hp) with hh | hh
      · exact ⟨p.1,Or.inl rfl,hh⟩
      · exact ⟨s p.1,Or.inr rfl,hh⟩
    obtain ⟨i,hi,hci⟩ := hWhere e hv
    obtain ⟨j,hj,hcj⟩ := hWhere e' hv'
    have he : (i,e.2.1) = (j,e'.2.1) := by
      by_contra hn
      exact disjoint_left.mp (hCell _ _ hn) hci hcj
    have hStyle : e'.2.1 = e.2.1 := (congrArg Prod.snd he).symm
    have hIJ : i = j := congrArg Prod.fst he
    have hNear : e'.1 ∈ F := by
      change e'.1 ∈ ({e.1,s e.1,s.symm e.1} : Finset (Fin f))
      simp only [mem_insert,mem_singleton]
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi,hj] at hIJ
      · exact Or.inl hIJ.symm
      · exact Or.inr (Or.inr (s.eq_symm_apply.mpr hIJ.symm))
      · exact Or.inr (Or.inl hIJ.symm)
      · exact Or.inl (s.injective hIJ).symm
    exact mem_product.mpr ⟨mem_product.mpr ⟨hNear,mem_singleton.mpr hStyle⟩,mem_univ _⟩
  · rintro ⟨i,j,k⟩ _ ⟨i',j',k'⟩ _ he
    injection he with hij hk
    injection hij with hi hj
    exact Prod.ext hi (Prod.ext hj hk)

/-- Lemma 9.6 in the interval and style coordinates of the
exceptional factors. Boundaries may occur in both adjacent systems. -/
theorem kuhn_osthus_lemma_9_6_of_interval_cells {n f t : ℕ} [NeZero n]
    (s : Equiv.Perm (Fin f)) (H : Fin n → Finset V) (A : Fin f → Finset V)
    (cell : Fin f × S → Finset V) (Q : Fin f × (S × Fin t) → Finset V)
    (index : Fin n ≃ Fin f × (S × Fin t)) (a b : ℕ) (hn : 200 ≤ n)
    (ha : 100*a ≤ f) (hb : 100*b ≤ n) (ht : 300*t ≤ n)
    (hH : ∀ i j, residueCyclicClose 10 i j → Disjoint (H i) (H j))
    (hCellSub : ∀ e, cell e ⊆ A e.1)
    (hCell : ∀ a b, a ≠ b → Disjoint (cell a) (cell b))
    (hQ : ∀ e, Q e ⊆ cell (e.1,e.2.1) ∪ cell (s e.1,e.2.1))
    (hRow : ∀ i, (finiteSatisfying (fun j => ¬ Disjoint (H i) (A j ∪ A (s j)))).card ≤ a)
    (hCol : ∀ j, (finiteSatisfying (fun i => ¬ Disjoint (H i) (A j ∪ A (s j)))).card ≤ b) :
    ∃ assign : Fin n ≃ Fin f × (S × Fin t), (∀ i, Disjoint (H i) (Q (assign i))) ∧
      ∀ i j, residueCyclicClose 10 i j →
        Disjoint (H i ∪ Q (assign i)) (H j ∪ Q (assign j)) := by
  apply kuhn_osthus_lemma_9_6 H (fun j => A j ∪ A (s j)) Q index a b (3*t) hn ha hb
  · simpa only [←Nat.mul_assoc,Nat.reduceMul] using ht
  · exact hH
  · exact fun e => (hQ e).trans (union_subset_union (hCellSub _) (hCellSub _))
  · exact hRow
  · exact hCol
  · exact card_exceptional_interval_conflicts s cell Q hCell hQ

end OverfullWork.DirectedRobustExpansion
