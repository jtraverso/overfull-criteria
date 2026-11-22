module

public import OverfullWork.CMSOperation41ChargedWords

@[expose] public section


/-! The singleton alternatives in S2.2. The charged vertex is
outside the active singleton. If every such candidate is maximum,
both outside matching endpoints already belong to the ordinary set. -/
namespace OverfullWork.CMSTrimmingRound

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [DecidableEq V]

theorem singleton_odd_pool_choice (X U : Finset V) (degree : V → ℕ) (d : ℕ)
    {w a b : V} (hw : w ∈ U) (hwX : w ∉ X) (ha : a ∈ X ∪ U) (hb : b ∈ X ∪ U)
    (haw : a ≠ w) (hbw : b ≠ w)
    (hLow : ∀ v ∈ U,degree v < d)
    (hParity : Odd (insert w (insert a (insert b X))).card) :
    (∃ x ∈ (insert a (insert b X)).erase w,degree x < d) ∨
      (a ∈ X ∧ b ∈ X ∧ Even X.card) := by
  by_cases h : ∃ x ∈ (insert a (insert b X)).erase w,degree x < d
  · exact Or.inl h
  right
  have haX : a ∈ X := by
    rcases mem_union.mp ha with ha' | ha'
    · exact ha'
    · exact (h ⟨a,mem_erase.mpr ⟨haw,mem_insert_self _ _⟩,hLow a ha'⟩).elim
  have hbX : b ∈ X := by
    rcases mem_union.mp hb with hb' | hb'
    · exact hb'
    · exact (h ⟨b,mem_erase.mpr ⟨hbw,mem_insert_of_mem (mem_insert_self _ _)⟩,hLow b hb'⟩).elim
  have hSet : insert a (insert b X) = X := by rw [insert_eq_of_mem hbX,insert_eq_of_mem haX]
  rw [hSet,card_insert_of_notMem hwX] at hParity
  obtain ⟨k,hk⟩ := hParity
  exact ⟨haX,hbX,⟨k,by omega⟩⟩

end OverfullWork.CMSTrimmingRound
