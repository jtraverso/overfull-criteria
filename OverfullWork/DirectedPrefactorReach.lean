module

public import OverfullWork.DirectedPrefactor

@[expose] public section


/-! Bounded extension sequences and the predecessor disagreement
bound in the proof of Lo–Patel Lemma 5.2. -/
namespace OverfullWork.DirectedPrefactor
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}

inductive Reach (B : Prefactor D x → Finset V) (F₀ : Prefactor D x) :
    ℕ → Prefactor D x → Prop
  | zero : Reach B F₀ 0 F₀
  | keep {k F} : Reach B F₀ k F → Reach B F₀ (k+1) F
  | step {k F} (hF : Reach B F₀ k F) (z : V) (hz : z ≠ x)
      (ha : D.Adj (terminus F) z) (hB : F.successor.symm z ∉ B F) :
      Reach B F₀ (k+1) (extend F z hz ha)

noncomputable def changed (F₀ F : Prefactor D x) : Finset V :=
  univ.filter fun w => w ≠ x ∧ F.successor.symm w ≠ F₀.successor.symm w

theorem changed_extend_subset (F₀ F : Prefactor D x) (z : V) (hz : z ≠ x)
    (ha : D.Adj (terminus F) z) :
    changed F₀ (extend F z hz ha) ⊆ insert z (changed F₀ F) := by
  intro w hw
  obtain ⟨hwx,hwChange⟩ := (mem_filter.mp hw).2
  by_cases h : w=z
  · exact mem_insert.mpr (Or.inl h)
  · apply mem_insert.mpr
    right
    rw [predecessor_extend_same F z hz ha w hwx h] at hwChange
    exact mem_filter.mpr ⟨mem_univ _,hwx,hwChange⟩

theorem changed_card_le {B : Prefactor D x → Finset V} {F₀ F : Prefactor D x}
    {k : ℕ} (h : Reach B F₀ k F) : (changed F₀ F).card ≤ k := by
  induction h with
  | zero => simp [changed]
  | keep _ ih => exact ih.trans (Nat.le_succ _)
  | step _ z hz ha _ ih =>
      exact ((card_le_card (changed_extend_subset _ _ z hz ha)).trans
        (card_insert_le _ _)).trans (Nat.succ_le_succ ih)

noncomputable def reachableTermini (B : Prefactor D x → Finset V)
    (F₀ : Prefactor D x) (k : ℕ) : Finset V :=
  univ.filter fun v => ∃ F, Reach B F₀ k F ∧ terminus F=v

theorem mem_reachableTermini {B : Prefactor D x → Finset V}
    {F₀ : Prefactor D x} {k : ℕ} {v : V} :
    v∈reachableTermini B F₀ k ↔ ∃ F,Reach B F₀ k F ∧ terminus F=v := by
  simp [reachableTermini]

theorem reachableTermini_mono (B : Prefactor D x → Finset V) (F₀ : Prefactor D x)
    (k : ℕ) : reachableTermini B F₀ k ⊆ reachableTermini B F₀ (k+1) := by
  intro v hv
  obtain ⟨F,hF,rfl⟩ := mem_reachableTermini.mp hv
  exact mem_reachableTermini.mpr ⟨F,.keep hF,rfl⟩

end OverfullWork.DirectedPrefactor
