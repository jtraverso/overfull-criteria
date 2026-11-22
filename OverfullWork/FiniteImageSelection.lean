module

public import OverfullWork.BoundedForkSelection

@[expose] public section


/-! # Selecting distinct witnesses from a sufficiently large finite image -/
namespace OverfullWork.CaoChenForkSelection
open Finset
open SimpleGraph Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_distinct_pairs_of_image_card (T : Finset V) (f : V → V) (m : ℕ)
    (hm : m≤(T.image f).card) :
    ∃z t : Fin m → V,Function.Injective z ∧ Function.Injective t ∧
      ∀i,t i∈T ∧ f (t i)=z i := by
  let Z := T.image f
  let e : Fin m ↪ Z := (Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin m)≤Fintype.card Z by simpa using hm)).some
  have hp : ∀z : Z,∃t∈T,f t=z.val := fun z => mem_image.mp z.property
  choose pre hpreT hpreEq using hp
  have hz : Function.Injective (fun i : Fin m => (e i).val) := by
    intro i j hij
    exact e.injective (Subtype.ext hij)
  refine ⟨fun i => (e i).val,fun i => pre (e i),hz,?_,?_⟩
  · intro i j hij
    apply hz
    change (e i).val=(e j).val
    rw [←hpreEq (e i),←hpreEq (e j)]
    exact congrArg f hij
  · intro i
    exact ⟨hpreT (e i),hpreEq (e i)⟩

/-- Of two distinct leaves sharing a missing colour with the root,
at least one has a Kempe component avoiding the root. -/
theorem exists_unlinked_of_two_free_leaves {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (c : PEC G (Fin k)) {δ γ : Fin k} {a t₁ t₂ : V}
    (ha₁ : a≠t₁) (ha₂ : a≠t₂) (h₁₂ : t₁≠t₂)
    (ha : c.IsFree a δ) (h₁ : c.IsFree t₁ δ) (h₂ : c.IsFree t₂ δ) :
    ¬(c.kempeGraph δ γ).Reachable t₁ a ∨ ¬(c.kempeGraph δ γ).Reachable t₂ a := by
  by_cases hr : (c.kempeGraph δ γ).Reachable t₁ a
  · right
    intro hs
    exact not_three_linked c ha₁ ha₂ h₁₂ (Or.inl ha) (Or.inl h₁) (Or.inl h₂) hr.symm hs.symm
  · exact Or.inl hr

end OverfullWork.CaoChenForkSelection
