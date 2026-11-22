module

public import OverfullWork.PairedPredecessorCounts

@[expose] public section


/-! # Finite layer growth and the terminal meeting choice

These are the two counting steps around CMS's backwards construction:
leave the robust size window after boundedly many increments, and
choose a terminal matching pair from two large sets in one part.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 16000000

theorem exists_large_layer (S : ℕ → Finset V) (m t g : ℕ) (hg : 0 < g)
    (hLow : t ≤ (S 0).card) (hBound : ∀ j, (S j).card ≤ m)
    (hGrow : ∀ j, t ≤ (S j).card → (S j).card+t ≤ m → (S j).card+g ≤ (S (j+1)).card) :
    ∃ j ≤ m/g+1, m < (S j).card+t := by
  by_contra! hn
  have hLower : ∀ j, j ≤ m/g+1 → t+j*g ≤ (S j).card := by
    intro j
    induction j with
    | zero => intro _;simpa using hLow
    | succ j ih =>
      intro hj
      have hPrev := ih (by omega)
      have hInc := hGrow j (by omega) (hn j (by omega))
      rw [Nat.succ_mul]
      omega
  have hh := hLower (m/g+1) le_rfl
  have hMax := hBound (m/g+1)
  have hDiv := Nat.lt_mul_div_succ m hg
  nlinarith only [hh,hMax,hDiv]

theorem exists_layered_meeting (τ : Equiv.Perm V) (hτ : ∀ v, τ (τ v)=v)
    (A X T : Finset V) (hX : X ⊆ A) (hT : T.image τ ⊆ A)
    (hLarge : A.card < X.card+T.card) : ∃ z ∈ X, τ z ∈ T := by
  have hCard : (T.image τ).card=T.card := card_image_of_injective _ τ.injective
  have hUnion : (X ∪ T.image τ).card ≤ A.card := card_le_card (union_subset hX hT)
  have hCount := card_union_add_card_inter X (T.image τ)
  have hMeet : (X ∩ T.image τ).Nonempty := by apply card_pos.mp;omega
  obtain ⟨z,hz⟩ := hMeet
  obtain ⟨hzX,hzT⟩ := mem_inter.mp hz
  obtain ⟨y,hy,he⟩ := mem_image.mp hzT
  refine ⟨z,hzX,?_⟩
  rw [←he,hτ]
  exact hy

end OverfullWork.PairedRoutes
