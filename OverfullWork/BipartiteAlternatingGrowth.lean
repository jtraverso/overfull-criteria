module

public import OverfullWork.BipartiteRobustTransport
public import OverfullWork.RobustExpansionDeletion

@[expose] public section


/-! # Actual alternating-neighborhood growth after colored-edge deletion

The matching permutation preserves the current part and the eligible
set. Free crossing edges then grow into the opposite part. Deleted
degrees are charged only outside the forbidden set, so exceptional
centre rows need no false global simple-degree deletion bound.
This is a set-growth lemma, not an asserted alternating-path oracle.
-/
namespace OverfullWork.BipartiteRobustMargin
open SimpleGraph Finset PrunedCore RobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H F : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel F.Adj]
set_option maxHeartbeats 8000000

theorem neighbours_survive_outside (B W S : Finset V) (r d : ℕ)
    (hF : ∀ v, v ∉ W → F.degree v ≤ d) :
    neighbours H B r S\W ⊆ neighbours (H\F) B (r-d) S\W := by
  intro v hv
  obtain ⟨hvN,hvW⟩ := mem_sdiff.mp hv
  obtain ⟨hvB,hvDegree⟩ := mem_filter.mp hvN
  have hLoss := neighboursIn_le_sdiff_add_degree H F S v
  have hBound := hF v hvW
  exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨hvB,by omega⟩,hvW⟩

noncomputable def alternatingStep (B W : Finset V) (τ : Equiv.Perm V) (r d : ℕ) (X : Finset V) :
    Finset V := neighbours (H\F) B (r-d) (X.image τ)\W

theorem alternating_growth (A B W X : Finset V) (τ : Equiv.Perm V) (r d t : ℕ)
    (hExpand : ExpandsTo H A B r t) (hX : X ⊆ A\W)
    (hMate : ∀ v ∈ A\W, τ v ∈ A\W)
    (hF : ∀ v, v ∉ W → F.degree v ≤ d)
    (hLow : t ≤ X.card) (hHigh : X.card+t ≤ A.card) :
    (X.image τ).card=X.card ∧ X.image τ ⊆ A\W ∧
      alternatingStep H F B W τ r d X ⊆ B\W ∧
      X.card+r ≤ (alternatingStep H F B W τ r d X).card+W.card ∧
      ∀ v ∈ alternatingStep H F B W τ r d X,
        r-d ≤ neighboursIn (H\F) (X.image τ) v := by
  have hCard : (X.image τ).card=X.card := card_image_of_injective _ τ.injective
  have hSub : X.image τ ⊆ A\W := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hv
    exact hMate u (hX hu)
  have hRob := hExpand (X.image τ) (hSub.trans sdiff_subset)
    (by rwa [hCard]) (by rwa [hCard])
  have hSurvive := neighbours_survive_outside H F B W (X.image τ) r d hF
  have hDeleted := card_sdiff_add_card_inter (neighbours H B r (X.image τ)) W
  have hInter : (neighbours H B r (X.image τ)∩W).card ≤ W.card := card_le_card inter_subset_right
  have hSize := card_le_card hSurvive
  refine ⟨hCard,hSub,?_,?_,?_⟩
  · intro v hv
    obtain ⟨hvN,hvW⟩ := mem_sdiff.mp hv
    exact mem_sdiff.mpr ⟨(mem_filter.mp hvN).1,hvW⟩
  · change X.card+r ≤ (neighbours (H\F) B (r-d) (X.image τ)\W).card+W.card
    rw [hCard] at hRob
    omega
  · intro v hv
    exact (mem_filter.mp (mem_sdiff.mp hv).1).2

end OverfullWork.BipartiteRobustMargin
