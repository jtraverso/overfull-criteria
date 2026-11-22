module

public import OverfullWork.BipartiteRobustTransport

@[expose] public section


/-! # Quantified changes of a balanced cut

The two one-sided difference bounds count exchanged vertices. They
control both neighbour discrepancy and the robust crossing after an
actual change of sides, as required in CMS Theorem 4.2, Case 2, Step 1.
-/
namespace OverfullWork.BalancedCutPerturbation
open SimpleGraph Finset PrunedCore RobustExpansion BipartiteRobustMargin
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 5000000

def Close (A B : Finset V) (h : ℕ) : Prop := (A\B).card ≤ h ∧ (B\A).card ≤ h

theorem difference_card_eq (A B : Finset V) (hcard : A.card = B.card) :
    (A\B).card = (B\A).card := by
  have ha := card_sdiff_add_card_inter A B
  have hb := card_sdiff_add_card_inter B A
  rw [inter_comm B A] at hb
  omega

theorem Close.compl {A B : Finset V} {h : ℕ} (hc : Close A B h) : Close Aᶜ Bᶜ h := by
  have h₁ : Aᶜ\Bᶜ = B\A := by ext x; simp; tauto
  have h₂ : Bᶜ\Aᶜ = A\B := by ext x; simp; tauto
  exact ⟨by rw [h₁]; exact hc.2, by rw [h₂]; exact hc.1⟩

theorem neighboursIn_le_add_difference (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (v : V) :
    neighboursIn G A v ≤ neighboursIn G B v + (A\B).card := by
  have hs : G.neighborFinset v ∩ A ⊆ (G.neighborFinset v ∩ B) ∪ (A\B) := by
    intro x hx
    by_cases hB : x ∈ B
    · exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hx).1,hB⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_inter.mp hx).2,hB⟩)
  exact (card_le_card hs).trans (card_union_le _ _)

theorem discrepancy_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (h : ℕ) (hc : Close A B h) (v : V) :
    |(neighboursIn G B v:ℝ)-(neighboursIn G Bᶜ v:ℝ)| ≤
      |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)| + 2*(h:ℝ) := by
  have h₁ : (neighboursIn G A v:ℝ) ≤ (neighboursIn G B v:ℝ)+(h:ℝ) := by
    exact_mod_cast (neighboursIn_le_add_difference G A B v).trans (Nat.add_le_add_left hc.1 _)
  have h₂ : (neighboursIn G B v:ℝ) ≤ (neighboursIn G A v:ℝ)+(h:ℝ) := by
    exact_mod_cast (neighboursIn_le_add_difference G B A v).trans (Nat.add_le_add_left hc.2 _)
  have h₃ : (neighboursIn G Aᶜ v:ℝ) ≤ (neighboursIn G Bᶜ v:ℝ)+(h:ℝ) := by
    exact_mod_cast (neighboursIn_le_add_difference G Aᶜ Bᶜ v).trans (Nat.add_le_add_left hc.compl.1 _)
  have h₄ : (neighboursIn G Bᶜ v:ℝ) ≤ (neighboursIn G Aᶜ v:ℝ)+(h:ℝ) := by
    exact_mod_cast (neighboursIn_le_add_difference G Bᶜ Aᶜ v).trans (Nat.add_le_add_left hc.compl.2 _)
  obtain ⟨hl,hu⟩ := abs_le.mp (le_refl |(neighboursIn G A v:ℝ)-(neighboursIn G Aᶜ v:ℝ)|)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem expandsTo_of_changed_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B A' B' : Finset V) (r t h : ℕ) (hcard : A.card = A'.card)
    (hSource : (A'\A).card ≤ h) (hTarget : (B\B').card ≤ h)
    (hr : 2*h ≤ r) (hexpand : ExpandsTo G A B r t) :
    ExpandsTo G A' B' (r-2*h) (t+h) := by
  intro S hSA hlo hhi
  let S₀ := S∩A
  have hS₀ : S₀ ⊆ A := inter_subset_right
  have hS₀S : S₀ ⊆ S := inter_subset_left
  have hdiff : S\A ⊆ A'\A := by
    intro x hx
    exact mem_sdiff.mpr ⟨hSA (mem_sdiff.mp hx).1,(mem_sdiff.mp hx).2⟩
  have hLoss : (S\A).card ≤ h := (card_le_card hdiff).trans hSource
  have hSize := card_sdiff_add_card_inter S A
  have hLow : t ≤ S₀.card := by dsimp only [S₀]; omega
  have hHigh : S₀.card+t ≤ A.card := by
    have hh := card_le_card hS₀S
    omega
  have hE := hexpand S₀ hS₀ hLow hHigh
  let N := neighbours G B r S₀
  have hNloss : (N\B').card ≤ h := by
    apply (card_le_card ?_).trans hTarget
    intro x hx
    have hxB : x ∈ B := (mem_filter.mp (mem_sdiff.mp hx).1).1
    exact mem_sdiff.mpr ⟨hxB,(mem_sdiff.mp hx).2⟩
  have hkeep : N∩B' ⊆ neighbours G B' (r-2*h) S := by
    intro v hv
    have hN := (mem_filter.mp (mem_inter.mp hv).1).2
    have hmono := neighboursIn_mono G hS₀S v
    exact mem_filter.mpr ⟨(mem_inter.mp hv).2,by omega⟩
  have hNsize := card_sdiff_add_card_inter N B'
  have hK := card_le_card hkeep
  change S₀.card+r ≤ N.card at hE
  change (S\A).card+S₀.card = S.card at hSize
  omega

theorem robust_of_close (G : SimpleGraph V) [DecidableRel G.Adj]
    (A A' : Finset V) (r t h : ℕ) (hcard : A.card = A'.card)
    (hc : Close A A' h) (hr : 2*h ≤ r) (hrobust : IsBipartiteRobustAt G A r t) :
    IsBipartiteRobustAt G A' (r-2*h) (t+h) := by
  have hcompl : Aᶜ.card = A'ᶜ.card := by simp only [card_compl]; omega
  have h₁ : Aᶜ\A'ᶜ = A'\A := by ext x; simp; tauto
  have h₂ : A'ᶜ\Aᶜ = A\A' := by ext x; simp; tauto
  exact ⟨expandsTo_of_changed_parts G A Aᶜ A' A'ᶜ r t h hcard hc.2
      (by rw [h₁]; exact hc.2) hr hrobust.1,
    expandsTo_of_changed_parts G Aᶜ A A'ᶜ A' r t h hcompl
      (by rw [h₂]; exact hc.1) hc.1 hr hrobust.2⟩

theorem robust_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (r t : ℕ) (hrobust : IsBipartiteRobustAt G A r t) :
    IsBipartiteRobustAt G Aᶜ r t := by
  simpa only [IsBipartiteRobustAt, compl_compl] using And.intro hrobust.2 hrobust.1

end OverfullWork.BalancedCutPerturbation
