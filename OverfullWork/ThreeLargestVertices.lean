module

public import OverfullWork.MaximumCoreRoundBudget

@[expose] public section


/-! Choose three largest positive weights by a finite maximum, with all ties allowed. -/
namespace OverfullWork.ThreeLargestVertices
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

theorem exists_selection (Y : Finset V) (w : V → ℕ)
    (hActive : 3 ≤ (Y.filter (fun v => 0 < w v)).card) :
    ∃ U : Finset V, U ⊆ Y ∧ U.card=3 ∧ (∀ u ∈ U, 0 < w u) ∧
      ∀ u ∈ U, ∀ v ∈ Y, v ∉ U → w v ≤ w u := by
  have hY : 3 ≤ Y.card := hActive.trans (card_le_card (filter_subset _ _))
  obtain ⟨U₀,hU₀,hCard₀⟩ := exists_subset_card_eq hY
  let F := Y.powerset.filter (fun U => U.card=3)
  have hF : F.Nonempty := ⟨U₀,mem_filter.mpr ⟨mem_powerset.mpr hU₀,hCard₀⟩⟩
  obtain ⟨U,hU,hMax⟩ := F.exists_max_image (fun U => ∑ u ∈ U, w u) hF
  have hUY : U ⊆ Y := mem_powerset.mp (mem_filter.mp hU).1
  have hCard : U.card=3 := (mem_filter.mp hU).2
  have hTop : ∀ u ∈ U, ∀ v ∈ Y, v ∉ U → w v ≤ w u := by
    intro u hu v hv hvU
    let Z := insert v (U.erase u)
    have hvZ : v ∉ U.erase u := fun hh => hvU (mem_erase.mp hh).2
    have hZY : Z ⊆ Y := insert_subset hv ((erase_subset _ _).trans hUY)
    have hZCard : Z.card=3 := by simp only [Z,card_insert_of_notMem hvZ,card_erase_of_mem hu];omega
    have hZF : Z ∈ F := mem_filter.mpr ⟨mem_powerset.mpr hZY,hZCard⟩
    have hBound := hMax Z hZF
    have hSum := sum_erase_add U w hu
    change (∑ x ∈ insert v (U.erase u), w x) ≤ ∑ x ∈ U, w x at hBound
    rw [sum_insert hvZ] at hBound
    omega
  have hPositive : ∀ u ∈ U, 0 < w u := by
    intro u hu
    by_contra! hZero
    have hSub : Y.filter (fun v => 0 < w v) ⊆ U.erase u := by
      intro v hv
      have hvPos := (mem_filter.mp hv).2
      have hvU : v ∈ U := by
        by_contra hh
        have hLe := hTop u hu v (mem_filter.mp hv).1 hh
        omega
      exact mem_erase.mpr ⟨by intro he;subst v;omega,hvU⟩
    have hc := card_le_card hSub
    rw [card_erase_of_mem hu,hCard] at hc
    omega
  exact ⟨U,hUY,hCard,hPositive,hTop⟩

end OverfullWork.ThreeLargestVertices
