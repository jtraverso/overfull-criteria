module

public import OverfullWork.DirectedPrefactorReach

@[expose] public section


/-! One growth step in Lo–Patel Lemma 5.2. Count the inadmissible arcs
by their sources and the missed robust neighbours by their targets. -/
namespace OverfullWork.DirectedPrefactor
open Finset DirectedRobustExpansion
open scoped Classical
variable {V : Type*} [Fintype V] {D : Digraph V} {x : V}
set_option maxHeartbeats 16000000

theorem missed_neighbours_budget (B : Prefactor D x → Finset V) (F₀ : Prefactor D x)
    (k r b : ℕ) (hB : ∀ F,(B F).card ≤ b) :
    let S := reachableTermini B F₀ k
    let T := reachableTermini B F₀ (k+1)
    let Y := ((neighbourhood D r S).erase x).filter (fun w => F₀.successor.symm w ∉ T)
    Y.card*r ≤ S.card*(b+k) := by
  dsimp only
  let S := reachableTermini B F₀ k
  let T := reachableTermini B F₀ (k+1)
  let Y := ((neighbourhood D r S).erase x).filter (fun w => F₀.successor.symm w ∉ T)
  change Y.card*r ≤ S.card*(b+k)
  have hIn : ∀ w ∈ Y,r ≤ inNeighbours D S w := by
    intro w hw
    exact (mem_filter.mp (mem_erase.mp (mem_filter.mp hw).1).2).2
  have hOut : ∀ v ∈ S,(Y.filter (D.Adj v)).card ≤ b+k := by
    intro v hv
    obtain ⟨F,hReach,hEnd⟩ := mem_reachableTermini.mp hv
    have hSub : Y.filter (D.Adj v) ⊆ (B F).image F₀.successor ∪ changed F₀ F := by
      intro w hw
      obtain ⟨hwy,ha⟩ := mem_filter.mp hw
      obtain ⟨hwx,_⟩ := mem_erase.mp (mem_filter.mp hwy).1
      have hn := (mem_filter.mp hwy).2
      by_cases he : F.successor.symm w=F₀.successor.symm w
      · apply mem_union_left
        have hForbidden : F₀.successor.symm w∈B F := by
          by_contra hh
          have hArc : D.Adj (terminus F) w := by
            rw [hEnd]
            exact ha
          have hStep := Reach.step hReach w hwx hArc (by simpa only [he] using hh)
          apply hn
          exact mem_reachableTermini.mpr ⟨_,hStep,(terminus_extend F w hwx hArc).trans he⟩
        exact mem_image.mpr ⟨_,hForbidden,F₀.successor.apply_symm_apply w⟩
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hwx,he⟩)
    have hu := card_union_le ((B F).image F₀.successor) (changed F₀ F)
    have hi := card_image_le (s:=B F) (f:=F₀.successor)
    have hc := changed_card_le hReach
    have hb := hB F
    have hs := card_le_card hSub
    omega
  calc
    Y.card*r = ∑ _w ∈ Y,r := by simp
    _ ≤ incidences D S Y := sum_le_sum hIn
    _ = ∑ v ∈ S,(Y.filter (D.Adj v)).card := by
      simp only [incidences,inNeighbours,card_filter]
      exact sum_comm
    _ ≤ ∑ _v ∈ S,(b+k) := sum_le_sum hOut
    _ = S.card*(b+k) := by simp

theorem growth_of_prefactor_termini (B : Prefactor D x → Finset V) (F₀ : Prefactor D x)
    (k r t b j : ℕ) (hB : ∀ F,(B F).card ≤ b)
    (hRobust : IsRobustAt D r t)
    (hlo : t ≤ (reachableTermini B F₀ k).card)
    (hhi : (reachableTermini B F₀ k).card+t ≤ Fintype.card V)
    (hBudget : (reachableTermini B F₀ k).card*(b+k) < (j+1)*r) :
    (reachableTermini B F₀ k).card+r ≤ (reachableTermini B F₀ (k+1)).card+j+1 := by
  let S := reachableTermini B F₀ k
  let T := reachableTermini B F₀ (k+1)
  let R := neighbourhood D r S
  let Y := (R.erase x).filter (fun w => F₀.successor.symm w ∉ T)
  have hLost : Y.card ≤ j := by
    have hCount : Y.card*r ≤ S.card*(b+k) := missed_neighbours_budget B F₀ k r b hB
    by_contra! hh
    exact (not_lt_of_ge ((Nat.mul_le_mul_right r (Nat.succ_le_of_lt hh)).trans hCount)) hBudget
  let G := (R.erase x).filter (fun w => F₀.successor.symm w ∈ T)
  have hG : G.card ≤ T.card := by
    rw [←card_image_of_injective G F₀.successor.symm.injective]
    apply card_le_card
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    exact (mem_filter.mp hw).2
  have hSplit : G.card+Y.card=(R.erase x).card := card_filter_add_card_filter_not _
  have hErase : R.card ≤ (R.erase x).card+1 := by
    by_cases hx : x∈R
    · rw [card_erase_of_mem hx]; omega
    · rw [erase_eq_of_notMem hx]; omega
  have hGrow := hRobust S hlo hhi
  change S.card+r ≤ T.card+j+1
  change S.card+r ≤ R.card at hGrow
  omega

end OverfullWork.DirectedPrefactor
