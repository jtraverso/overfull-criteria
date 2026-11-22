module

public import OverfullWork.CopyMultifanRotation

@[expose] public section


/-! # Kempe swaps preserve labelled-copy multifans

Only colored spokes are used in the fan conditions. A component swap
away from the root fixes these spokes, including their copy identities.
-/
namespace OverfullWork.CopyMultifan
open Finset ShannonColouring
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {ends : I → V × V} {s : Finset I} {k : ℕ} {c : I → Fin k}
variable {x : V} {e : I} {L : ℕ} {y : ℕ → V} {g : ℕ → I}
set_option maxHeartbeats 10000000

theorem swap_col_outside {α β : Fin k} {T : Set V} (hT : KempeClosed ends s c α β T)
    {h : I} (hh : h ∈ s) (hx : Incident ends h x) (hxT : x ∉ T) :
    kempeSwap ends c α β T h = c h := by
  by_cases hc : c h=α ∨ c h=β
  · rw [kempeSwap_mem_or hc,if_neg (fun hhT => hxT ((hT.mem_of_incident hh hc hx).mpr hhT))]
  · exact kempeSwap_of_not hc

theorem misses_swap_other {α β δ : Fin k} {T : Set V} (hT : KempeClosed ends s c α β T)
    (hδα : δ ≠ α) (hδβ : δ ≠ β) {v : V} (hm : Misses ends s c v δ) :
    Misses ends s (kempeSwap ends c α β T) v δ := by
  by_cases hv : v ∈ T
  · apply Misses.kempeSwap_of_mem hT hv
    simpa only [Equiv.swap_apply_of_ne_of_ne hδα hδβ] using hm
  · exact hm.kempeSwap_of_notMem hT hv

theorem IsFan.kempeSwap (hF : IsFan ends s c x e L y g) {α β : Fin k} {T : Set V}
    (hT : KempeClosed ends s c α β T) (hxT : x ∉ T)
    (hprev : ∀ j, j < L-1 → y j ∈ T → ¬Misses ends s c (y j) α ∧ ¬Misses ends s c (y j) β) :
    IsFan ends s (ShannonColouring.kempeSwap ends c α β T) x e L y g := by
  refine ⟨hF.pos,hF.start,hF.joins,hF.inj,hF.colored,?_⟩
  intro i hi0 hi
  obtain ⟨j,hji,hm⟩ := hF.step i hi0 hi
  have hcol : ShannonColouring.kempeSwap ends c α β T (g i)=c (g i) :=
    swap_col_outside hT (hF.colored i hi0 hi) ((hF.joins i hi).incident_iff.mpr (Or.inl rfl)) hxT
  refine ⟨j,hji,?_⟩
  rw [hcol]
  by_cases hjT : y j ∈ T
  · have hh := hprev j (by omega) hjT
    exact misses_swap_other hT (fun he => hh.1 (he ▸ hm)) (fun he => hh.2 (he ▸ hm)) hm
  · exact hm.kempeSwap_of_notMem hT hjT

theorem not_three_linked (hc : ProperOn ends s c) {α β : Fin k} {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : Misses ends s c u α ∨ Misses ends s c u β)
    (hv : Misses ends s c v α ∨ Misses ends s c v β)
    (hw : Misses ends s c w α ∨ Misses ends s c w β)
    (h1 : (kempeGraph ends s c α β).Reachable u v)
    (h2 : (kempeGraph ends s c α β).Reachable u w) : False := by
  have hd : ∀ z, (kempeGraph ends s c α β).degree z ≤ 2 := by
    intro z
    have hh := kempeGraph_degree_le hc z {α,β} (by
      intro i hi hiz hcol
      simpa only [mem_insert,mem_singleton] using hcol)
    exact hh.trans (by simpa only [card_singleton] using (card_insert_le α ({β} : Finset (Fin k))))
  have hend : ∀ z, (Misses ends s c z α ∨ Misses ends s c z β) →
      (kempeGraph ends s c α β).degree z ≤ 1 := by
    intro z hz
    rcases hz with hz|hz
    · have hh := kempeGraph_degree_le hc z {β} (by
        intro i hi hiz hcol
        rcases hcol with hcol|hcol
        · exact False.elim (hz i hi hiz hcol)
        · exact mem_singleton.mpr hcol)
      simpa only [card_singleton] using hh
    · have hh := kempeGraph_degree_le hc z {α} (by
        intro i hi hiz hcol
        rcases hcol with hcol|hcol
        · exact mem_singleton.mpr hcol
        · exact False.elim (hz i hi hiz hcol))
      simpa only [card_singleton] using hh
  exact not_three_ends_in_component _ hd huv huw hvw h1 h2 (hend u hu) (hend v hv) (hend w hw)

end OverfullWork.CopyMultifan
