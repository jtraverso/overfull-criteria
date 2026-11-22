module

public import OverfullWork.CopyMultifanKempe

@[expose] public section


/-! # Elementarity and Kempe linkage for labelled-copy multifans

Simultaneous induction follows the original multifan argument: rotation
excludes a common root color, while a component swap reduces a repeated
missing color or failed linkage to that exclusion. Parallel copies keep
their identities throughout the argument.
-/
namespace OverfullWork.CopyMultifan
open Finset ShannonColouring SimpleGraph
open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
variable {ends : I → V × V} {s : Finset I} {k : ℕ} {x : V} {e : I}
variable {y : ℕ → V} {g : ℕ → I}
set_option maxHeartbeats 12000000

theorem elementary (hloop : ∀ h, (ends h).1 ≠ (ends h).2) (he : e ∉ s)
    (hNo : ¬∃ c' : I → Fin k, ProperOn ends (insert e s) c')
    (hRoot : ∀ c : I → Fin k, ProperOn ends s c → ∃ a, Misses ends s c x a) :
    ∀ L : ℕ, ∀ c : I → Fin k, ProperOn ends s c → IsFan ends s c x e L y g →
      (∀ i, i < L → ∀ a, Misses ends s c x a → ¬Misses ends s c (y i) a) ∧
      (∀ i, i < L → ∀ j, j < L → i ≠ j → ∀ a, Misses ends s c (y i) a → ¬Misses ends s c (y j) a) ∧
      (∀ i, i < L → ∀ a b, Misses ends s c x a → Misses ends s c (y i) b →
        (kempeGraph ends s c a b).Reachable x (y i)) := by
  intro L
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro c hc hF
    have hA : ∀ i, i < L → ∀ a, Misses ends s c x a → ¬Misses ends s c (y i) a :=
      fun i hi a hx hy => hF.not_common_root hloop he hc hNo hi hx hy
    have hApart : ∀ i, i < L → ∀ j, j < L → i ≠ j → ∀ a,
        Misses ends s c (y i) a → ¬Misses ends s c (y j) a := by
      have key : ∀ i, i < L → ∀ j, j < i → ∀ a,
          Misses ends s c (y i) a → ¬Misses ends s c (y j) a := by
        intro i hi j hji a hia hja
        obtain ⟨b,hb⟩ := hRoot c hc
        have hFi := hF.prefix (m := i) (by omega) (by omega)
        obtain ⟨hAi,hAparti,hBi⟩ := ih i hi c hc hFi
        have hlink := hBi j hji b a hb hja
        have hxi : x ≠ y i := (hF.joins i hi).ne hloop
        have hxj : x ≠ y j := (hF.joins j (by omega)).ne hloop
        have hjiNe : y j ≠ y i := fun hh => by
          have hsame := hF.inj j (by omega) i hi hh
          omega
        have hnr : ¬(kempeGraph ends s c b a).Reachable (y i) x := fun hr =>
          not_three_linked hc hxj hxi hjiNe (Or.inl hb) (Or.inr hja) (Or.inr hia) hlink hr.symm
        let T : Set V := {z | (kempeGraph ends s c b a).Reachable (y i) z}
        have hT : KempeClosed ends s c b a T := kempeClosed_reachable hloop (y i)
        have hFi1 := hF.prefix (m := i+1) (by omega) (by omega)
        have hsw := hFi1.kempeSwap hT hnr (by
          intro q hq hr
          simp only [Nat.add_sub_cancel] at hq
          refine ⟨hAi q hq b hb,?_⟩
          intro hqa
          by_cases hqj : q=j
          · subst q
            exact hnr (hr.trans hlink.symm)
          · exact hAparti q hq j hji hqj a hqa hja)
        have hc' := hc.kempeSwap hT
        have hx' := hb.kempeSwap_of_notMem hT hnr
        have hy' : Misses ends s (kempeSwap ends c b a T) (y i) b := by
          apply Misses.kempeSwap_of_mem hT (Reachable.refl _)
          simpa only [Equiv.swap_apply_left] using hia
        exact hsw.not_common_root hloop he hc' hNo (by omega) hx' hy'
      intro i hi j hj hij a hia hja
      rcases lt_or_gt_of_ne hij with hij|hij
      · exact key j hj i hij a hja hia
      · exact key i hi j hij a hia hja
    refine ⟨hA,hApart,?_⟩
    intro i hi a b ha hb
    by_contra hnr
    have hnr' : ¬(kempeGraph ends s c a b).Reachable (y i) x := fun hr => hnr hr.symm
    let T : Set V := {z | (kempeGraph ends s c a b).Reachable (y i) z}
    have hT : KempeClosed ends s c a b T := kempeClosed_reachable hloop (y i)
    have hFi1 := hF.prefix (m := i+1) (by omega) (by omega)
    have hsw := hFi1.kempeSwap hT hnr' (by
      intro q hq _
      simp only [Nat.add_sub_cancel] at hq
      exact ⟨hA q (by omega) a ha,fun hqb => hApart q (by omega) i hi (by omega) b hqb hb⟩)
    have hx' := ha.kempeSwap_of_notMem hT hnr'
    have hy' : Misses ends s (kempeSwap ends c a b T) (y i) a := by
      apply Misses.kempeSwap_of_mem hT (Reachable.refl _)
      simpa only [Equiv.swap_apply_left] using hb
    exact hsw.not_common_root hloop he (hc.kempeSwap hT) hNo (by omega) hx' hy'

end OverfullWork.CopyMultifan
