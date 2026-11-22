module

public import OverfullWork.RobustRegularFactorization

@[expose] public section


/-! Robustness of a pure graph from the total loss bound of its
regularity partition, used for the bipartition in CMS Lemma 5.4. -/
namespace OverfullWork.RobustExpansion

open Finset SimpleGraph PrunedCore
open scoped Classical
universe u

/-- Adding simple edges preserves robust expansion with the same parameters. -/
theorem isRealRobust_mono_simple
    {V : Type u} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) (ν τ : ℝ) (hRob : IsRealRobust G ν τ) : IsRealRobust H ν τ := by
  intro S hLo hHi
  have hN : realNeighbourhood G ν S ⊆ realNeighbourhood H ν S := by
    intro v hv
    have hInc : neighboursIn G S v ≤ neighboursIn H S v := by
      rw [neighboursIn_eq_filter_card,neighboursIn_eq_filter_card]
      exact card_le_card fun w hw => mem_filter.mpr ⟨(mem_filter.mp hw).1,hGH (mem_filter.mp hw).2⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2.trans (by exact_mod_cast hInc)⟩
  have hCard : ((realNeighbourhood G ν S).card:ℝ) ≤ ((realNeighbourhood H ν S).card:ℝ) := by
    exact_mod_cast card_le_card hN
  exact (hRob S hLo hHi).trans hCard

/-- A global bound on deleted degree suffices for robust expansion of
the remaining graph. Vertices above the local loss threshold are
charged against the available robust-neighbourhood growth. -/
theorem isRealRobust_sdiff_of_total_degree_loss
    {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
    (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (ν ν' τ τ' : ℝ) (hν : ν' < ν) (hτ : τ ≤ τ')
    (hLoss : (∑ v, (F.degree v:ℝ)) ≤ ((ν-ν')*(Fintype.card V:ℝ))^2)
    (hRob : IsRealRobust G ν τ) : IsRealRobust (G \ F) ν' τ' := by
  let loss := (ν-ν')*(Fintype.card V:ℝ)
  have hPos : 0 < loss := mul_pos (sub_pos.mpr hν) (by exact_mod_cast Fintype.card_pos)
  let B := univ.filter (fun v => loss < (F.degree v:ℝ))
  have hB : (B.card:ℝ) ≤ loss := by
    apply (mul_le_mul_iff_of_pos_right hPos).mp
    calc
      _ = ∑ _v ∈ B, loss := by simp [nsmul_eq_mul]
      _ ≤ ∑ v ∈ B, (F.degree v:ℝ) :=
        sum_le_sum (fun v hv => (mem_filter.mp hv).2.le)
      _ ≤ ∑ v, (F.degree v:ℝ) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ _ := by simpa only [pow_two] using hLoss
  intro S hLo hHi
  have hWindow := mul_le_mul_of_nonneg_right hτ (Nat.cast_nonneg (α := ℝ) (Fintype.card V))
  have hGrow := hRob S (hWindow.trans hLo) (by linarith only [hWindow,hHi])
  have hKeep : realNeighbourhood G ν S \ B ⊆ realNeighbourhood (G \ F) ν' S := by
    intro v hv
    obtain ⟨hv,hvB⟩ := mem_sdiff.mp hv
    have hN := (mem_filter.mp hv).2
    have hDeg : (F.degree v:ℝ) ≤ loss := by simpa [B] using hvB
    have hLost :
        (neighboursIn G S v:ℝ) ≤ (neighboursIn (G \ F) S v:ℝ)+(F.degree v:ℝ) := by
      exact_mod_cast neighboursIn_le_sdiff_add_degree G F S v
    exact mem_filter.mpr ⟨mem_univ _,by
      dsimp only [loss] at hDeg
      linarith only [hN,hLost,hDeg]⟩
  have hCard : ((realNeighbourhood G ν S).card:ℝ) ≤
      ((realNeighbourhood (G \ F) ν' S).card:ℝ)+(B.card:ℝ) := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := realNeighbourhood G ν S) (t := B)).trans
      (Nat.add_le_add_right (card_le_card hKeep) _)
  dsimp only [loss] at hB
  linarith only [hGrow,hCard,hB]

end OverfullWork.RobustExpansion
