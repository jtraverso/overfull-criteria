module

public import OverfullWork.UniformSubsetSampling

@[expose] public section

namespace OverfullWork.UniformSubsetSampling

open Finset
open scoped Classical

variable {V : Type*} [Fintype V]

/-- Fixing vertices in a subset leaves a uniform subset of the complement
with precisely the remaining number of places. -/
theorem probability_contains_eq (T : Finset V) {k : ℕ} (hT : T.card ≤ k) :
    probability k (fun X => T ⊆ X) =
      ((Fintype.card V - T.card).choose (k-T.card) : ℝ) / (Fintype.card V).choose k := by
  let _ : DecidablePred (fun X : Finset V => T ⊆ X) := fun _ => Classical.propDecidable _
  let P := ((univ : Finset V).powersetCard k).filter (fun X => T ⊆ X)
  let U := (univ : Finset V) \ T
  have hU : U.card = Fintype.card V - T.card := by
    simp [U,card_sdiff_of_subset (subset_univ T)]
  have hCount : P.card = (U.powersetCard (k-T.card)).card := by
    apply card_bij (fun X _ => X \ T)
    · intro X hX
      obtain ⟨hP,hTX⟩ := mem_filter.mp hX
      obtain ⟨hXV,hXk⟩ := mem_powersetCard.mp hP
      refine mem_powersetCard.mpr ⟨?_,by rw [card_sdiff_of_subset hTX,hXk]⟩
      intro v hv
      exact mem_sdiff.mpr ⟨hXV (mem_sdiff.mp hv).1,(mem_sdiff.mp hv).2⟩
    · intro X hX Y hY he
      have hXT := (mem_filter.mp hX).2
      have hYT := (mem_filter.mp hY).2
      calc
        X = X \ T ∪ T := (sdiff_union_of_subset hXT).symm
        _ = Y \ T ∪ T := congrArg (fun S => S ∪ T) he
        _ = Y := sdiff_union_of_subset hYT
    · intro Y hY
      obtain ⟨hYU,hYk⟩ := mem_powersetCard.mp hY
      have hDis : Disjoint Y T := by
        apply disjoint_left.mpr
        intro v hv
        exact (mem_sdiff.mp (hYU hv)).2
      have hCard : (Y ∪ T).card = k := by rw [card_union_of_disjoint hDis,hYk]; omega
      refine ⟨Y ∪ T,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hCard⟩,
        subset_union_right⟩,?_⟩
      ext v
      simp only [mem_sdiff,mem_union]
      constructor
      · rintro ⟨hv|hv,hn⟩
        · exact hv
        · exact (hn hv).elim
      · intro hv
        exact ⟨Or.inl hv,(mem_sdiff.mp (hYU hv)).2⟩
  unfold probability
  change (P.card : ℝ) / _ = _
  rw [hCount,card_powersetCard,hU]

private theorem choose_ratio_le (n k t : ℕ) (hk : k ≤ n) (ht : t ≤ k) :
    ((n-t).choose (k-t) : ℝ) / n.choose k ≤ ((k:ℝ)/n)^t := by
  induction t generalizing n k with
  | zero =>
    have h := (Nat.choose_pos hk).ne'
    simp [h]
  | succ t ih =>
    obtain ⟨k,rfl⟩ : ∃ k', k = k'+1 := ⟨k-1,by omega⟩
    obtain ⟨n,rfl⟩ : ∃ n', n = n'+1 := ⟨n-1,by omega⟩
    have hk' : k ≤ n := by omega
    have ht' : t ≤ k := by omega
    have hSmall := ih n k hk' ht'
    have hRatio : (k:ℝ)/n ≤ ((k:ℝ)+1)/((n:ℝ)+1) := by
      by_cases hn : n = 0
      · subst n
        have hk₀ : k = 0 := by omega
        simp [hk₀]
      · have hn' : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        apply (div_le_div_iff₀ hn' (by positivity : 0 < (n:ℝ)+1)).mpr
        have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk'
        nlinarith only [hkn]
    have hnChoose : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk'
    have hzChoose : (0:ℝ) < (n+1).choose (k+1) := by exact_mod_cast Nat.choose_pos hk
    have hStep : ((n+1).choose (k+1):ℝ)*((k:ℝ)+1) = ((n:ℝ)+1)*n.choose k := by
      have h := Nat.choose_mul (n := n+1) (k := k+1) (s := 1) (by omega)
      have h' : (n+1).choose (k+1)*(k+1) = (n+1)*n.choose k := by
        simpa only [Nat.choose_one_right,Nat.add_sub_cancel] using h
      exact_mod_cast h'
    rw [show n+1-(t+1)=n-t by omega, show k+1-(t+1)=k-t by omega]
    simp only [Nat.cast_add,Nat.cast_one,pow_succ]
    calc
      _ = ((k:ℝ)+1)/((n:ℝ)+1)*(((n-t).choose (k-t):ℝ)/n.choose k) := by
        field_simp [hnChoose.ne',hzChoose.ne',show (n:ℝ)+1 ≠ 0 by positivity]
        linear_combination (((n-t).choose (k-t):ℝ)) * hStep.symm
      _ ≤ ((k:ℝ)+1)/((n:ℝ)+1)*((k:ℝ)/n)^t := mul_le_mul_of_nonneg_left hSmall (by positivity)
      _ ≤ _ := by
        rw [mul_comm (((k:ℝ)+1)/((n:ℝ)+1))]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hRatio _) (by positivity)

/-- Inclusion probabilities for distinct vertices are bounded by the
product of the one-vertex sampling proportions. -/
theorem probability_contains_le (T : Finset V) {k : ℕ} (hk : k ≤ Fintype.card V) :
    probability k (fun X => T ⊆ X) ≤ ((k:ℝ)/Fintype.card V)^T.card := by
  by_cases hT : T.card ≤ k
  · rw [probability_contains_eq T hT]
    exact choose_ratio_le _ _ _ hk hT
  · let _ : DecidablePred (fun X : Finset V => T ⊆ X) := fun _ => Classical.propDecidable _
    have hEmpty : (((univ : Finset V).powersetCard k).filter (fun X => T ⊆ X)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro X hX
      have he := (mem_powersetCard.mp (mem_filter.mp hX).1).2
      exact hT ((card_le_card (mem_filter.mp hX).2).trans_eq he)
    rw [probability,hEmpty,card_empty,Nat.cast_zero,zero_div]
    positivity

end OverfullWork.UniformSubsetSampling
