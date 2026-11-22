module

public import OverfullWork.UniformSubsetSampling

@[expose] public section


/-! Fixed-size concentration for a finite family of vertex profiles.
The same sample controls neighbourhoods and regularity-cell sizes.
The failure probability is an explicit cardinality ratio, including
sample sizes zero and the full vertex set. -/
namespace OverfullWork.UniformSubsetSampling
open Finset Real
open scoped Classical
variable {V : Type*} [Fintype V]
set_option maxHeartbeats 20000000

theorem probability_zero_size (P : Finset V → Prop) (hP : ¬P ∅) :
    probability 0 P=0 := by simp [probability,powersetCard_zero,hP]

theorem probability_full_size (P : Finset V → Prop) (hP : ¬P univ) :
    probability (Fintype.card V) P=0 := by
  have hh : (univ : Finset V).powersetCard (Fintype.card V)={univ} := by
    simpa only [card_univ] using powersetCard_self (univ : Finset V)
  simp [probability,hh,hP]

theorem additive_intersection_tail_all (k : ℕ) (hk : k ≤ Fintype.card V)
    (A : Finset V) (ε : ℝ) (hε : 0 < ε) :
    probability k (fun X => ε*(Fintype.card V:ℝ) ≤
      |((X ∩ A).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*(A.card:ℝ)|) ≤
      2*((Fintype.card V:ℝ)+1)*exp (-ε^2*(Fintype.card V:ℝ)/2) := by
  by_cases hn : Fintype.card V=0
  · have hh := probability_le_one k hk
      (fun X => ε*(Fintype.card V:ℝ) ≤ |((X ∩ A).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*(A.card:ℝ)|)
    have hBound : (1:ℝ) ≤ 2*((Fintype.card V:ℝ)+1)*exp (-ε^2*(Fintype.card V:ℝ)/2) := by simp [hn]
    exact hh.trans hBound
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hεn : 0 < ε*(Fintype.card V:ℝ) := mul_pos hε hnR
  by_cases hk0 : k=0
  · subst k
    rw [probability_zero_size _ (by simpa using (show ¬ε*(Fintype.card V:ℝ) ≤ 0 by linarith only [hεn]))]
    positivity
  by_cases hkN : k=Fintype.card V
  · subst k
    rw [probability_full_size _ (by simpa only [univ_inter,div_self hnR.ne',one_mul,sub_self,abs_zero] using (show ¬ε*(Fintype.card V:ℝ) ≤ 0 by linarith only [hεn]))]
    positivity
  exact additive_intersection_tail k (Nat.pos_of_ne_zero hk0) (lt_of_le_of_ne hk hkN) A ε hε

theorem probability_union_bound {I : Type*} [Fintype I] (k : ℕ) (P : I → Finset V → Prop) :
    probability k (fun X => ∃ i,P i X) ≤ ∑ i,probability k (P i) := by
  letI : DecidablePred (fun X : Finset V => ∃ i,P i X) := fun _ => Classical.propDecidable _
  let S := (univ : Finset V).powersetCard k
  have hPoint : ∀ X : Finset V,
      (if ∃ i,P i X then (1:ℕ) else 0) ≤ ∑ i,if P i X then 1 else 0 := by
    intro X
    by_cases h : ∃ i,P i X
    · obtain ⟨i,hi⟩ := h
      rw [if_pos ⟨i,hi⟩]
      have hh := single_le_sum (s:=univ) (f:=fun j => if P j X then (1:ℕ) else 0)
        (fun _ _ => Nat.zero_le _) (mem_univ i)
      simpa only [if_pos hi] using hh
    · simp only [if_neg h]
      exact Nat.zero_le _
  have hCount := sum_le_sum (s:=S) fun X _ => hPoint X
  rw [sum_comm] at hCount
  simp only [←card_filter] at hCount
  have hCountR : (((S.filter fun X => ∃ i,P i X).card):ℝ) ≤
      ∑ i,((S.filter (P i)).card:ℝ) := by exact_mod_cast hCount
  unfold probability
  simp only [div_eq_mul_inv]
  rw [←sum_mul]
  exact mul_le_mul_of_nonneg_right hCountR (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem profiles_tail {I : Type*} [Fintype I] (A : I → Finset V)
    (k : ℕ) (hk : k ≤ Fintype.card V) (ε : ℝ) (hε : 0 < ε) :
    probability k (fun X => ∃ i,ε*(Fintype.card V:ℝ) ≤
      |((X ∩ A i).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((A i).card:ℝ)|) ≤
      2*(Fintype.card I:ℝ)*((Fintype.card V:ℝ)+1)*exp (-ε^2*(Fintype.card V:ℝ)/2) := by
  have hh := probability_union_bound k
    (fun i X => ε*(Fintype.card V:ℝ) ≤
      |((X ∩ A i).card:ℝ)-((k:ℝ)/(Fintype.card V:ℝ))*((A i).card:ℝ)|)
  have hSum := sum_le_sum (s:=univ) fun i _ => additive_intersection_tail_all k hk (A i) ε hε
  simp only [sum_const,card_univ,nsmul_eq_mul] at hSum
  exact hh.trans (by nlinarith only [hSum])

end OverfullWork.UniformSubsetSampling
