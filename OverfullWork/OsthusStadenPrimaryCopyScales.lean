module

public import OverfullWork.KuhnOsthusDivisibleClusters
public import OverfullWork.OsthusStadenQuotientCopies
public import OverfullWork.OsthusStadenH1Assembly

@[expose] public section


/-! Counts and scales for the physical copies of the primary reduced factors. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion
open scoped Classical

variable {I : Type*} [Fintype I]

theorem reducedCopy_incident_count (M : I → I → ℕ) (s : Bool) (i : I) :
    (incidentCopySet (fun e : ReducedCopy M => e.1.1) (fun e => e.1.2) s i).card =
      if s then ∑ j,M i j else ∑ j,M j i := by
  have h (p : I × I → Prop) :
      ((univ : Finset (ReducedCopy M)).filter (fun e => p e.1)).card =
        ∑ ij : I × I, if p ij then M ij.1 ij.2 else 0 := by
    rw [card_eq_sum_ones,sum_filter,Fintype.sum_sigma]
    apply sum_congr rfl
    intro ij _
    by_cases hp : p ij <;> simp [hp]
  cases s
  · simp only [incidentCopySet,copyEndpoint,Bool.false_eq_true,ite_false]
    rw [h (fun q => q.2 = i),Fintype.sum_prod_type]
    simp only [sum_ite_eq',mem_univ,if_true]
  · simp only [incidentCopySet,copyEndpoint,ite_true]
    rw [h (fun q => q.1 = i),Fintype.sum_prod_type]
    have h' (j : I) : (∑ l : I, if j = i then M j l else 0) =
        if j = i then ∑ l : I,M j l else 0 := by
      by_cases he : j = i <;> simp [he]
    simp only [h',sum_ite_eq',mem_univ,if_true]

theorem reducedCopy_parallel_count (M : I → I → ℕ) (i j : I) :
    ((univ : Finset (ReducedCopy M)).filter (fun e => e.1 = (i,j))).card = M i j := by
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_sigma]
  have h (ij : I × I) :
      (∑ _ : Fin (M ij.1 ij.2), if ij = (i,j) then (1:ℕ) else 0) =
        if ij = (i,j) then M ij.1 ij.2 else 0 := by
    by_cases h : ij = (i,j) <;> simp [h]
  simp only [h,sum_ite_eq',mem_univ,if_true]

/-- Remove at least a prescribed fraction and round the retained size
down to a multiple of the subdivision size. The rounding spends at
most a second copy of the fractional budget. -/
theorem exists_primary_copy_trim (σ : ℝ) (b : ℕ) (hσ : 0 < σ)
    (hσSmall : σ ≤ 1/4) (hb : 0 < b) :
    ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      ∃ t m : ℕ, t+m = M ∧ b ∣ m ∧ M ≤ 2*m ∧
        σ*(M:ℝ) ≤ (t:ℝ) ∧ (t:ℝ) ≤ 2*σ*(M:ℝ) := by
  refine ⟨⌈(b:ℝ)/σ⌉₊,?_⟩
  intro M hM
  have hReq : (b:ℝ) ≤ σ*(M:ℝ) := by
    have hM' : (↑⌈(b:ℝ)/σ⌉₊:ℝ) ≤ (M:ℝ) := by exact_mod_cast hM
    have h := (div_le_iff₀ hσ).mp ((Nat.le_ceil ((b:ℝ)/σ)).trans hM')
    simpa only [mul_comm] using h
  let t₀ := ⌈σ*(M:ℝ)⌉₊
  have h₀ : t₀ ≤ M := Nat.ceil_le.mpr (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith only [hσSmall]))
  obtain ⟨hDiv,hLe,_,hLoss⟩ :=
    round_down_cluster_size M t₀ b hb h₀
  let m := ((M-t₀)/b)*b
  let t := M-m
  have ht : t+m = M := Nat.sub_add_cancel (hLe.trans (Nat.sub_le _ _))
  have hL : σ*(M:ℝ) ≤ (t:ℝ) := (Nat.le_ceil _).trans (by
    have hh : t₀ ≤ t := by
      change m ≤ M-t₀ at hLe
      have := h₀
      omega
    exact_mod_cast hh)
  have hU : (t:ℝ) ≤ 2*σ*(M:ℝ) := by
    have ha : (t+1:ℕ) ≤ t₀+b := by
      exact hLoss
    have hR : (t:ℝ)+1 ≤ (t₀:ℝ)+(b:ℝ) := by exact_mod_cast ha
    have hc := Nat.ceil_lt_add_one (show 0 ≤ σ*(M:ℝ) by positivity)
    change (t₀:ℝ) < σ*(M:ℝ)+1 at hc
    linarith only [hR,hc,hReq]
  have hhalf : M ≤ 2*m := by
    have htR : (t:ℝ)+(m:ℝ) = (M:ℝ) := by exact_mod_cast ht
    have hσM := mul_le_mul_of_nonneg_right hσSmall (Nat.cast_nonneg M : (0:ℝ) ≤ _)
    have hh : (M:ℝ) ≤ 2*(m:ℝ) := by linarith only [htR,hσM,hU]
    exact_mod_cast hh
  exact ⟨t,m,ht,hDiv,hhalf,hL,hU⟩

end OverfullWork.DirectedRegularPairs
