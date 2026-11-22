module

public import OverfullWork.TwoCentreStarCompletion

@[expose] public section


/-! Finite cut expansion from a simple core of order 2m.
Only cuts with at least two vertices on each side are covered. -/
namespace OverfullWork.DenseCoreCutBound
open SimpleGraph Finset
open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]
set_option maxHeartbeats 8000000

theorem internal_bound (R : MultiGraph W) (hSimple : ∀ u v, R.mult s(u,v) ≤ 1)
    (S : Finset W) : R.twiceInternal S ≤ S.card*(S.card-1) := by
  have hRow : ∀ v ∈ S, (∑ w ∈ S, R.mult s(v,w)) ≤ S.card-1 := by
    intro v hv
    have hh := sum_erase_add S (fun w => R.mult s(v,w)) hv
    rw [R.loopless _ (by simp),Nat.add_zero] at hh
    rw [←hh]
    calc
      _ ≤ ∑ _w ∈ S.erase v, 1 := sum_le_sum (fun _ _ => hSimple _ _)
      _ = _ := by simp [card_erase_of_mem hv]
  calc
    _ ≤ ∑ _v ∈ S, (S.card-1) := sum_le_sum hRow
    _ = _ := by simp

theorem concave_reserve (m k δ D c : ℕ) (hm : 3 ≤ m) (hk : 2 ≤ k) (hkm : k ≤ m)
    (hδ : m+2 ≤ δ) (hDδ : D+2 ≤ 2*δ) (hDm : D ≤ 3*m)
    (hCut : k*δ ≤ c+k*(k-1)) : D ≤ c := by
  have hProduct : 0 ≤ (k-2 : ℤ)*(m-k : ℤ) :=
    mul_nonneg (by omega) (by omega)
  have hScaled : 0 ≤ (k-2 : ℤ)*(m-k : ℤ)*(m-2 : ℤ) :=
    mul_nonneg hProduct (by omega)
  have hChord : (D:ℤ)*(m-2) ≤ (k:ℤ)*(δ-k+1)*(m-2) := by
    have hLeft : (D:ℤ) ≤ 2*(δ-1) := by omega
    have hRight : (D:ℤ) ≤ (m:ℤ)*(δ-m+1) := by
      have hMul : (3:ℤ)*m ≤ (m:ℤ)*(δ-m+1) := by
        nlinarith only [hδ]
      omega
    have hWeightLeft := mul_le_mul_of_nonneg_right hLeft (show (0:ℤ) ≤ m-k by omega)
    have hWeightRight := mul_le_mul_of_nonneg_right hRight (show (0:ℤ) ≤ k-2 by omega)
    nlinarith only [hWeightLeft,hWeightRight,hScaled]
  have hLower : (D:ℤ) ≤ (k:ℤ)*(δ-k+1) := by
    nlinarith only [hChord,hm]
  have hCutZ : (k:ℤ)*δ ≤ c+(k:ℤ)*(k-1) := by
    have hh : (k:ℤ)*δ ≤ (c:ℤ)+(k:ℤ)*((k-1:ℕ):ℤ) := by exact_mod_cast hCut
    have hCast : ((k-1:ℕ):ℤ)=(k:ℤ)-1 := by omega
    rwa [hCast] at hh
  nlinarith only [hLower,hCutZ]

theorem cut_bound_half (R : MultiGraph W) (m δ D : ℕ)
    (hm : 3 ≤ m) (hSimple : ∀ u v, R.mult s(u,v) ≤ 1)
    (hMin : ∀ v, δ ≤ R.degree v) (hδ : m+2 ≤ δ)
    (hDδ : D+2 ≤ 2*δ) (hDm : D ≤ 3*m)
    (S : Finset W) (hS : 2 ≤ S.card) (hHalf : S.card ≤ m) : D ≤ R.cutSize S := by
  have hSum : S.card*δ ≤ ∑ v ∈ S, R.degree v := by
    calc
      _ = ∑ _v ∈ S, δ := by simp
      _ ≤ _ := sum_le_sum (fun _ _ => hMin _)
  rw [R.sum_degree_eq_internal_add_cut S] at hSum
  have hInternal := internal_bound R hSimple S
  exact concave_reserve m S.card δ D (R.cutSize S) hm hS hHalf hδ hDδ hDm (by omega)

theorem cut_bound (R : MultiGraph W) (m δ D : ℕ) (hCard : Fintype.card W=2*m)
    (hm : 3 ≤ m) (hSimple : ∀ u v, R.mult s(u,v) ≤ 1)
    (hMin : ∀ v, δ ≤ R.degree v) (hδ : m+2 ≤ δ)
    (hDδ : D+2 ≤ 2*δ) (hDm : D ≤ 3*m)
    (S : Finset W) (hS : 2 ≤ S.card) (hSc : 2 ≤ Sᶜ.card) : D ≤ R.cutSize S := by
  by_cases hHalf : S.card ≤ m
  · exact cut_bound_half R m δ D hm hSimple hMin hδ hDδ hDm S hS hHalf
  · rw [←R.cutSize_compl S]
    apply cut_bound_half R m δ D hm hSimple hMin hδ hDδ hDm Sᶜ hSc
    rw [card_compl,hCard]
    omega

end OverfullWork.DenseCoreCutBound
