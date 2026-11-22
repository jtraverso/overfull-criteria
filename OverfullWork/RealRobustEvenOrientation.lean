module

public import OverfullWork.EvenRegularOrientation
public import OverfullWork.RealRobustRegularFactor
public import OverfullWork.RealRobustOrientation
public import OverfullWork.MaximumMatchingPeeling
public import Mathlib.Combinatorics.Digraph.Orientation

@[expose] public section


/-! Kühn–Osthus, Applications Lemma 3.6. Preserve a sparse robust
regular factor and balance the orientation of its even-regular complement. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset SimpleGraph
open scoped Classical
universe u

theorem exists_real_robust_even_regular_orientation (ν τ α : ℝ)
    (hν : 0 < ν) (hν1 : ν ≤ 1) (hτ : 0 ≤ τ) (hτα : 64*τ ≤ α) (hα : 0 < α) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ N : ℕ, ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ),
      N ≤ Fintype.card V → RobustExpansion.IsRealRobust G ν τ →
      α*(Fintype.card V:ℝ) ≤ 2*(m:ℝ) → (∀ v, G.degree v = 2*m) →
      ∃ D : Digraph V, IsOrientationOf D G ∧ IsRealRobust D μ τ ∧
        ∀ v, outDegree D v = m ∧ inDegree D v = m := by
  let ξ := min (α/32) ((ν/4)^2/32)
  have hξ : 0 < ξ := lt_min (by positivity) (by positivity)
  have hξα : 32*ξ ≤ α := by linarith only [min_le_left (α/32) ((ν/4)^2/32)]
  have hξν : 32*ξ ≤ (ν/4)^2 := by linarith only [min_le_right (α/32) ((ν/4)^2/32)]
  obtain ⟨N₁,hN₁⟩ := BalancedRobustOrientation.exists_real_relative_orientation.{u} ν τ α (1/2)
    hν hτ hα (by norm_num)
  obtain ⟨μ,hμ,N₂,hN₂⟩ := exists_real_robust_regular_factor.{u} (ν/4) τ (α/4) ξ
    (by positivity) (by linarith only [hν1]) hτ (by linarith only [hτα])
    (by positivity) hξ (by linarith only [hξα]) hξν
  refine ⟨μ,hμ,max N₁ (max N₂ ⌈2/ξ⌉₊),?_⟩
  intro V _ _ G _ m hn hG hd hReg
  let n := Fintype.card V
  let k := ⌊ξ*(n:ℝ)⌋₊
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hξn : 2 ≤ ξ*(n:ℝ) := by
    have h : ⌈2/ξ⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    simpa [mul_comm] using (div_le_iff₀ hξ).mp (Nat.ceil_le.mp h)
  have hkhi : (k:ℝ) ≤ ξ*(n:ℝ) := Nat.floor_le (by positivity)
  have hklo : ξ*(n:ℝ)/2 ≤ (k:ℝ) := by
    have hh := Nat.lt_floor_add_one (ξ*(n:ℝ))
    change ξ*(n:ℝ) < (k:ℝ)+1 at hh
    linarith only [hh,hξn]
  have hkm : k ≤ m := by
    have hx := mul_le_mul_of_nonneg_right hξα (Nat.cast_nonneg n : 0 ≤ (n:ℝ))
    exact_mod_cast (show (k:ℝ) ≤ m by nlinarith only [hkhi,hx,hd,(Nat.cast_nonneg m : 0 ≤ (m:ℝ))])
  obtain ⟨B,hBG,hBI,hBO,hB⟩ := hN₁ G hn₁ hG (fun v => by simpa only [hReg,Nat.cast_mul,Nat.cast_ofNat] using hd)
  have hSemi (b d : ℕ) (h₁ : α*(n:ℝ) ≤ (d:ℝ))
      (h₂ : |2*(b:ℝ)-(d:ℝ)| < (1/2:ℝ)*(d:ℝ)) : α/4*(n:ℝ) ≤ b := by
    linarith only [h₁,(abs_lt.mp h₂).1]
  have hDeg (v : V) : α*(n:ℝ) ≤ (G.degree v:ℝ) := by
    simpa only [hReg,Nat.cast_mul,Nat.cast_ofNat] using hd
  obtain ⟨A,hAB,hA,hRegA⟩ := hN₂ B k hn₂ hB
    (fun v => hSemi _ _ (hDeg v) (hBI v)) (fun v => hSemi _ _ (hDeg v) (hBO v)) hklo hkhi
  let M := A.toSimpleGraphInclusive
  letI : DecidableRel M.Adj := Classical.decRel _
  have hAM : IsOrientationOf A M := by
    refine ⟨?_,fun _ _ h => h.2,?_⟩
    · intro v w h
      exact ⟨(hBG.1 v w (hAB h)).ne,Or.inl h⟩
    · intro v w h
      exact hBG.2.2 v w ⟨hAB h.1,hAB h.2⟩
  have hMG : M ≤ G := by
    intro v w h
    rcases h.2 with h | h
    · exact hBG.1 v w (hAB h)
    · exact (hBG.1 w v (hAB h)).symm
  have hRes (v : V) : (G \ M).degree v = 2*(m-k) := by
    have h := MaximumMatching.degree_sdiff_add_of_le G M hMG v
    have hh := degree_partition A M hAM v
    rw [hReg v] at h
    rw [(hRegA v).1,(hRegA v).2] at hh
    omega
  obtain ⟨C,hC,hRegC⟩ := exists_balanced_even_regular_orientation (G \ M) (m-k) hRes
  have hCA (v w : V) : ¬(A.Adj v w ∧ C.Adj v w) :=
    fun h => (hC.1 v w h.2).2 (hAM.1 v w h.1)
  refine ⟨A ⊔ C,?_,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · intro v w h
      exact h.elim (fun h => hMG (hAM.1 v w h)) (fun h => (hC.1 v w h).1)
    · intro v w h
      by_cases hM : M.Adj v w
      · exact (hAM.2.1 v w hM).imp Or.inl Or.inl
      · exact (hC.2.1 v w ⟨h,hM⟩).imp Or.inr Or.inr
    · intro v w h
      rcases h.1 with hAvw | hCvw <;> rcases h.2 with hAwv | hCwv
      · exact hAM.2.2 v w ⟨hAvw,hAwv⟩
      · exact (hC.1 w v hCwv).2 (hAM.1 v w hAvw).symm
      · exact (hC.1 v w hCvw).2 (hAM.1 w v hAwv).symm
      · exact hC.2.2 v w ⟨hCvw,hCwv⟩
  · exact real_of_integer_at_ceil_interval _ _ μ τ hτ
      (robust_mono le_sup_left (integer_of_real A μ τ hμ.le hA)) (Nat.le_ceil _)
  · intro v
    obtain ⟨ho,hi⟩ := degrees_sup_of_disjoint A C hCA v
    rw [ho,hi,(hRegA v).1,(hRegA v).2,(hRegC v).1,(hRegC v).2]
    omega

end OverfullWork.DirectedRobustExpansion
