module

public import OverfullWork.IndependentBernoulliSampling
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset IndependentBernoulliSampling
open scoped Classical

/-- The simultaneous vertex degree tests in (R1). Each incoming and
outgoing mean is at most 4μn, and the two means agree at every vertex. -/
theorem exists_reserve_sample_degree_control
    {I V : Type*} [Fintype I] [Fintype V] (p : I → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hp' : ∀ e, p e ≤ 1) (In Out : V → Finset I)
    {μ n ξ : ℝ} (hμ : 0 < μ) (hn : 0 < n) (hξ : 0 ≤ ξ)
    (hMean : ∀ v, mean p (In v) = mean p (Out v))
    (hUpper : ∀ v, mean p (Out v) ≤ 4*μ*n)
    (hUnion : (Fintype.card V : ℝ)*4*
      Real.exp (-((min (ξ*n/2) (μ*n))^2/(16*μ*n))) < 1) :
    ∃ sample : I → Bool, ∀ v,
      |count (Out v) sample-count (In v) sample| ≤ ξ*n ∧
      count (Out v) sample+count (In v) sample ≤ 10*μ*n := by
  let D := min (ξ*n/2) (μ*n)
  let S (b : Bool × V) := if b.1 then Out b.2 else In b.2
  have hM : 0 < 4*μ*n := by positivity
  have hBound (b : Bool × V) : mean p (S b) ≤ 4*μ*n := by
    cases b with
    | mk t v =>
      cases t
      · change mean p (In v) ≤ _
        rw [hMean]
        exact hUpper v
      · exact hUpper v
  have hD : 0 ≤ D := le_min (by positivity) (by positivity)
  have hD' : D ≤ 2*(4*μ*n) := by
    have h := min_le_right (ξ*n/2) (μ*n)
    linarith only [h,hM]
  have hUnion' : (Fintype.card (Bool × V) : ℝ)*
      (2*Real.exp (-(D^2/(4*(4*μ*n))))) < 1 := by
    rw [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    have hDen : 4*(4*μ*n) = 16*μ*n := by ring
    rw [hDen]
    convert hUnion using 1
    ring
  obtain ⟨sample,hsample⟩ :=
    exists_simultaneous_count_of_mean_le p hp hp' S hM hBound hD hD' hUnion'
  refine ⟨sample,fun v => ?_⟩
  have hOut : |count (Out v) sample-mean p (Out v)| ≤ D := hsample (true,v)
  have hIn : |count (In v) sample-mean p (In v)| ≤ D := hsample (false,v)
  rw [hMean v] at hIn
  have ho := abs_le.mp hOut
  have hi := abs_le.mp hIn
  have hSmall : D ≤ ξ*n/2 := min_le_left _ _
  have hSmall' : D ≤ μ*n := min_le_right _ _
  exact ⟨abs_le.mpr ⟨by linarith only [hSmall,ho.1,hi.2],
    by linarith only [hSmall,ho.2,hi.1]⟩, by
      linarith only [hSmall',ho.2,hi.2,hUpper v]⟩

end OverfullWork.ChenShan
