module

public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! Integer radius, growth rate and congestion budget for the
canonical reduced interval in Kühn–Osthus Lemma 7.5(ii). -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- Round the thresholds and choose the growth and forbidden-set
budgets. The factor 16 accounts for rounding the congestion budget. -/
theorem exists_interval_chord_parameters {I : Type*} [Fintype I]
    (Q : Digraph I) (μ τ α : ℝ) (hμ : 0 < μ) (hτ : 0 ≤ τ)
    (z cap : ℕ) (hLarge : 8 ≤ μ*(Fintype.card I:ℝ))
    (hDegree : (τ+μ/2)*(Fintype.card I:ℝ)+2 ≤ α*(Fintype.card I:ℝ))
    (hLoad : (z:ℝ)*(8/μ+6) < (cap:ℝ)*(μ*(Fintype.card I:ℝ)/16))
    (hRob : IsRobustAt Q ⌈μ*(Fintype.card I:ℝ)⌉₊ ⌈τ*(Fintype.card I:ℝ)⌉₊)
    (hIn : ∀ i, α*(Fintype.card I:ℝ) ≤ (inDegree Q i:ℝ))
    (hOut : ∀ i, α*(Fintype.card I:ℝ) ≤ (outDegree Q i:ℝ)) :
    ∃ radius growth cutoff budget : ℕ, IsRobustAt Q radius cutoff ∧ 0 < growth ∧
      2*(budget+1)+growth ≤ radius ∧
      (∀ i, cutoff+2*(budget+1) ≤ outDegree Q i) ∧ (∀ i, cutoff ≤ inDegree Q i) ∧
      z*(2*(Fintype.card I/growth+3)) < cap*(budget+1) := by
  let n := Fintype.card I
  let r := ⌈μ*(n:ℝ)⌉₊
  let t := ⌈τ*(n:ℝ)⌉₊
  let g := r/2
  let b := r/8-1
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hnPos : (0:ℝ) < n := by
    have h : (0:ℝ) < μ*(n:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ) < 8) hLarge
    exact pos_of_mul_pos_right h hμ.le
  have hrLo : μ*(n:ℝ) ≤ r := Nat.le_ceil _
  have hrHi : (r:ℝ) ≤ μ*(n:ℝ)+1 := (Nat.ceil_lt_add_one (mul_nonneg hμ.le hn)).le
  have htHi : (t:ℝ) ≤ τ*(n:ℝ)+1 := (Nat.ceil_lt_add_one (mul_nonneg hτ hn)).le
  have hr : 8 ≤ r := by exact_mod_cast hLarge.trans hrLo
  have hb : b+1 = r/8 := by dsimp only [b]; omega
  have hg : 0 < g := by dsimp only [g]; omega
  have hAvoid : 2*(b+1)+g ≤ r := by rw [hb]; dsimp only [g]; omega
  have hB : 8*(b+1) ≤ r := by rw [hb]; omega
  have hCapLo : (r:ℝ) ≤ 16*((b+1:ℕ):ℝ) := by
    exact_mod_cast (show r ≤ 16*(b+1) by rw [hb]; omega)
  have hBudget : (t:ℝ)+2*((b+1:ℕ):ℝ) ≤ α*(n:ℝ) := by
    have hb' : 8*((b+1:ℕ):ℝ) ≤ r := by exact_mod_cast hB
    nlinarith only [hb',hrHi,htHi,hDegree,mul_nonneg hμ.le hn]
  have hGrowth : μ*(n:ℝ) ≤ 4*(g:ℝ) := hrLo.trans (by
    exact_mod_cast (show r ≤ 4*g by dsimp only [g]; omega))
  have hRatio : ((n/g:ℕ):ℝ) ≤ 4/μ := by
    have hD : ((n/g:ℕ):ℝ)*(g:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n g
    have hM := mul_le_mul_of_nonneg_left hGrowth (Nat.cast_nonneg (n/g) : (0:ℝ) ≤ _)
    have hFour := mul_le_mul_of_nonneg_left hD (by norm_num : (0:ℝ) ≤ 4)
    apply (le_div_iff₀ hμ).mpr
    apply (mul_le_mul_iff_of_pos_right hnPos).mp
    nlinarith only [hM,hFour]
  have hMass : z*(2*(n/g+3)) < cap*(b+1) := by
    have hz := mul_le_mul_of_nonneg_left hRatio (Nat.cast_nonneg z : (0:ℝ) ≤ _)
    have hRight : (cap:ℝ)*(μ*(n:ℝ)/16) ≤ (cap:ℝ)*((b+1:ℕ):ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg cap)
      linarith only [hrLo,hCapLo]
    have hLeft : (z:ℝ)*(2*(((n/g:ℕ):ℝ)+3)) ≤ (z:ℝ)*(8/μ+6) := by
      rw [show 8/μ = 2*(4/μ) by ring]
      nlinarith only [hz]
    exact_mod_cast (hLeft.trans_lt (hLoad.trans_le hRight))
  refine ⟨r,g,t,b,hRob,hg,hAvoid,?_,?_,hMass⟩
  · intro i
    exact_mod_cast hBudget.trans (hOut i)
  · intro i
    have h : (t:ℝ) ≤ α*(n:ℝ) :=
      (le_add_of_nonneg_right (by positivity)).trans hBudget
    exact_mod_cast h.trans (hIn i)

/-- The canonical lifted reduced interval satisfies the exact
integer input needed to schedule all its chord routes. -/
theorem winding_interval_chord_parameters {p b k : ℕ}
    (R₀ : Digraph (Fin k)) (R : Digraph (Fin (p*(b*k)))) (i : Fin p)
    (hb : 0 < b) (hk : 0 < k)
    (hLift : ∀ x y, R.Adj x y ↔ R₀.Adj (windingParent k hk x) (windingParent k hk y))
    (ν τ α : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ) (hτ : τ ≤ 1/4)
    (hOrder : 2 ≤ τ*(k:ℝ)) (hRob : IsRealRobust R₀ ν τ)
    (hIn : ∀ u, α*(k:ℝ) ≤ (inDegree R₀ u:ℝ))
    (hOut : ∀ u, α*(k:ℝ) ≤ (outDegree R₀ u:ℝ))
    (z cap : ℕ)
    (hLarge : 8 ≤ (ν^2/2)*((b*k:ℕ):ℝ))
    (hDegree : (2*τ+(ν^2/2)/2)*((b*k:ℕ):ℝ)+2 ≤ α*((b*k:ℕ):ℝ))
    (hLoad : (z:ℝ)*(8/(ν^2/2)+6) < (cap:ℝ)*((ν^2/2)*((b*k:ℕ):ℝ)/16)) :
    let Q : Digraph (Fin (b*k)) := ⟨fun x y => R.Adj (intervalPosition i x) (intervalPosition i y)⟩
    ∃ radius growth cutoff budget : ℕ, IsRobustAt Q radius cutoff ∧ 0 < growth ∧
      2*(budget+1)+growth ≤ radius ∧
      (∀ j, cutoff+2*(budget+1) ≤ outDegree Q j) ∧
      (∀ j, cutoff ≤ inDegree Q j) ∧
      z*(2*((b*k)/growth+3)) < cap*(budget+1) := by
  dsimp only
  let Q : Digraph (Fin (b*k)) := ⟨fun x y => R.Adj (intervalPosition i x) (intervalPosition i y)⟩
  obtain ⟨hR,hSemi⟩ := winding_interval_integer_expansion R₀ R i hb hk hLift ν τ hν hντ hτ hOrder hRob
  have hMinIn (x : Fin (b*k)) : α*((b*k:ℕ):ℝ) ≤ (inDegree Q x:ℝ) := by
    rw [(hSemi x).1,Nat.cast_mul,Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_right (hIn (windingParent k hk x)) (Nat.cast_nonneg b)
    nlinarith only [h]
  have hMinOut (x : Fin (b*k)) : α*((b*k:ℕ):ℝ) ≤ (outDegree Q x:ℝ) := by
    rw [(hSemi x).2,Nat.cast_mul,Nat.cast_mul]
    have h := mul_le_mul_of_nonneg_right (hOut (windingParent k hk x)) (Nat.cast_nonneg b)
    nlinarith only [h]
  have h := exists_interval_chord_parameters Q (ν^2/2) (2*τ)
    α (by positivity) (by linarith) z cap
    (by simpa only [Fintype.card_fin] using hLarge)
    (by simpa only [Fintype.card_fin] using hDegree)
    (by simpa only [Fintype.card_fin] using hLoad)
    (by simpa only [Fintype.card_fin] using hR)
    (by simpa only [Fintype.card_fin] using hMinIn)
    (by simpa only [Fintype.card_fin] using hMinOut)
  simpa only [Fintype.card_fin] using h

end OverfullWork.DirectedRobustExpansion
