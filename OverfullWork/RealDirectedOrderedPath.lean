module

public import OverfullWork.DirectedPrescribedVertexPath
public import OverfullWork.RealDirectedRobustExpansion

@[expose] public section


/-! Normalized, graph-independent sufficient parameter range for the
short prescribed directed path in KLO Corollary 6.8. Integer thresholds
and deletion budgets are derived internally from real robust expansion. -/
namespace OverfullWork.DirectedPrescribedVertexPath
open Finset DirectedRobustExpansion DirectedListRoutes
open scoped Classical
set_option maxHeartbeats 16000000

theorem ordered_path_budgets (n q : ℕ) (ν τ α : ℝ)
    (hν : 0 < ν) (hSmall : ν ≤ 1/64) (hντ : ν ≤ τ) (hτα : 4*τ ≤ α)
    (hLarge : 64 ≤ ν*(n:ℝ)) (hQ : (q:ℝ) ≤ ν^3*(n:ℝ)) :
    let r := ⌈ν*(n:ℝ)⌉₊
    let t := ⌈τ*(n:ℝ)⌉₊
    let s := ⌈ν*(n:ℝ)/2⌉₊
    let L := n/s+3
    0 < s ∧ q*(L+2)+s ≤ r ∧
      ((t+q*(L+2):ℕ):ℝ) ≤ α*(n:ℝ) ∧
      ((q*L+1:ℕ):ℝ) ≤ ν*(n:ℝ)/4 := by
  dsimp only
  let s := ⌈ν*(n:ℝ)/2⌉₊
  let d := n/s
  let L := d+3
  have hn : (0:ℝ) < n := by
    by_contra hh
    have he : (n:ℝ)=0 := le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg n)
    rw [he,mul_zero] at hLarge
    norm_num at hLarge
  have hs : 0 < s := Nat.ceil_pos.mpr (by nlinarith only [hLarge])
  have hsLo : ν*(n:ℝ)/2 ≤ (s:ℝ) := Nat.le_ceil _
  have hsHi : (s:ℝ) ≤ ν*(n:ℝ)/2+1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hd : (d:ℝ)*(s:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.div_mul_le_self n s
  have hDν : ν*(d:ℝ) ≤ 2 := by
    by_contra hh
    have hp := mul_pos hn (show 0 < ν*(d:ℝ)-2 by linarith)
    have hm := mul_le_mul_of_nonneg_left hsLo (Nat.cast_nonneg d : (0:ℝ) ≤ d)
    nlinarith only [hp,hm,hd]
  have hLν : ν*((L+2:ℕ):ℝ) ≤ 3 := by
    simp only [L,Nat.cast_add,Nat.cast_ofNat]
    nlinarith only [hDν,hSmall]
  have hMulQ := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (L+2) : (0:ℝ) ≤ ((L+2:ℕ):ℝ))
  have hMulL := mul_le_mul_of_nonneg_left hLν
    (mul_nonneg (sq_nonneg ν) hn.le)
  have hNuBound : 3*ν^2 ≤ ν/8 := by
    have hh := mul_le_mul_of_nonneg_left hSmall hν.le
    nlinarith only [hh,hν]
  have hMulN := mul_le_mul_of_nonneg_right hNuBound hn.le
  have hReserve : ((q*(L+2):ℕ):ℝ) ≤ ν*(n:ℝ)/8 := by
    push_cast at hMulQ hMulL hMulN ⊢
    nlinarith only [hMulQ,hMulL,hMulN]
  have hR : ν*(n:ℝ) ≤ (⌈ν*(n:ℝ)⌉₊:ℝ) := Nat.le_ceil _
  have hBudget : q*(L+2)+s ≤ ⌈ν*(n:ℝ)⌉₊ := by
    exact_mod_cast (show ((q*(L+2):ℕ):ℝ)+(s:ℝ) ≤ (⌈ν*(n:ℝ)⌉₊:ℝ) by
      linarith only [hReserve,hsHi,hR,hLarge])
  have hτ : 0 ≤ τ := hν.le.trans hντ
  have hT : (⌈τ*(n:ℝ)⌉₊:ℝ) ≤ τ*(n:ℝ)+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hτ hn.le)).le
  have hScale := mul_le_mul_of_nonneg_right hτα hn.le
  have hNuScale := mul_le_mul_of_nonneg_right hντ hn.le
  have hDegree : ((⌈τ*(n:ℝ)⌉₊+q*(L+2):ℕ):ℝ) ≤ α*(n:ℝ) := by
    rw [Nat.cast_add]
    nlinarith only [hT,hReserve,hScale,hNuScale,hLarge]
  have hLength : ((q*L+1:ℕ):ℝ) ≤ ν*(n:ℝ)/4 := by
    have hh : q*L ≤ q*(L+2) := Nat.mul_le_mul_left q (by omega)
    have hc : ((q*L:ℕ):ℝ) ≤ ((q*(L+2):ℕ):ℝ) := by exact_mod_cast hh
    have hs : ((q*L+1:ℕ):ℝ) ≤ ((q*(L+2):ℕ):ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right hh 1
    linarith only [hs,hReserve,hLarge]
  exact ⟨hs,hBudget,hDegree,hLength⟩

/-- The actual simple directed path through all prescribed vertices,
in order, using at most nu*n/4 vertices. No Hamiltonian input. -/
theorem exists_real_ordered_path {V : Type*} [Fintype V] (D : Digraph V)
    (ν τ α : ℝ) (hν : 0 < ν) (hSmall : ν ≤ 1/64)
    (hντ : ν ≤ τ) (hτα : 4*τ ≤ α) (hLarge : 64 ≤ ν*(Fintype.card V:ℝ))
    (hRobust : IsRealRobust D ν τ)
    (hIn : ∀ v,α*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ))
    (hOut : ∀ v,α*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ))
    (x : V) (marks : List V) (hDistinct : (x :: marks).Nodup)
    (hCount : (marks.length:ℝ) ≤ ν^3*(Fintype.card V:ℝ)) :
    ∃ l,(x :: l).IsChain D.Adj ∧
      (x :: l).getLast?=(x :: marks).getLast? ∧
      (x :: l).Nodup ∧ marks.Sublist l ∧
      ((x :: l).length:ℝ) ≤ ν*(Fintype.card V:ℝ)/4 := by
  obtain ⟨hS,hBudget,hDegree,hLength⟩ := ordered_path_budgets
    (Fintype.card V) marks.length ν τ α hν hSmall hντ hτα hLarge hCount
  obtain ⟨l,hChain,hLast,hSimple,hSub,hLen,_⟩ := exists_ordered_path D
    ⌈ν*(Fintype.card V:ℝ)⌉₊ ⌈ν*(Fintype.card V:ℝ)/2⌉₊ ⌈τ*(Fintype.card V:ℝ)⌉₊
    (Fintype.card V/⌈ν*(Fintype.card V:ℝ)/2⌉₊+3)
    (integer_of_real D ν τ hν.le hRobust) hS le_rfl marks ∅ x hDistinct
    (by simp) (by simpa using hBudget)
    (fun v _ => by
      have hh := hDegree.trans (hOut v)
      have hn : ⌈τ*(Fintype.card V:ℝ)⌉₊ +
          marks.length*(Fintype.card V/⌈ν*(Fintype.card V:ℝ)/2⌉₊+3+2) ≤ outDegree D v := by
        exact_mod_cast hh
      simpa only [card_empty,add_zero] using hn)
    (fun v _ => by
      have hh := hDegree.trans (hIn v)
      have hn : ⌈τ*(Fintype.card V:ℝ)⌉₊ +
          marks.length*(Fintype.card V/⌈ν*(Fintype.card V:ℝ)/2⌉₊+3+2) ≤ inDegree D v := by
        exact_mod_cast hh
      omega)
  refine ⟨l,hChain,hLast,hSimple,hSub,?_⟩
  have hc : ((l.length+1:ℕ):ℝ) ≤
      ((marks.length*(Fintype.card V/⌈ν*(Fintype.card V:ℝ)/2⌉₊+3)+1:ℕ):ℝ) := by
    exact_mod_cast Nat.add_le_add_right hLen 1
  simpa only [List.length_cons] using hc.trans hLength

end OverfullWork.DirectedPrescribedVertexPath
