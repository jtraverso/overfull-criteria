module

public import OverfullWork.KuhnOsthusUniversalWalkOrdering
public import OverfullWork.KuhnOsthusWindingIntervalGeometry

@[expose] public section


/-! Choose the routing parameters of Lemma 9.1 from real robust
expansion and the minimum semidegree of the wound reduced graph. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical

/-- The lower bound on the multiplicity of the universal walk depends
only on the reduced expansion parameter. The actual walk is then
constructed after the reduced graph and the cycle have been fixed. -/
theorem kuhn_osthus_universal_walk_on_ordered_cycle (ν τ : ℝ)
    (hν : 0 < ν) (hν₁ : ν ≤ 1/3) (hντ : ν ≤ τ) :
    ∀ (n L : ℕ) (R : Digraph (Fin n)),
      2 ≤ n → ⌈25/ν^2⌉₊+4 ≤ L → 3 ≤ τ*(n:ℝ) → IsRealRobust R ν τ →
      (∀ i, R.Adj i (finRotate n i)) →
      (∀ i, 2*τ*(n:ℝ) ≤ (inDegree R i:ℝ)) →
      (∀ i, 2*τ*(n:ℝ) ≤ (outDegree R i:ℝ)) →
      ∃ l : Fin n → List (Fin n), ∃ F : Fin (L+1) → Equiv.Perm (Fin n),
        (∀ j, DirectedListRoutes.Route (reindexSources R (finRotate n).symm) j (finRotate n j) (l j) ∧
          ((l j).length:ℝ) ≤ 3/ν) ∧
        F 0 = finRotate n ∧ (∀ j x, R.Adj x (F j x)) ∧
        (∀ x y, ((univ : Finset (Fin (L+1))).filter (fun j => F j x = y)).card =
          elementaryChordMultiplicity (finRotate n) l x y +
            if finRotate n x = y then L+1 - (∑ z, elementaryChordMultiplicity (finRotate n) l x z) else 0) ∧
        HasSpanningCycle (fun e f : (Σ _ : Fin (L+1), Fin n) => F e.1 e.2 = f.2) := by
  intro n L R hn hL hSize hRob hCycle hIn hOut
  let r := ⌈ν*(n:ℝ)⌉₊
  let b := r/4
  let g := r-2*b
  let t := ⌈τ*(n:ℝ)⌉₊
  let cap := ⌈25/ν^2⌉₊
  have hn' : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrLo : ν*(n:ℝ) ≤ (r:ℝ) := Nat.le_ceil _
  have hrHi : (r:ℝ) ≤ ν*(n:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have htHi : (t:ℝ) ≤ τ*(n:ℝ)+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hr : 0 < r := by exact_mod_cast (mul_pos hν hn').trans_le hrLo
  have hg : 0 < g := by dsimp only [g,b]; omega
  have hHalf : r ≤ 2*g := by dsimp only [g,b]; omega
  have hAvoid : 2*b+g ≤ r := by dsimp only [g,b]; omega
  have hSpend : (4:ℝ)*(b:ℝ) ≤ r := by exact_mod_cast (show 4*b ≤ r by dsimp only [b]; omega)
  have hCeilB : (r:ℝ) ≤ 4*((b:ℝ)+1) := by exact_mod_cast (show r ≤ 4*(b+1) by dsimp only [b]; omega)
  have hDegree : (t:ℝ)+2*(b:ℝ) ≤ 2*τ*(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_right hντ hn'.le
    linarith only [hSize,h,hrHi,htHi,hSpend]
  have hLength : ((n/g+3:ℕ):ℝ) ≤ 3/ν := by
    have hG : ν*(n:ℝ) ≤ 2*(g:ℝ) := hrLo.trans (by exact_mod_cast hHalf)
    have hDiv : ((n/g:ℕ):ℝ)*(g:ℝ) ≤ n := by exact_mod_cast Nat.div_mul_le_self n g
    have hMul := mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg (n/g))
    have hCancel := mul_le_mul_of_nonneg_left hDiv (by norm_num : (0:ℝ) ≤ 2)
    have hRatio : ((n/g:ℕ):ℝ) ≤ 2/ν := by
      apply (le_div_iff₀ hν).mpr
      apply (mul_le_mul_iff_of_pos_right hn').mp
      linarith only [hMul,hCancel]
    have hThree : (3:ℝ) ≤ 1/ν := (le_div_iff₀ hν).mpr (by linarith only [hν₁])
    push_cast
    have hEq : (2:ℝ)/ν+1/ν = 3/ν := by rw [←add_div]; norm_num
    linarith only [hRatio,hThree,hEq]
  have hCap : (25:ℝ) ≤ (cap:ℝ)*ν^2 :=
    (div_le_iff₀ (sq_pos_of_pos hν)).mp (Nat.le_ceil _)
  have hMass : n*(2*(n/g+3)) < cap*(b+1) := by
    have h₁ := mul_le_mul_of_nonneg_left hLength (show 0 ≤ (2:ℝ)*(n:ℝ)*ν by positivity)
    have h₂ := mul_le_mul_of_nonneg_left (show ν*(n:ℝ) ≤ 4*((b:ℝ)+1) by linarith only [hrLo,hCeilB])
      (show 0 ≤ (cap:ℝ)*ν by positivity)
    have h₃ := mul_le_mul_of_nonneg_right hCap hn'.le
    have hDiv : ν*(3/ν) = (3:ℝ) := mul_div_cancel₀ _ hν.ne'
    have hR : (n:ℝ)*(2*(((n/g:ℕ):ℝ)+3)) < (cap:ℝ)*((b:ℝ)+1) := by
      push_cast at h₁
      apply (mul_lt_mul_iff_of_pos_left hν).mp
      nlinarith only [h₁,h₂,h₃,hn',congrArg (fun x : ℝ => x*(n:ℝ)) hDiv]
    exact_mod_cast hR
  let i₀ : Fin n := ⟨0,by omega⟩
  have hBase (i : Fin n) : (finRotate n).SameCycle i₀ i :=
    (isCycle_finRotate_of_le hn).sameCycle (finRotate_interval_ne_self hn _) (finRotate_interval_ne_self hn _)
  have hRob' : IsRobustAt R r t := by
    simpa only [r,t,Fintype.card_fin] using integer_of_real R ν τ hν.le hRob
  have hOut' (i : Fin n) : t+2*b ≤ outDegree R i := by exact_mod_cast hDegree.trans (hOut i)
  have hIn' (i : Fin n) : t ≤ inDegree R i := by
    have h := (le_add_of_nonneg_right (show 0 ≤ (2:ℝ)*(b:ℝ) by positivity)).trans hDegree
    exact_mod_cast h.trans (hIn i)
  obtain ⟨l,F,hRoute,hFirst,hF,hMult,hWalk⟩ := exists_universal_walk_of_chord_budgets
    R (finRotate n) i₀ r g t cap b L hBase hCycle hRob' hg hAvoid hOut' hIn'
    (by simpa only [Fintype.card_fin] using hMass) hL
  refine ⟨l,F,fun j => ⟨(hRoute j).1, (by exact_mod_cast
    (show (l j).length ≤ n/g+3 by simpa only [Fintype.card_fin] using (hRoute j).2) :
      ((l j).length:ℝ) ≤ ((n/g+3:ℕ):ℝ)).trans hLength⟩,hFirst,hF,?_,hWalk⟩
  intro x y
  convert hMult x y using 1
  · congr 1
    ext j
    simp
  · by_cases h : finRotate n x = y <;> simp [h]

end OverfullWork.DirectedRobustExpansion
