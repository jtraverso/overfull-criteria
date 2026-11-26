module

public import OverfullWork.ChenShanRepairIteration
public import OverfullWork.ChenShanRepairTripartite
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- Chen–Shan, Lemma 4.13. The repair works with c₀ = 1/16 and a deleted
degree bound of 5√ξ n whenever √ξ ≤ min (η/32) (1/128). -/
theorem exists_tripartite_balancing_deletion
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (n : ℕ) (η ξ : ℝ) (hη : 0 < η) (hξ : 0 ≤ ξ)
    (hSmall : Real.sqrt ξ ≤ min (η/32) (1/128))
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hW : (n : ℝ)/2 ≤ Fintype.card W ∧ (Fintype.card W : ℝ) ≤ 2*n)
    (hAB : ∀ a, (1/2+η)*n ≤ ((univ.filter (E a)).card : ℝ))
    (hBA : ∀ b, (1/2+η)*n ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun w => ¬ L a w)).card : ℝ) ≤ (n : ℝ)/16)
    (hBW : ∀ b, ((univ.filter (fun w => ¬ R b w)).card : ℝ) ≤ (n : ℝ)/16)
    (hWA : ∀ w, ((univ.filter (fun a => ¬ L a w)).card : ℝ) ≤ (n : ℝ)/16)
    (hWB : ∀ w, ((univ.filter (fun b => ¬ R b w)).card : ℝ) ≤ (n : ℝ)/16)
    (hImbalance : ∀ v, |(arcDivergence (tripartiteArcs E L R) v : ℝ)| ≤ ξ*n) :
    ∃ D ⊆ tripartiteArcs E L R, ArcBalanced (tripartiteArcs E L R \ D) ∧
      ∀ v, (incidentDegree D v : ℝ) ≤ 5*Real.sqrt ξ*n := by
  let G := tripartiteArcs E L R
  let s := Real.sqrt ξ
  let x := s*n
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2 = ξ := Real.sq_sqrt hξ
  have hsη : s ≤ η/32 := hSmall.trans (min_le_left _ _)
  have hs128 : s ≤ 1/128 := hSmall.trans (min_le_right _ _)
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hx : 0 ≤ x := mul_nonneg hs hn
  have hξx : ξ*n ≤ x := by
    have hy := mul_le_mul_of_nonneg_right (show s ≤ 1 by linarith only [hs128]) hx
    dsimp only [x] at hy ⊢
    rw [← hs2]
    nlinarith only [hy]
  have hAbs (v : A ⊕ B ⊕ W) : ((arcDivergence G v).natAbs : ℝ) ≤ ξ*n := by
    have h := congrArg (fun y : ℤ => (y : ℝ)) (Int.abs_eq_natAbs (arcDivergence G v))
    simp only [Int.cast_abs,Int.cast_natCast] at h
    rw [← h]
    exact hImbalance v
  by_cases hx1 : 1 ≤ x
  · have hn0 : 0 < (n : ℝ) := by
      by_contra! h
      have hZero : (n : ℝ) = 0 := le_antisymm h hn
      have hXZero : x = 0 := by simp [x,hZero]
      linarith only [hXZero,hx1]
    let K := ⌊ξ*(n : ℝ)⌋₊
    let T := ⌈x⌉₊
    let Fcap := ⌈12*x⌉₊
    have hK (v : A ⊕ B ⊕ W) : (arcDivergence G v).natAbs ≤ K :=
      (Nat.le_floor_iff (mul_nonneg hξ hn)).2 (hAbs v)
    have hKx : (K : ℝ) ≤ x := (Nat.floor_le (mul_nonneg hξ hn)).trans hξx
    have hTx : x ≤ (T : ℝ) := Nat.le_ceil _
    have hBx : 12*x ≤ (Fcap : ℝ) := Nat.le_ceil _
    have hT : 0 < T := by
      exact_mod_cast (show (0 : ℝ) < T by linarith only [hx1,hTx])
    have hTupper : (T : ℝ) ≤ 2*x := by
      have h := Nat.ceil_lt_add_one hx
      change (T : ℝ) < x+1 at h
      linarith only [hx1,h]
    have hBupper : (Fcap : ℝ) ≤ 13*x := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ 12*x by positivity)
      change (Fcap : ℝ) < 12*x+1 at h
      linarith only [hx1,h]
    have hV : (Fintype.card (A ⊕ B ⊕ W) : ℝ) ≤ 4*n := by
      simp only [Fintype.card_sum,Nat.cast_add,hA,hB]
      linarith only [hW.2]
    have hP : (positiveImbalance G : ℝ) ≤ 4*x^2 := by
      calc
        _ ≤ (Fintype.card (A ⊕ B ⊕ W) : ℝ) * (ξ*n) :=
          positiveImbalance_le_card_mul G (mul_nonneg hξ hn)
            (fun v => (le_abs_self _).trans (hImbalance v))
        _ ≤ (4*n)*(ξ*n) := mul_le_mul_of_nonneg_right hV (mul_nonneg hξ hn)
        _ = 4*x^2 := by dsimp only [x]; rw [← hs2]; ring
    have hTotal : 3*positiveImbalance G ≤ T*Fcap := by
      have hMul := mul_le_mul hTx hBx (show 0 ≤ 12*x by positivity) (Nat.cast_nonneg T)
      exact_mod_cast (show (3:ℝ)*positiveImbalance G ≤ (T:ℝ)*Fcap by
        nlinarith only [hP,hMul])
    let q : ℕ := (Fcap+2)+2*(K+2*T)
    have hq : (q : ℝ) ≤ 25*x := by
      push_cast [q]
      linarith only [hBupper,hKx,hTupper,hx1]
    have hq₁ : (q : ℝ) < 2*η*n := by
      apply hq.trans_lt
      have h := mul_lt_mul_of_pos_right (show 25*s < 2*η by linarith only [hη,hsη]) hn0
      dsimp only [x]
      linarith only [h]
    have hq₂ : (q : ℝ) < (1/2-2*(1/16))*n := by
      apply hq.trans_lt
      have h := mul_lt_mul_of_pos_right
        (show 25*s < 1/2-2*(1/16) by linarith only [hs128]) hn0
      dsimp only [x]
      linarith only [h]
    obtain ⟨hOut,hIn⟩ := tripartite_repair_neighborhoods E L R n η (1/16) q hA hB hW.1
      hAB hBA (fun a => by simpa [div_eq_mul_inv,mul_comm] using hAW a)
      (fun b => by simpa [div_eq_mul_inv,mul_comm] using hBW b)
      (fun w => by simpa [div_eq_mul_inv,mul_comm] using hWA w)
      (fun w => by simpa [div_eq_mul_inv,mul_comm] using hWB w) hq₁ hq₂
    obtain ⟨D,hD,hBalanced,hBound⟩ := exists_balanced_leave_of_repair_budgets repairPart G K T Fcap
      hT hTotal (repairPart_step E L R) hK
      (fun a => by
        have h : (repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) (repairPart a+1)).card + q <
            2*(arcOutNeighbors G a).card := by exact_mod_cast hOut a
        simpa only [q,Nat.add_assoc] using h)
      (fun b => by
        have h : (repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) (repairPart b-1)).card + q <
            2*(arcInNeighbors G b).card := by exact_mod_cast hIn b
        simpa only [q,Nat.add_assoc] using h)
    refine ⟨D,hD,?_,fun v => ?_⟩
    · convert hBalanced using 1
      ext e
      simp [G]
    have hNat : (incidentDegree D v : ℝ) ≤ (K:ℝ)+2*T := by exact_mod_cast hBound v
    dsimp only [x] at hKx hTupper
    linarith only [hNat,hKx,hTupper]
  · have hZero (v : A ⊕ B ⊕ W) : arcDivergence G v = 0 := by
      have h : ((arcDivergence G v).natAbs : ℝ) < 1 :=
        ((hAbs v).trans hξx).trans_lt (lt_of_not_ge hx1)
      have h' : (arcDivergence G v).natAbs < 1 := by exact_mod_cast h
      omega
    refine ⟨∅,empty_subset _,?_,?_⟩
    · rw [sdiff_empty]
      change ArcBalanced G
      apply (arcBalanced_iff_positiveImbalance_eq_zero _).2
      simp only [positiveImbalance,hZero,Int.toNat_zero,sum_const_zero]
    · intro v
      simp only [incidentDegree,filter_empty,card_empty,Nat.cast_zero]
      positivity

end OverfullWork.ChenShan
