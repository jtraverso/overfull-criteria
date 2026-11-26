module

public import OverfullWork.ChenShanCrossingMargins
import OverfullWork.DenseHall
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u

variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The six parts in Step 2 of Theorem 4.15, in directed cyclic order. -/
abbrev CrossingPart (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) : Fin 6 → Type u
  | ⟨0,_⟩ => ↥(S.left (i+1))
  | ⟨1,_⟩ => ↥(S.right i \ S.right (i+1))
  | ⟨2,_⟩ => ↥(S.colors (i+1))
  | ⟨3,_⟩ => ↥(S.left i \ S.left (i+1))
  | ⟨4,_⟩ => ↥(S.right (i+1))
  | ⟨5,_⟩ => ↥(S.colors i \ S.colors (i+1))
  | ⟨j+6,hj⟩ => False.elim (by omega)

noncomputable instance (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) :
    (j : Fin 6) → Fintype (CrossingPart S i j)
  | ⟨0,_⟩ => inferInstanceAs (Fintype ↥(S.left (i+1)))
  | ⟨1,_⟩ => inferInstanceAs (Fintype ↥(S.right i \ S.right (i+1)))
  | ⟨2,_⟩ => inferInstanceAs (Fintype ↥(S.colors (i+1)))
  | ⟨3,_⟩ => inferInstanceAs (Fintype ↥(S.left i \ S.left (i+1)))
  | ⟨4,_⟩ => inferInstanceAs (Fintype ↥(S.right (i+1)))
  | ⟨5,_⟩ => inferInstanceAs (Fintype ↥(S.colors i \ S.colors (i+1)))
  | ⟨j+6,hj⟩ => False.elim (by omega)

def crossingNext : Fin 6 ≃ Fin 6 := Equiv.addRight 1

def crossingVertex (S : NestedTripartitePrefixes A B W ρ m k l)
    (i : ℕ) : (j : Fin 6) → CrossingPart S i j → TripartiteVertex A B W
  | ⟨0,_⟩ => fun v => .inl v.1
  | ⟨1,_⟩ => fun v => .inr (.inl v.1)
  | ⟨2,_⟩ => fun v => .inr (.inr v.1)
  | ⟨3,_⟩ => fun v => .inl v.1
  | ⟨4,_⟩ => fun v => .inr (.inl v.1)
  | ⟨5,_⟩ => fun v => .inr (.inr v.1)
  | ⟨j+6,hj⟩ => False.elim (by omega)

def crossingArc (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (F : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop)
    (j j' : Fin 6) (v : CrossingPart S i j) (w : CrossingPart S i j') : Prop :=
  tripartiteArc F P Q (crossingVertex S i j v) (crossingVertex S i j' w)

private theorem crossing_out_degree {X Y : Type*} [Fintype Y]
    (U : Finset X) (T : Finset Y) (E : X → Y → Prop) (v : U) :
    reserveOutDegree (fun (x : U) (y : T) => E x.1 y.1) v = ((T.filter (E v)).card : ℝ) := by
  unfold reserveOutDegree
  rw [DenseHall.subtype_filter_card]

private theorem crossing_in_degree {X Y : Type*} [Fintype X]
    (U : Finset X) (T : Finset Y) (E : X → Y → Prop) (w : T) :
    reserveInDegree (fun (x : U) (y : T) => E x.1 y.1) w =
      ((U.filter (fun x => E x w)).card : ℝ) := by
  exact congrArg (fun n : ℕ => (n:ℝ)) (DenseHall.subtype_filter_card U (fun x => E x w))


/-- The degree centers in the six parts, in cyclic order. -/
noncomputable def crossingDegreeCenter (ρ : ℝ) (m k i : ℕ) (j : Fin 6) : ℝ :=
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  ![(n-s)/m*k, s/m*k, (n-s)/m*m, s/m*k, (n-s)/m*k, s/m*m] j

theorem crossing_cycle_degree_errors
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {S : NestedTripartitePrefixes A B W ρ m k l} {i : ℕ} {budget : ℝ}
    (hb : TripartiteResidualPrefixBounds F P Q S i budget)
    (hNext : i+1 ≤ l) (hBudget : 0 ≤ budget) (j : Fin 6) (v : CrossingPart S i j) :
    |reserveOutDegree (crossingArc S i F P Q j (crossingNext j)) v -
      crossingDegreeCenter ρ m k i j| ≤ 2*budget ∧
    |reserveInDegree (crossingArc S i F P Q (crossingNext.symm j) j) v -
      crossingDegreeCenter ρ m k i j| ≤ 2*budget := by
  have ab := hb.leftRight.crossing_degree_errors hNext (S.rightAntitone (Nat.le_succ i))
  have ba := hb.rightLeft.crossing_degree_errors hNext (S.leftAntitone (Nat.le_succ i))
  have aw := hb.leftColors.crossing_degree_errors hNext (S.colorsAntitone (Nat.le_succ i))
  have bw := hb.rightColors.crossing_degree_errors hNext (S.colorsAntitone (Nat.le_succ i))
  have wa := hb.colorsLeft.crossing_degree_errors hNext (S.leftAntitone (Nat.le_succ i))
  have wb := hb.colorsRight.crossing_degree_errors hNext (S.rightAntitone (Nat.le_succ i))
  revert v
  fin_cases j <;> intro v <;> constructor
  · change |reserveOutDegree (fun (a : ↥(S.left (i+1))) (b : ↥(S.right i \ S.right (i+1))) => F a b) v - _| ≤ _
    rw [crossing_out_degree (S.left (i+1)) (S.right i \ S.right (i+1)) F v]
    exact (ab v.1 (S.leftAntitone (Nat.le_succ i) v.2)).2
  · change |reserveInDegree (fun (w : ↥(S.colors i \ S.colors (i+1))) (a : ↥(S.left (i+1))) => P a w) v - _| ≤ _
    rw [crossing_in_degree (S.colors i \ S.colors (i+1)) (S.left (i+1)) (fun w a => P a w) v]
    exact (aw v.1 (S.leftAntitone (Nat.le_succ i) v.2)).2
  · change |reserveOutDegree (fun (b : ↥(S.right i \ S.right (i+1))) (w : ↥(S.colors (i+1))) => Q b w) v - _| ≤ _
    rw [crossing_out_degree (S.right i \ S.right (i+1)) (S.colors (i+1)) Q v]
    exact (bw v.1 (mem_sdiff.mp v.2).1).1.trans (by linarith only [hBudget])
  · change |reserveInDegree (fun (a : ↥(S.left (i+1))) (b : ↥(S.right i \ S.right (i+1))) => F a b) v - _| ≤ _
    rw [crossing_in_degree (S.left (i+1)) (S.right i \ S.right (i+1)) F v]
    exact (ba v.1 (mem_sdiff.mp v.2).1).1.trans (by linarith only [hBudget])
  · change |reserveOutDegree (fun (w : ↥(S.colors (i+1))) (a : ↥(S.left i \ S.left (i+1))) => P a w) v - _| ≤ _
    rw [crossing_out_degree (S.colors (i+1)) (S.left i \ S.left (i+1)) (fun w a => P a w) v]
    exact (wa v.1 (S.colorsAntitone (Nat.le_succ i) v.2)).2
  · change |reserveInDegree (fun (b : ↥(S.right i \ S.right (i+1))) (w : ↥(S.colors (i+1))) => Q b w) v - _| ≤ _
    rw [crossing_in_degree (S.right i \ S.right (i+1)) (S.colors (i+1)) Q v]
    exact (wb v.1 (S.colorsAntitone (Nat.le_succ i) v.2)).2
  · change |reserveOutDegree (fun (a : ↥(S.left i \ S.left (i+1))) (b : ↥(S.right (i+1))) => F a b) v - _| ≤ _
    rw [crossing_out_degree (S.left i \ S.left (i+1)) (S.right (i+1)) F v]
    exact (ab v.1 (mem_sdiff.mp v.2).1).1.trans (by linarith only [hBudget])
  · change |reserveInDegree (fun (w : ↥(S.colors (i+1))) (a : ↥(S.left i \ S.left (i+1))) => P a w) v - _| ≤ _
    rw [crossing_in_degree (S.colors (i+1)) (S.left i \ S.left (i+1)) (fun w a => P a w) v]
    exact (aw v.1 (mem_sdiff.mp v.2).1).1.trans (by linarith only [hBudget])
  · change |reserveOutDegree (fun (b : ↥(S.right (i+1))) (w : ↥(S.colors i \ S.colors (i+1))) => Q b w) v - _| ≤ _
    rw [crossing_out_degree (S.right (i+1)) (S.colors i \ S.colors (i+1)) Q v]
    exact (bw v.1 (S.rightAntitone (Nat.le_succ i) v.2)).2
  · change |reserveInDegree (fun (a : ↥(S.left i \ S.left (i+1))) (b : ↥(S.right (i+1))) => F a b) v - _| ≤ _
    rw [crossing_in_degree (S.left i \ S.left (i+1)) (S.right (i+1)) F v]
    exact (ba v.1 (S.rightAntitone (Nat.le_succ i) v.2)).2
  · change |reserveOutDegree (fun (w : ↥(S.colors i \ S.colors (i+1))) (a : ↥(S.left (i+1))) => P a w) v - _| ≤ _
    rw [crossing_out_degree (S.colors i \ S.colors (i+1)) (S.left (i+1)) (fun w a => P a w) v]
    exact (wa v.1 (mem_sdiff.mp v.2).1).1.trans (by linarith only [hBudget])
  · change |reserveInDegree (fun (b : ↥(S.right (i+1))) (w : ↥(S.colors i \ S.colors (i+1))) => Q b w) v - _| ≤ _
    rw [crossing_in_degree (S.right (i+1)) (S.colors i \ S.colors (i+1)) Q v]
    exact (wb v.1 (mem_sdiff.mp v.2).1).1.trans (by linarith only [hBudget])


noncomputable def crossingSizeCenter (ρ : ℝ) (m k i : ℕ) (j : Fin 6) : ℝ :=
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let p : ℝ := (k:ℝ)/m
  ![s,n-s,p*s,n-s,s,p*(n-s)] j

private theorem crossing_core_difference {X : Type*} (U T : Finset X) (h : T ⊆ U) :
    ((U \ T).card : ℝ) = (U.card : ℝ)-(T.card : ℝ) := by
  have he : (((U \ T).card : ℝ)) + (T.card : ℝ) = U.card := by
    exact_mod_cast card_sdiff_add_card_eq_card h
  linarith only [he]

theorem crossingSizeErrors (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (hi : i+1 ≤ l) :
    ∀ j, |(Fintype.card (CrossingPart S i j) : ℝ)-crossingSizeCenter ρ m k i j| ≤ 1 := by
  obtain ⟨hInner,hOuter⟩ := S.crossing_color_sizes hi
  have hCurr : i ≤ l := by omega
  intro j
  fin_cases j
  · change |(Fintype.card ↥(S.left (i+1)) : ℝ)-_| ≤ 1
    rw [Fintype.card_coe,S.leftSize _ hi]
    change |(nestedCoreSize ρ m (i+1) : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ)| ≤ 1
    simp
  · change |(Fintype.card ↥(S.right i \ S.right (i+1)) : ℝ)-_| ≤ 1
    rw [Fintype.card_coe,crossing_core_difference _ _ (S.rightAntitone (Nat.le_succ i)),
      S.rightSize _ hi,S.rightSize _ hCurr]
    change |((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ)) -
      ((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ))| ≤ 1
    simp
  · change |(Fintype.card ↥(S.colors (i+1)) : ℝ)-_| ≤ 1
    rw [Fintype.card_coe]
    exact hInner.trans (by norm_num)
  · change |(Fintype.card ↥(S.left i \ S.left (i+1)) : ℝ)-_| ≤ 1
    rw [Fintype.card_coe,crossing_core_difference _ _ (S.leftAntitone (Nat.le_succ i)),
      S.leftSize _ hi,S.leftSize _ hCurr]
    change |((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ)) -
      ((nestedCoreSize ρ m i : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ))| ≤ 1
    simp
  · change |(Fintype.card ↥(S.right (i+1)) : ℝ)-_| ≤ 1
    rw [Fintype.card_coe,S.rightSize _ hi]
    change |(nestedCoreSize ρ m (i+1) : ℝ)-(nestedCoreSize ρ m (i+1) : ℝ)| ≤ 1
    simp
  · change |(Fintype.card ↥(S.colors i \ S.colors (i+1)) : ℝ)-_| ≤ 1
    rw [Fintype.card_coe]
    exact hOuter

/-- Balanced probabilities on the actual six crossing pairs of Step 2.
The inputs are (4.23) and explicit inequalities on the hierarchy. -/
theorem exists_crossing_cycle_reserve_probabilities
    {F : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (hi : i+1 ≤ l)
    {η δ μ : ℝ} (hm : 0 < m) (hη : 0 < η) (hηhalf : η ≤ 1/2)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/4) (hδ : 0 ≤ δ)
    (hInit : 6 ≤ ρ*(nestedCoreSize ρ m i : ℝ))
    (hSlack : 1 ≤ δ*(nestedCoreSize ρ m i : ℝ))
    (hp : 1/2+η ≤ (k:ℝ)/m) (hMin : 18*δ ≤ η*ρ)
    (hθsmall : 16*δ/ρ ≤ 1/4) (hθtight : (8/η)*(16*δ/ρ) < 1/2)
    (hμ : 0 < μ) (hμupper : μ < 1/4)
    (hb : TripartiteResidualPrefixBounds F P Q S i (δ*nestedCoreSize ρ m i)) :
    ∃ p : (j : Fin 6) → CrossingPart S i j → CrossingPart S i (crossingNext j) → ℝ,
      (∀ j a b, ¬crossingArc S i F P Q j (crossingNext j) a b → p j a b = 0) ∧
      (∀ j a b, crossingArc S i F P Q j (crossingNext j) a b →
        p j a b ∈ Set.Ioo (0 : ℝ) 1 ∧ |p j a b-μ| ≤ μ*((8/η)*(16*δ/ρ))) ∧
      (∀ j (a : CrossingPart S i (crossingNext j)), (∑ b, p (crossingNext j) a b) = ∑ b, p j b a) := by
  let n : ℝ := nestedCoreSize ρ m i
  let s : ℝ := nestedCoreSize ρ m (i+1)
  let p : ℝ := (k:ℝ)/m
  let E := crossingArc S i F P Q
  let g (j : Fin 6) (_ : CrossingPart S i j) := crossingDegreeCenter ρ m k i j
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hn : 0 < n := by
    by_contra! hn'
    linarith only [hInit,mul_nonpos_of_nonneg_of_nonpos hρ.le hn']
  have hρn : 0 < ρ*n := mul_pos hρ hn
  have ⟨hs,_,hr⟩ := nested_crossing_core_window hρ hρsmall (by linarith only [hInit] : 1 ≤ ρ*n)
  change ρ*n ≤ s at hs
  change ρ*n ≤ n-s at hr
  have hpHalf : 1/2 ≤ p := by linarith only [hp,hη]
  have hpPos : 0 < p := by linarith only [hpHalf]
  have hsPos := hρn.trans_le hs
  have hrPos := hρn.trans_le hr
  have hswap (t : ℝ) : t/m*k = p*t := by dsimp only [p]; ring
  have hcancel (t : ℝ) : t/m*m = t := div_mul_cancel₀ _ hmR.ne'
  have hDeg (j : Fin 6) (a : CrossingPart S i j) :=
    crossing_cycle_degree_errors hb hi (mul_nonneg hδ hn.le) j a
  have hS := crossingSizeErrors S i hi
  have hSmall : 8*δ ≤ ρ := by
    have ht := (div_le_iff₀ hρ).mp hθsmall
    linarith only [ht,hρ]
  have hLowS : ρ*n/2 ≤ p*s := by
    have hh := mul_le_mul_of_nonneg_right hpHalf hsPos.le
    linarith only [hh,hs]
  have hLowR : ρ*n/2 ≤ p*(n-s) := by
    have hh := mul_le_mul_of_nonneg_right hpHalf hrPos.le
    linarith only [hh,hr]
  have hCenter (j : Fin 6) : ρ*n/2 ≤ crossingDegreeCenter ρ m k i j := by
    fin_cases j
    · change ρ*n/2 ≤ (n-s)/m*k
      rw [hswap]; exact hLowR
    · change ρ*n/2 ≤ s/m*k
      rw [hswap]; exact hLowS
    · change ρ*n/2 ≤ (n-s)/m*m
      rw [hcancel]; linarith only [hr,hρn]
    · change ρ*n/2 ≤ s/m*k
      rw [hswap]; exact hLowS
    · change ρ*n/2 ≤ (n-s)/m*k
      rw [hswap]; exact hLowR
    · change ρ*n/2 ≤ s/m*m
      rw [hcancel]; linarith only [hs,hρn]

  have hBudgetS (j : Fin 6) (a : CrossingPart S i j) :
      |reserveOutDegree (E j (crossingNext j)) a-g j a| ≤ 2*δ*n ∧
      |reserveInDegree (E (crossingNext.symm j) j) a-g j a| ≤ 2*δ*n := by
    simpa only [mul_assoc] using hDeg j a
  have hUpper : 1/2+η ≤ 1 := by linarith only [hηhalf]
  have hC : 0 ≤ 1/2+η := by positivity
  have htightS : (1/2+η)*s ≤ p*s := mul_le_mul_of_nonneg_right hp hsPos.le
  have htightR : (1/2+η)*(n-s) ≤ p*(n-s) := mul_le_mul_of_nonneg_right hp hrPos.le
  have hUnitS : (1/2+η)*s ≤ s := mul_le_of_le_one_left hsPos.le hUpper
  have hUnitR : (1/2+η)*(n-s) ≤ n-s := mul_le_of_le_one_left hrPos.le hUpper
  have hUnitPS : (1/2+η)*(p*s) ≤ p*s := mul_le_of_le_one_left (mul_nonneg hpPos.le hsPos.le) hUpper
  have hUnitPR : (1/2+η)*(p*(n-s)) ≤ p*(n-s) :=
    mul_le_of_le_one_left (mul_nonneg hpPos.le hrPos.le) hUpper
  have hSide (j j' : Fin 6) (t q : ℝ)
      (hIdealSize : crossingSizeCenter ρ m k i j' = q*t) (ht : ρ*n ≤ t)
      (hq : 1/2 ≤ q) (hIdeal : (1/2+η)*(q*t) ≤ crossingDegreeCenter ρ m k i j) :
      ρ*n/3 ≤ (Fintype.card (CrossingPart S i j') : ℝ) ∧
      (1/2+η)*(Fintype.card (CrossingPart S i j') : ℝ) ≤ crossingDegreeCenter ρ m k i j+1 := by
    apply crossing_target_geometry hn.le hρ.le hη.le hηhalf hInit hq ht _ hIdeal
    rw [← hIdealSize]
    exact hS j'
  have hSideOut (j : Fin 6) :
      ρ*n/3 ≤ (Fintype.card (CrossingPart S i (crossingNext j)) : ℝ) ∧
      (1/2+η)*(Fintype.card (CrossingPart S i (crossingNext j)) : ℝ) ≤
        crossingDegreeCenter ρ m k i j+1 := by
    fin_cases j
    · apply hSide _ _ (n-s) 1 (by simp only [one_mul]; rfl)
        hr (by norm_num)
      change (1/2+η)*(1*(n-s)) ≤ (n-s)/m*k
      rw [hswap]
      simpa only [one_mul] using htightR
    · apply hSide _ _ s p rfl
        hs hpHalf
      change (1/2+η)*(p*s) ≤ s/m*k
      rw [hswap]
      exact hUnitPS
    · apply hSide _ _ (n-s) 1 (by simp only [one_mul]; rfl)
        hr (by norm_num)
      change (1/2+η)*(1*(n-s)) ≤ (n-s)/m*m
      rw [hcancel]
      simpa only [one_mul] using hUnitR
    · apply hSide _ _ s 1 (by simp only [one_mul]; rfl)
        hs (by norm_num)
      change (1/2+η)*(1*s) ≤ s/m*k
      rw [hswap]
      simpa only [one_mul] using htightS
    · apply hSide _ _ (n-s) p rfl
        hr hpHalf
      change (1/2+η)*(p*(n-s)) ≤ (n-s)/m*k
      rw [hswap]
      exact hUnitPR
    · apply hSide _ _ s 1 (by simp only [one_mul]; rfl)
        hs (by norm_num)
      change (1/2+η)*(1*s) ≤ s/m*m
      rw [hcancel]
      simpa only [one_mul] using hUnitS
  have hSideIn (j : Fin 6) :
      ρ*n/3 ≤ (Fintype.card (CrossingPart S i (crossingNext.symm j)) : ℝ) ∧
      (1/2+η)*(Fintype.card (CrossingPart S i (crossingNext.symm j)) : ℝ) ≤
        crossingDegreeCenter ρ m k i j+1 := by
    fin_cases j
    · apply hSide _ _ (n-s) p rfl
        hr hpHalf
      change (1/2+η)*(p*(n-s)) ≤ (n-s)/m*k
      rw [hswap]
      exact hUnitPR
    · apply hSide _ _ s 1 (by simp only [one_mul]; rfl)
        hs (by norm_num)
      change (1/2+η)*(1*s) ≤ s/m*k
      rw [hswap]
      simpa only [one_mul] using htightS
    · apply hSide _ _ (n-s) 1 (by simp only [one_mul]; rfl)
        hr (by norm_num)
      change (1/2+η)*(1*(n-s)) ≤ (n-s)/m*m
      rw [hcancel]
      simpa only [one_mul] using hUnitR
    · apply hSide _ _ s p rfl
        hs hpHalf
      change (1/2+η)*(p*s) ≤ s/m*k
      rw [hswap]
      exact hUnitPS
    · apply hSide _ _ (n-s) 1 (by simp only [one_mul]; rfl)
        hr (by norm_num)
      change (1/2+η)*(1*(n-s)) ≤ (n-s)/m*k
      rw [hswap]
      simpa only [one_mul] using htightR
    · apply hSide _ _ s 1 (by simp only [one_mul]; rfl)
        hs (by norm_num)
      change (1/2+η)*(1*s) ≤ s/m*m
      rw [hcancel]
      simpa only [one_mul] using hUnitS

  have hOutMin (j : Fin 6) (a : CrossingPart S i j) :
      (1/2+η/2)*(Fintype.card (CrossingPart S i (crossingNext j)) : ℝ) ≤
      reserveOutDegree (E j (crossingNext j)) a :=
    crossing_min_degree hn.le hη.le hSlack hMin (hSideOut j).1 (hSideOut j).2 (hBudgetS j a).1
  have hInAt (j : Fin 6) (a : CrossingPart S i j) :
      (1/2+η/2)*(Fintype.card (CrossingPart S i (crossingNext.symm j)) : ℝ) ≤
      reserveInDegree (E (crossingNext.symm j) j) a :=
    crossing_min_degree hn.le hη.le hSlack hMin (hSideIn j).1 (hSideIn j).2 (hBudgetS j a).2
  have hInMin (j : Fin 6) (b : CrossingPart S i (crossingNext j)) :
      (1/2+η/2)*(Fintype.card (CrossingPart S i j) : ℝ) ≤
      reserveInDegree (E j (crossingNext j)) b := by
    have transport (x : Fin 6) (hx : x = j)
        (hxMin : (1/2+η/2)*(Fintype.card (CrossingPart S i x) : ℝ) ≤
          reserveInDegree (E x (crossingNext j)) b) :
        (1/2+η/2)*(Fintype.card (CrossingPart S i j) : ℝ) ≤
          reserveInDegree (E j (crossingNext j)) b := by
      subst x
      exact hxMin
    exact transport _ (crossingNext.symm_apply_apply j) (hInAt (crossingNext j) b)
  have hA0 : (Fintype.card (CrossingPart S i 0) : ℝ) = s := by
    change (Fintype.card ↥(S.left (i+1)) : ℝ) = _
    rw [Fintype.card_coe,S.leftSize _ hi]
  have hA3 : (Fintype.card (CrossingPart S i 3) : ℝ) = n-s := by
    change (Fintype.card ↥(S.left i \ S.left (i+1)) : ℝ) = _
    rw [Fintype.card_coe,crossing_core_difference _ _ (S.leftAntitone (Nat.le_succ i)),
      S.leftSize _ hi,S.leftSize _ (by omega : i ≤ l)]
  have hB1 : (Fintype.card (CrossingPart S i 1) : ℝ) = n-s := by
    change (Fintype.card ↥(S.right i \ S.right (i+1)) : ℝ) = _
    rw [Fintype.card_coe,crossing_core_difference _ _ (S.rightAntitone (Nat.le_succ i)),
      S.rightSize _ hi,S.rightSize _ (by omega : i ≤ l)]
  have hB4 : (Fintype.card (CrossingPart S i 4) : ℝ) = s := by
    change (Fintype.card ↥(S.right (i+1)) : ℝ) = _
    rw [Fintype.card_coe,S.rightSize _ hi]
  have hCount (j : Fin 6) : |reservePairSize (E j (crossingNext j))-p*s*(n-s)| ≤
      (16*δ/ρ)*(p*s*(n-s)) := by
    fin_cases j
    · have hh := (crossing_pair_size_from_core (E (0:Fin 6) (1:Fin 6)) hn.le hρ hδ hpHalf hr).1 (by
        intro a
        have hd := (hBudgetS (0:Fin 6) a).1
        change |reserveOutDegree (E (0:Fin 6) (1:Fin 6)) a-((n-s)/m*k)| ≤ _ at hd
        rwa [hswap] at hd)
      rw [hA0,show s*(p*(n-s)) = p*s*(n-s) by ring] at hh
      exact hh
    · have hh := (crossing_pair_size_from_core (E (1:Fin 6) (2:Fin 6)) hn.le hρ hδ hpHalf hs).1 (by
        intro a
        have hd := (hBudgetS (1:Fin 6) a).1
        change |reserveOutDegree (E (1:Fin 6) (2:Fin 6)) a-(s/m*k)| ≤ _ at hd
        rwa [hswap] at hd)
      rw [hB1,show (n-s)*(p*s) = p*s*(n-s) by ring] at hh
      exact hh
    · have hh := (crossing_pair_size_from_core (E (2:Fin 6) (3:Fin 6)) hn.le hρ hδ hpHalf hs).2 (by
        intro a
        have hd := (hBudgetS (3:Fin 6) a).2
        change |reserveInDegree (E (2:Fin 6) (3:Fin 6)) a-(s/m*k)| ≤ _ at hd
        rwa [hswap] at hd)
      rw [hA3,show (n-s)*(p*s) = p*s*(n-s) by ring] at hh
      exact hh
    · have hh := (crossing_pair_size_from_core (E (3:Fin 6) (4:Fin 6)) hn.le hρ hδ hpHalf hs).1 (by
        intro a
        have hd := (hBudgetS (3:Fin 6) a).1
        change |reserveOutDegree (E (3:Fin 6) (4:Fin 6)) a-(s/m*k)| ≤ _ at hd
        rwa [hswap] at hd)
      rw [hA3,show (n-s)*(p*s) = p*s*(n-s) by ring] at hh
      exact hh
    · have hh := (crossing_pair_size_from_core (E (4:Fin 6) (5:Fin 6)) hn.le hρ hδ hpHalf hr).1 (by
        intro a
        have hd := (hBudgetS (4:Fin 6) a).1
        change |reserveOutDegree (E (4:Fin 6) (5:Fin 6)) a-((n-s)/m*k)| ≤ _ at hd
        rwa [hswap] at hd)
      rw [hB4,show s*(p*(n-s)) = p*s*(n-s) by ring] at hh
      exact hh
    · have hh := (crossing_pair_size_from_core (E (5:Fin 6) (0:Fin 6)) hn.le hρ hδ hpHalf hr).2 (by
        intro a
        have hd := (hBudgetS (0:Fin 6) a).2
        change |reserveInDegree (E (5:Fin 6) (0:Fin 6)) a-((n-s)/m*k)| ≤ _ at hd
        rwa [hswap] at hd)
      rw [hA0,show s*(p*(n-s)) = p*s*(n-s) by ring] at hh
      exact hh

  exact exists_balanced_reserve_of_crossing_estimates crossingNext E g hη hρ hδ hn
    hSmall hθsmall hθtight hμ hμupper (by positivity) hOutMin hInMin hCount
    (fun j _ => hCenter j) (fun j a => (hBudgetS j a).1) (fun j a => (hBudgetS j a).2)

end OverfullWork.ChenShan
