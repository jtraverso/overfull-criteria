module

public import OverfullWork.ChenShanRepairNeighborhoods
import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

def repairPart : A ⊕ B ⊕ W → ZMod 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem repairPart_step (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (a b : A ⊕ B ⊕ W) (h : (a,b) ∈ tripartiteArcs E L R) :
    repairPart b = repairPart a + 1 := by
  have h' := mem_tripartiteArcs.mp h
  rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
    simp [tripartiteArc] at h' <;> simp only [repairPart] <;> decide

theorem card_tripartite_outNeighbors (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (v : A ⊕ B ⊕ W) : (arcOutNeighbors (tripartiteArcs E L R) v).card =
      match v with
      | .inl a => (univ.filter (E a)).card
      | .inr (.inl b) => (univ.filter (R b)).card
      | .inr (.inr w) => (univ.filter (fun a => L a w)).card := by
  rcases v with a | (b | w) <;>
    simp only [arcOutNeighbors,mem_tripartiteArcs,card_filter,Fintype.sum_sum_type,tripartiteArc,
      ite_false,sum_const_zero,zero_add,add_zero]

theorem card_tripartite_inNeighbors (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (v : A ⊕ B ⊕ W) : (arcInNeighbors (tripartiteArcs E L R) v).card =
      match v with
      | .inl a => (univ.filter (L a)).card
      | .inr (.inl b) => (univ.filter (fun a => E a b)).card
      | .inr (.inr w) => (univ.filter (fun b => R b w)).card := by
  rcases v with a | (b | w) <;>
    simp only [arcInNeighbors,mem_tripartiteArcs,card_filter,Fintype.sum_sum_type,tripartiteArc,
      ite_false,sum_const_zero,zero_add,add_zero]

private theorem dense_repair_slack {X : Type*} [Fintype X] {P : X → Prop}
    {n : ℕ} {η q : ℝ} (hq : q < 2*η*n) (hc : Fintype.card X = n)
    (hP : (1/2+η)*n ≤ ((univ.filter P).card : ℝ)) :
    (Fintype.card X : ℝ) + q < 2*(univ.filter P).card := by
  rw [hc]
  linarith only [hq,hP]

private theorem nearly_complete_repair_slack {X : Type*} [Fintype X] {P : X → Prop}
    {n : ℕ} {c q : ℝ} (hq : q < (1/2-2*c)*n)
    (hc : (n : ℝ)/2 ≤ Fintype.card X)
    (hP : ((univ.filter (fun x => ¬ P x)).card : ℝ) ≤ c*n) :
    (Fintype.card X : ℝ) + q < 2*(univ.filter P).card := by
  have hS : ((univ.filter P).card : ℝ) + ((univ.filter (fun x => ¬ P x)).card : ℝ) =
      Fintype.card X := by
    exact_mod_cast (card_filter_add_card_filter_not (s := (univ : Finset X)) P).trans card_univ
  linarith only [hq,hP,hS,hc]

/-- The dense pair and the two almost-complete pairs provide the
neighborhood slack used by the repair procedure. -/
theorem tripartite_repair_neighborhoods
    (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
    (n : ℕ) (η c q : ℝ)
    (hA : Fintype.card A = n) (hB : Fintype.card B = n)
    (hW : (n : ℝ)/2 ≤ Fintype.card W)
    (hAB : ∀ a, (1/2+η)*n ≤ ((univ.filter (E a)).card : ℝ))
    (hBA : ∀ b, (1/2+η)*n ≤ ((univ.filter (fun a => E a b)).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun w => ¬ L a w)).card : ℝ) ≤ c*n)
    (hBW : ∀ b, ((univ.filter (fun w => ¬ R b w)).card : ℝ) ≤ c*n)
    (hWA : ∀ w, ((univ.filter (fun a => ¬ L a w)).card : ℝ) ≤ c*n)
    (hWB : ∀ w, ((univ.filter (fun b => ¬ R b w)).card : ℝ) ≤ c*n)
    (hq₁ : q < 2*η*n) (hq₂ : q < (1/2-2*c)*n) :
    (∀ a : A ⊕ B ⊕ W, ((repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) (repairPart a + 1)).card : ℝ) + q <
      2*(arcOutNeighbors (tripartiteArcs E L R) a).card) ∧
    (∀ b : A ⊕ B ⊕ W, ((repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) (repairPart b - 1)).card : ℝ) + q <
      2*(arcInNeighbors (tripartiteArcs E L R) b).card) := by
  have hHalfA : (n : ℝ)/2 ≤ Fintype.card A := by rw [hA]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hHalfB : (n : ℝ)/2 ≤ Fintype.card B := by rw [hB]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have h01 : (0 : ZMod 3)+1 = 1 := by decide
  have h12 : (1 : ZMod 3)+1 = 2 := by decide
  have h20 : (2 : ZMod 3)+1 = 0 := by decide
  have h02 : (0 : ZMod 3)-1 = 2 := by decide
  have h10 : (1 : ZMod 3)-1 = 0 := by decide
  have h21 : (2 : ZMod 3)-1 = 1 := by decide
  have hMem (v : A ⊕ B ⊕ W) (i : ZMod 3) :
      v ∈ repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) i ↔ repairPart v = i :=
    ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_univ v,h⟩⟩
  have hClass0 : (repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) 0).card =
      Fintype.card A := by
    let f : A ↪ A ⊕ B ⊕ W := ⟨Sum.inl,fun _ _ h => Sum.inl.inj h⟩
    have h : repairClass repairPart 0 = univ.map f := by
      ext v
      rw [hMem,mem_map]
      change repairPart v = 0 ↔ ∃ x : A, x ∈ univ ∧ Sum.inl x = v
      rcases v with a | (b | w) <;> simp [repairPart,show (2:ZMod 3) ≠ 0 by decide]
    rw [h,card_map,card_univ]
  have hClass1 : (repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) 1).card =
      Fintype.card B := by
    let f : B ↪ A ⊕ B ⊕ W :=
      ⟨fun b => .inr (.inl b),fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
    have h : repairClass repairPart 1 = univ.map f := by
      ext v
      rw [hMem,mem_map]
      change repairPart v = 1 ↔ ∃ x : B, x ∈ univ ∧ Sum.inr (Sum.inl x) = v
      rcases v with a | (b | w) <;> simp [repairPart,show (2:ZMod 3) ≠ 1 by decide]
    rw [h,card_map,card_univ]
  have hClass2 : (repairClass (repairPart : A ⊕ B ⊕ W → ZMod 3) 2).card =
      Fintype.card W := by
    let f : W ↪ A ⊕ B ⊕ W :=
      ⟨fun w => .inr (.inr w),fun _ _ h => Sum.inr.inj (Sum.inr.inj h)⟩
    have h : repairClass repairPart 2 = univ.map f := by
      ext v
      rw [hMem,mem_map]
      change repairPart v = 2 ↔ ∃ x : W, x ∈ univ ∧ Sum.inr (Sum.inr x) = v
      rcases v with a | (b | w) <;> simp [repairPart,
        show (0:ZMod 3) ≠ 2 by decide,show (1:ZMod 3) ≠ 2 by decide]
    rw [h,card_map,card_univ]
  constructor
  · intro a
    rw [card_tripartite_outNeighbors]
    rcases a with a | (b | w)
    · simpa only [repairPart,h01,hClass1] using dense_repair_slack hq₁ hB (hAB a)
    · simpa only [repairPart,h12,hClass2] using nearly_complete_repair_slack hq₂ hW (hBW b)
    · simpa only [repairPart,h20,hClass0] using nearly_complete_repair_slack hq₂ hHalfA (hWA w)
  · intro b
    rw [card_tripartite_inNeighbors]
    rcases b with a | (b | w)
    · simpa only [repairPart,h02,hClass2] using nearly_complete_repair_slack hq₂ hW (hAW a)
    · simpa only [repairPart,h10,hClass0] using dense_repair_slack hq₁ hA (hBA b)
    · simpa only [repairPart,h21,hClass1] using nearly_complete_repair_slack hq₂ hHalfB (hWB w)

end OverfullWork.ChenShan
