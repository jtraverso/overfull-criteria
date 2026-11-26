module

public import OverfullWork.ChenShanFractionalCorrection
public import OverfullWork.ChenShanTrianglePackingLeave

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

private noncomputable def outgoingDegree {V : Type*} (G : Finset (V × V)) (v : V) : ℕ :=
  (G.filter (fun e => e.1 = v)).card

private theorem incidentDegree_eq_two_outgoing {V : Type*} (G : Finset (V × V))
    (hb : ArcBalanced G) (hn : ∀ e ∈ G, e.1 ≠ e.2) (v : V) :
    incidentDegree G v = 2 * outgoingDegree G v := by
  let P : Finset (V × V) := G.filter (fun e => e.1 = v)
  let Q : Finset (V × V) := G.filter (fun e => e.2 = v)
  have hFilter : (G.filter (fun e => e.1 = v ∨ e.2 = v)) = P ∪ Q := by
    ext e
    simp only [P,Q,mem_filter,mem_union]
    tauto
  have hDisjoint : Disjoint P Q := by
    apply disjoint_left.mpr
    intro e heP heQ
    have h₁ := mem_filter.mp heP
    have h₂ := mem_filter.mp heQ
    exact hn e h₁.1 (h₁.2.trans h₂.2.symm)
  rw [incidentDegree,hFilter,card_union_of_disjoint hDisjoint]
  change P.card + Q.card = 2 * P.card
  have hEq : P.card = Q.card := hb v
  omega

private theorem tripartite_outdegree (v : A ⊕ B ⊕ W) :
    outgoingDegree (tripartiteArcs E L R) v =
      match v with
      | .inl a => (univ.filter (E a)).card
      | .inr (.inl b) => (univ.filter (R b)).card
      | .inr (.inr w) => (univ.filter (fun a => L a w)).card := by
  unfold outgoingDegree tripartiteArcs
  rw [filter_filter,card_filter,Fintype.sum_prod_type,Fintype.sum_sum_type]
  rcases v with a | (b | w) <;>
    simp [Fintype.sum_sum_type,tripartiteArc,card_filter,ite_and,-Finset.sum_boole]
  all_goals
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    have hSwap (p q : Prop) [Decidable p] [Decidable q] :
        (if p then (if q then (1 : ℕ) else 0) else 0) =
          (if q then (if p then (1 : ℕ) else 0) else 0) := by
      by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]
    simp_rw [hSwap _ (_ = _)]
    simp

theorem DenseTripartite.incidentDegree_bounds {m : ℕ} {η ε : ℝ}
    (h : DenseTripartite E L R m η ε) (hη : 0 ≤ η) (hε : ε ≤ 1/2)
    (hk : (Fintype.card W : ℝ) ≤ 2 * m) (v : A ⊕ B ⊕ W) :
    (m : ℝ) ≤ incidentDegree (tripartiteArcs E L R) v ∧
      (incidentDegree (tripartiteArcs E L R) v : ℝ) ≤ 4 * m := by
  have hNoLoop e (he : e ∈ tripartiteArcs E L R) : e.1 ≠ e.2 := by
    rcases e with ⟨x,y⟩
    intro hEq
    change x = y at hEq
    subst y
    have he' := mem_tripartiteArcs.mp he
    rcases x with a | (b | w) <;> exact he'
  rw [incidentDegree_eq_two_outgoing _ (arcBalanced_of_tripartiteLocallyBalanced h.balanced)
    hNoLoop,tripartite_outdegree,Nat.cast_mul,Nat.cast_ofNat]
  have hηm : 0 ≤ η * (m : ℝ) := by positivity
  rcases v with a | (b | w)
  · dsimp only
    have hCap : ((univ.filter (E a)).card : ℝ) ≤ m := by
      rw [← h.sizeB]
      exact_mod_cast (card_filter_le _ _).trans_eq card_univ
    have hLower := h.degreeA a
    constructor <;> linarith only [hCap,hLower,hηm,Nat.cast_nonneg (α := ℝ) m]
  · dsimp only
    have hBalance : (univ.filter (fun a => E a b)).card = (univ.filter (R b)).card := by
      simpa only [Fintype.card_subtype] using h.balanced.2.1 b
    have hLower := h.degreeB b
    rw [hBalance] at hLower
    have hCap : ((univ.filter (R b)).card : ℝ) ≤ (Fintype.card W : ℝ) := by
      exact_mod_cast (card_filter_le _ _).trans_eq card_univ
    constructor <;> linarith only [hCap,hLower,hηm,hk]
  · dsimp only
    have hTotal := card_filter_add_card_filter_not (s := (univ : Finset A)) (fun a => L a w)
    rw [card_univ,h.sizeA] at hTotal
    have hTotal' : ((univ.filter (fun a => L a w)).card : ℝ) +
        ((univ.filter (fun a => ¬ L a w)).card : ℝ) = m := by exact_mod_cast hTotal
    have hMiss := h.missingWA w
    have hεm := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg (α := ℝ) m)
    constructor <;> linarith only [hTotal',hMiss,hεm,
      Nat.cast_nonneg (α := ℝ) m,
      Nat.cast_nonneg (α := ℝ) (univ.filter (fun a => ¬ L a w)).card]

end OverfullWork.ChenShan
