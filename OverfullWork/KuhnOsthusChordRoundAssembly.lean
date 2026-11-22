module

public import OverfullWork.KuhnOsthusChordCompletionMargins
public import OverfullWork.KuhnOsthusOriginalChordCycles

@[expose] public section


/-! Complete all chord rounds of Kühn–Osthus Lemma 9.7 in the
original vertex set. Only the unused physical base-cycle reserve
is passed between rounds. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical
universe u

/-- Ordinary contraction and expansion for every step of the
completion induction. Disjointness is required of the original
systems and the physical reserve. Shortcuts are local to a step. -/
theorem exists_original_chord_completions_of_cluster_budgets
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n q : ℕ}
      (B : Digraph V) (P : Fin q → Digraph V) (Z : Finset V)
      (c : ↥Zᶜ → Fin (n+1)) (m K : ℕ) (ε : ℝ),
      let s := finRotate (n+1)
      let A (j : Fin (n+1)) := (univ : Finset ↥Zᶜ).filter (fun v => c v = j)
      let F (i : Fin q) := basicExceptionalPathSystem (P i) Z
      N ≤ m → 0 ≤ ε → ε ≤ ρ/512 →
      (K:ℝ) ≤ (ρ/512)*(m:ℝ) → (q:ℝ) ≤ (ρ/128)^2*(m:ℝ)/16 →
      (∀ j, (A j).card = m) →
      (∀ j, IsSuperregularPair (induced B Zᶜ) ε ρ (A j) (A (s j))) →
      (∀ i, IsDirectedPathSystem (P i)) →
      (∀ i, CoversExceptional (P i) Z) →
      (∀ i x y, (P i).Adj x y → x ∈ Z → y ∉ Z) →
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      (∀ i, Disjoint (P i) B) →
      (∀ i j, (freeOut (F i) c j).card = (freeIn (F i) c (s j)).card) →
      (∀ i j, (finiteSatisfying (fun v => c v = j ∧ IncidentTo (F i) v)).card ≤ K) →
      ∃ G : Fin q → Equiv.Perm V,
        (∀ i, HasSpanningCycle (fun x y => G i x = y)) ∧
        (∀ i x y, (P i).Adj x y → G i x = y) ∧
        (∀ i x, (P i ⊔ B).Adj x (G i x)) ∧
        (∀ i j, i ≠ j → ∀ v, G i v ≠ G j v) ∧
        (⨆ i, P i) ≤ matchingUnion G := by
  obtain ⟨N,hN⟩ := exists_chord_completion_of_cluster_budgets.{u} ρ hρ hρ1
  refine ⟨N,?_⟩
  intro V _ n q B P Z c m K ε s A F hm hε hSmall hK hQ hA hPair hP hZ hNo hDis hReserve hBal hTouch
  apply exists_iterated_path_extensions B P hDis hReserve
  intro i L hLB hLoss
  have hOrdLe : induced L Zᶜ ≤ induced B Zᶜ := fun _ _ he => hLB he
  have hOrdLoss (v : ↥Zᶜ) :
      inDegree (induced L Zᶜ) v ≤ q ∧ outDegree (induced L Zᶜ) v ≤ q := by
    rw [induced_inDegree,induced_outDegree]
    exact ⟨(card_le_card inter_subset_right).trans
      ((inProfile_card L v.val).trans_le ((hLoss v.val).1.trans i.isLt.le)),
      (card_le_card inter_subset_right).trans
        ((outProfile_card L v.val).trans_le ((hLoss v.val).2.trans i.isLt.le))⟩
  obtain ⟨f,hCycle,hKeep,hEdge⟩ := hN (induced B Zᶜ) (induced L Zᶜ) (F i)
    c q m K ε hOrdLe hOrdLoss hm hε hSmall hK hQ hA hPair
    (basicExceptionalPathSystem.isDirectedPathSystem (hP i)) (hBal i) (hTouch i)
  exact expand_basic_exceptional_cycle (P i) (B \ L) Z (hP i) (hZ i) (hNo i) f hCycle hKeep hEdge

/-- Cycle removal with both exact coverage and the residue degree
of Lemma 9.7. This holds also when the residue degree is zero. -/
theorem chord_round_residue_degrees {V : Type*} [Fintype V] {q : ℕ}
    (B H U E : Digraph V) (Z : Finset V) (F : Fin q → Equiv.Perm V)
    (total : ℕ)
    (hPack : ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v)
    (hCover : H ⊔ U ⊔ E ≤ matchingUnion F)
    (hLe : matchingUnion F ≤ (H ⊔ U ⊔ E) ⊔ B)
    (hDeg : ∀ v, let d := if v ∈ Z then q else total
      inDegree ((H ⊔ U ⊔ E) ⊔ B) v = d ∧ outDegree ((H ⊔ U ⊔ E) ⊔ B) v = d) :
    let D := ((U ⊔ E) ⊔ B) \ matchingUnion F
    D ≤ B ∧
      D = ((H ⊔ U ⊔ E) ⊔ B) \ matchingUnion F ∧
      ∀ v, let d := if v ∈ Z then 0 else total-q
        inDegree D v = d ∧ outDegree D v = d := by
  intro D
  let W := (H ⊔ U ⊔ E) ⊔ B
  let M := matchingUnion F
  have hRest : D = W \ M := by
    ext x y
    constructor
    · rintro ⟨h,hM⟩
      refine ⟨?_,hM⟩
      rcases h with (hU | hE) | hB
      · exact Or.inl (Or.inl (Or.inr hU))
      · exact Or.inl (Or.inr hE)
      · exact Or.inr hB
    · rintro ⟨h,hM⟩
      refine ⟨?_,hM⟩
      rcases h with ((hH | hU) | hE) | hB
      · exact (hM (hCover (Or.inl (Or.inl hH)))).elim
      · exact Or.inl (Or.inl hU)
      · exact Or.inl (Or.inr hE)
      · exact Or.inr hB
  refine ⟨?_,hRest,?_⟩
  · rintro x y ⟨(hU | hE) | hB,hM⟩
    · exact (hM (hCover (Or.inl (Or.inr hU)))).elim
    · exact (hM (hCover (Or.inr hE))).elim
    · exact hB
  · intro v
    obtain ⟨hi,ho⟩ := residual_semidegrees W M hLe v
    obtain ⟨hiM,hoM⟩ := matchingUnion_exact_semidegrees F hPack v
    change inDegree M v = q at hiM
    change outDegree M v = q at hoM
    rw [←hRest,hiM,(hDeg v).1] at hi
    rw [←hRest,hoM,(hDeg v).2] at ho
    by_cases hv : v ∈ Z <;> simp only [hv,if_true,if_false] at hi ho ⊢ <;> omega

/-- The parameter arithmetic in the final semidegree calculation
of Lemma 9.7. -/
theorem chord_residue_degree_formula (r₁ r₂ r r₃ q s : ℕ) (hq : 0 < q) (hs : s = q*r₃) :
    r₁+r₂+r+r₃-s = r₁+r₂+r-(q-1)*r₃ := by
  have hq' := congrArg (fun v : ℕ => v*r₃) (Nat.sub_add_cancel (show 1 ≤ q by omega))
  rw [Nat.add_mul,one_mul] at hq'
  omega

/-- Before the cycle pack is removed, the four disjoint pieces
have the exact combined semidegrees used in Lemma 9.7. -/
theorem chord_absorption_input_degrees {V : Type*} [Fintype V]
    (B H U E : Digraph V) (Z : Finset V) (q s r₁ r₂ r₃ r : ℕ)
    (hs : s = q*r₃)
    (hHU : Disjoint H U) (hE : Disjoint (H ⊔ U) E) (hB : Disjoint (H ⊔ U ⊔ E) B)
    (hDegH : ∀ v, let d := if v ∈ Z then 0 else r
      inDegree H v = d ∧ outDegree H v = d)
    (hDegU : ∀ v, let d := if v ∈ Z then 0 else r₂
      inDegree U v = d ∧ outDegree U v = d)
    (hDegE : ∀ v, let d := if v ∈ Z then q*r₃ else r₃
      inDegree E v = d ∧ outDegree E v = d)
    (hDegB : ∀ v, let d := if v ∈ Z then 0 else r₁
      inDegree B v = d ∧ outDegree B v = d) :
    ∀ v, let d := if v ∈ Z then s else r₁+r₂+r+r₃
      inDegree ((H ⊔ U ⊔ E) ⊔ B) v = d ∧ outDegree ((H ⊔ U ⊔ E) ⊔ B) v = d := by
  intro v
  have add_degrees (A C : Digraph V) (h : Disjoint A C) :=
    degrees_sup_of_disjoint A C (fun _ _ he => disjoint_iff_inf_le.mp h he) v
  obtain ⟨hoB,hiB⟩ := add_degrees (H ⊔ U ⊔ E) B hB
  obtain ⟨hoE,hiE⟩ := add_degrees (H ⊔ U) E hE
  obtain ⟨hoU,hiU⟩ := add_degrees H U hHU
  rw [hoB,hiB,hoE,hiE,hoU,hiU,(hDegH v).1,(hDegH v).2,(hDegU v).1,(hDegU v).2,
    (hDegE v).1,(hDegE v).2,(hDegB v).1,(hDegB v).2]
  by_cases hv : v ∈ Z <;> simp [hv,hs,Nat.add_comm,Nat.add_left_comm]

end OverfullWork.DirectedRobustExpansion
