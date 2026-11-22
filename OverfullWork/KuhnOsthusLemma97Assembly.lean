module

public import OverfullWork.KuhnOsthusChordRoundBudgets
public import OverfullWork.KuhnOsthusPreparedChordSystems

@[expose] public section


/-! The complete iteration and edge accounting of Kühn–Osthus
Lemma 9.7 once the path systems of each round have been prepared. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open scoped Classical
universe u

/-- Assemble the rounds of Lemma 9.7. The cycles consume all arcs
assigned to the rounds. Their remaining arcs come from the
base-cycle reserve, and the unused graph has the stated degree. -/
theorem kuhn_osthus_lemma_9_7_of_prepared_rounds (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {n : ℕ}
      (B H U E : Digraph V) (Z : Finset V) (c : ↥Zᶜ → Fin (n+1))
      (r f q r₁ r₂ r₃ m K : ℕ) (ε : ℝ),
      let q' := f*(n+1)
      let s := r*q'
      let next := finRotate (n+1)
      let P := H ⊔ U ⊔ E
      let A (j : Fin (n+1)) := (univ : Finset ↥Zᶜ).filter (fun v => c v = j)
      ∀ Q : PreparedChordSystems P Z c next K (Fin r × Fin q'),
      N ≤ m → 0 ≤ ε → ε ≤ ρ/512 → (K:ℝ) ≤ (ρ/512)*(m:ℝ) →
      r*(n+1)*f^2 ≤ m → (16:ℝ) ≤ (ρ/128)^2*(f:ℝ) →
      0 < q → s = q*r₃ →
      (∀ j, (A j).card = m) →
      (∀ j, IsSuperregularPair (induced B Zᶜ) ε ρ (A j) (A (next j))) →
      Disjoint P B →
      (∀ x y, B.Adj x y → ∃ a b : ↥Zᶜ, a.val = x ∧ b.val = y ∧ c b = next (c a)) →
      (∀ v, let d := if v ∈ Z then s else r₁+r₂+r+r₃
        inDegree (P ⊔ B) v = d ∧ outDegree (P ⊔ B) v = d) →
      ∃ F : Fin s → Equiv.Perm V,
        (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
        (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
        P ≤ matchingUnion F ∧ matchingUnion F ≤ P ⊔ B ∧
        (∀ i, basicExceptionalPathSystem (Q.system i) Z ≤
          basicExceptionalPathSystem (matchingUnion (fun _ : Fin 1 => F (finProdFinEquiv i))) Z) ∧
        let D := ((U ⊔ E) ⊔ B) \ matchingUnion F
        D = (P ⊔ B) \ matchingUnion F ∧
        (∀ x y, D.Adj x y → ∃ a b : ↥Zᶜ, a.val = x ∧ b.val = y ∧ c b = next (c a)) ∧
        ∀ v, let d := if v ∈ Z then 0 else r₁+r₂+r-(q-1)*r₃
          inDegree D v = d ∧ outDegree D v = d := by
  obtain ⟨N,hN⟩ := exists_original_chord_completions_of_cluster_budgets.{u} ρ hρ hρ1
  refine ⟨N,?_⟩
  intro V _ n B H U E Z c r f q r₁ r₂ r₃ m K ε q' s next P A Q hm hε hSmall hK hSize hF hq hs
    hA hPairs hDisB hSupp hDeg
  let e : Fin r × Fin q' ≃ Fin s := finProdFinEquiv
  let S := Q.reindex e.symm
  have hLe (i : Fin s) : S.system i ≤ P := S.le i
  have hDis (i j : Fin s) (hij : i ≠ j) : Disjoint (S.system i) (S.system j) := by
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    obtain ⟨k,_,hOwner⟩ := S.owns x y (hLe i hxy.1)
    exact (hij ((hOwner _ hxy.1).trans (hOwner _ hxy.2).symm)).elim
  obtain ⟨F,hC,hKeep,hEdges,hPack,hCovered⟩ := hN B S.system Z c m K ε hm hε hSmall hK
    (chord_round_count_budget r f (n+1) m ρ hSize hF) hA hPairs
    S.path S.covers S.no_internal hDis (fun i => hDisB.mono_left (hLe i)) S.balance S.footprint
  have hAll : P ≤ matchingUnion F := by
    intro x y hp
    obtain ⟨i,hi,_⟩ := S.owns x y hp
    exact hCovered (Digraph.iSup_adj.mpr ⟨i,hi⟩)
  have hR : matchingUnion F ≤ P ⊔ B := by
    rintro x y ⟨i,rfl⟩
    exact sup_le_sup_right (hLe i) _ (hEdges i x)
  have hBasic (i : Fin r × Fin q') :
      basicExceptionalPathSystem (Q.system i) Z ≤
        basicExceptionalPathSystem (matchingUnion (fun _ : Fin 1 => F (e i))) Z := by
    have hQ x y (he : (Q.system i).Adj x y) : (matchingUnion (fun _ : Fin 1 => F (e i))).Adj x y :=
      ⟨0,hKeep (e i) x y (by simpa only [S,PreparedChordSystems.reindex,e.symm_apply_apply] using he)⟩
    rintro x y (he | ⟨z,hz,hxz,hzy⟩)
    · exact Or.inl (hQ _ _ he)
    · exact Or.inr ⟨z,hz,hQ _ _ hxz,hQ _ _ hzy⟩
  obtain ⟨hRB,hEq,hDegrees⟩ :=
    chord_round_residue_degrees B H U E Z F (r₁+r₂+r+r₃) hPack hAll hR hDeg
  rw [chord_residue_degree_formula r₁ r₂ r r₃ q s hq hs] at hDegrees
  exact ⟨F,hC,hPack,hAll,hR,hBasic,hEq,fun x y h => hSupp x y (hRB h),hDegrees⟩

/-- The residue sent to the cycle absorber has a factorization in
which every permutation follows the base successor. -/
theorem chord_residue_successor_factorization {V I : Type*} [Fintype V]
    (D : Digraph V) (Z : Finset V) (c : ↥Zᶜ → I) (s : Equiv.Perm I) (t : ℕ)
    (hSupport : ∀ x y, D.Adj x y → ∃ a b : ↥Zᶜ, a.val = x ∧ b.val = y ∧ c b = s (c a))
    (hDeg : ∀ v ∉ Z, inDegree D v = t ∧ outDegree D v = t) :
    ∃ F : Fin t → Equiv.Perm ↥Zᶜ, matchingUnion F = induced D Zᶜ ∧
      (∀ i x, c (F i x) = s (c x)) ∧ ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v := by
  have hOrd (x y : V) (h : D.Adj x y) : x ∉ Z ∧ y ∉ Z := by
    obtain ⟨a,b,rfl,rfl,_⟩ := hSupport x y h
    exact ⟨mem_compl.mp a.prop,mem_compl.mp b.prop⟩
  obtain ⟨F,hF,hApart⟩ := exists_permutation_factorization_of_regular (induced D Zᶜ) t
    (preprocessing_complement_factor D Z t hOrd hDeg)
  refine ⟨F,hF,?_,hApart⟩
  intro i x
  have hx : (induced D Zᶜ).Adj x (F i x) := hF ▸ (show (matchingUnion F).Adj x (F i x) from ⟨i,rfl⟩)
  obtain ⟨a,b,ha,hb,hs⟩ := hSupport x.val (F i x).val hx
  rwa [show a = x from Subtype.ext ha,show b = F i x from Subtype.ext hb] at hs

end OverfullWork.DirectedRobustExpansion
