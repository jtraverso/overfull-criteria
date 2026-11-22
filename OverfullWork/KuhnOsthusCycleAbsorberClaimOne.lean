module

public import OverfullWork.KuhnOsthusOrderedClusterPaths
public import OverfullWork.KuhnOsthusAlternatingSwitchOrder

@[expose] public section


/-! Physical Claim 1 of Kühn–Osthus Lemma 10.3. Cluster indices
start at zero, so the two switch pairs are 3→4 and 7→8. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
universe u
variable {V : Type u}

def alternateCycleAbsorberSwitchSlot (m : ℕ) : Fin m × Fin 2 ≃ Fin (2*m) :=
  (cycleAbsorberSwitchSlot m).trans (finRotate (2*m))

theorem alternate_cycle_absorber_switch_slot_next {m : ℕ} (i : Fin m) :
    finRotate (2*m) (alternateCycleAbsorberSwitchSlot m (i,0)) =
      alternateCycleAbsorberSwitchSlot m (i,1) :=
  congrArg (finRotate (2*m)) (cycleAbsorberSwitchSlot_next i)

/-- Every pair of cyclically consecutive labels appears in its
prescribed switch family, including the last and first labels. -/
theorem cycle_absorber_switch_covers_successors {m : ℕ} (j : Fin (2*m)) :
    (∃ i, j = cycleAbsorberSwitchSlot m (i,0) ∧
        finRotate (2*m) j = cycleAbsorberSwitchSlot m (i,1)) ∨
      ∃ i, j = alternateCycleAbsorberSwitchSlot m (i,0) ∧
        finRotate (2*m) j = alternateCycleAbsorberSwitchSlot m (i,1) := by
  obtain ⟨⟨i,a⟩,rfl⟩ := (cycleAbsorberSwitchSlot m).surjective j
  fin_cases a
  · exact Or.inl ⟨i,rfl,cycleAbsorberSwitchSlot_next i⟩
  · have h : cycleAbsorberSwitchSlot m (i,1) = alternateCycleAbsorberSwitchSlot m (i,0) :=
      (cycleAbsorberSwitchSlot_next i).symm
    exact Or.inr ⟨i,h,(congrArg (finRotate (2*m)) h).trans (alternate_cycle_absorber_switch_slot_next i)⟩

/-- The path bundle and the two ordered sets of four-arc switches. -/
structure CycleAbsorberClaimOne (G : Digraph V) (A : ℕ → Finset V) (m n : ℕ) where
  paths : OrderedClusterPaths G A (Fin (2*m)) 0 n
  first : OrderedSwitchCopies G (A 3) (A 4) m (cycleAbsorberSwitchSlot m)
  second : OrderedSwitchCopies G (A 7) (A 8) m (alternateCycleAbsorberSwitchSlot m)
  firstSource : ∀ j, paths.vertex 3 j = (first.source j).val
  firstTarget : ∀ j, paths.vertex 4 j = (first.target j).val
  secondSource : ∀ j, paths.vertex 7 j = (second.source j).val
  secondTarget : ∀ j, paths.vertex 8 j = (second.target j).val

/-- The vertices in the four slots of the two families are all distinct
as physical vertices, including across the two different pairs. -/
theorem CycleAbsorberClaimOne.copies_disjoint {G : Digraph V} {A : ℕ → Finset V} {m n : ℕ}
    (C : CycleAbsorberClaimOne G A m n) (hn : 8 ≤ n)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (i j : Fin m) (a b : Fin 4) : C.first.copies (i,a) ≠ C.second.copies (j,b) := by
  let left (p : Fin 4) : ℕ := if p.val < 2 then 3 else 4
  let right (p : Fin 4) : ℕ := if p.val < 2 then 7 else 8
  have hl (p : Fin 4) : C.first.copies (i,p) ∈ A (left p) := by
    fin_cases p
    · exact C.first.source_zero i ▸ (C.first.source _).prop
    · exact C.first.source_one i ▸ (C.first.source _).prop
    · exact C.first.target_zero i ▸ (C.first.target _).prop
    · exact C.first.target_one i ▸ (C.first.target _).prop
  have hr (p : Fin 4) : C.second.copies (j,p) ∈ A (right p) := by
    fin_cases p
    · exact C.second.source_zero j ▸ (C.second.source _).prop
    · exact C.second.source_one j ▸ (C.second.source _).prop
    · exact C.second.target_zero j ▸ (C.second.target _).prop
    · exact C.second.target_one j ▸ (C.second.target _).prop
  have hd : Disjoint (A (left a)) (A (right b)) := hDis _ _
    (by dsimp [left]; split <;> omega) (by dsimp [right]; split <;> omega)
    (by dsimp [left,right]; split <;> split <;> omega)
  intro he
  exact disjoint_left.mp hd (hl a) (he.symm ▸ hr b)

/-- At a switch layer, an arc between two label positions is on a
path precisely when both positions carry that path's label. -/
theorem OrderedClusterPaths.arc_between_labels {G : Digraph V} {A : ℕ → Finset V} {J : Type*} {l r : ℕ}
    (P : OrderedClusterPaths G A J l r)
    (hDis : ∀ i k, l ≤ i → i ≤ r → l ≤ k → k ≤ r → i ≠ k → Disjoint (A i) (A k))
    {i : ℕ} (hi : l ≤ i) (hi' : i < r) (a b j : J) :
    (P.pathDigraph j).Adj (P.vertex i a) (P.vertex (i+1) b) ↔ a = j ∧ b = j := by
  constructor
  · rintro ⟨k,hk,hk',hs,ht⟩
    obtain ⟨rfl,ha⟩ := P.unique_coordinates hDis hi hi'.le hk hk'.le hs
    exact ⟨ha,P.injective (i+1) (by omega) (by omega) ht⟩
  · rintro ⟨rfl,rfl⟩
    exact ⟨i,hi,hi',rfl,rfl⟩

/-- The diagonal edges of each first switch are the only switch
edges in the path bundle. Each is on the indicated path. -/
theorem CycleAbsorberClaimOne.first_arc_on_path {G : Digraph V} {A : ℕ → Finset V} {m n : ℕ}
    (C : CycleAbsorberClaimOne G A m n) (hn : 4 ≤ n)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (i : Fin m) (a b : Fin 2) (j : Fin (2*m)) :
    (C.paths.pathDigraph j).Adj (C.first.source (cycleAbsorberSwitchSlot m (i,a)))
        (C.first.target (cycleAbsorberSwitchSlot m (i,b))) ↔
      cycleAbsorberSwitchSlot m (i,a) = j ∧ cycleAbsorberSwitchSlot m (i,b) = j := by
  rw [←C.firstSource,←C.firstTarget]
  exact C.paths.arc_between_labels (fun i k _ hi _ hk h => hDis i k hi hk h)
    (by decide) (by omega) _ _ _

theorem CycleAbsorberClaimOne.second_arc_on_path {G : Digraph V} {A : ℕ → Finset V} {m n : ℕ}
    (C : CycleAbsorberClaimOne G A m n) (hn : 8 ≤ n)
    (hDis : ∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j))
    (i : Fin m) (a b : Fin 2) (j : Fin (2*m)) :
    (C.paths.pathDigraph j).Adj (C.second.source (alternateCycleAbsorberSwitchSlot m (i,a)))
        (C.second.target (alternateCycleAbsorberSwitchSlot m (i,b))) ↔
      alternateCycleAbsorberSwitchSlot m (i,a) = j ∧ alternateCycleAbsorberSwitchSlot m (i,b) = j := by
  rw [←C.secondSource,←C.secondTarget]
  exact C.paths.arc_between_labels (fun i k _ hi _ hk h => hDis i k hi hk h)
    (by decide) (by omega) _ _ _

/-- Construct the Claim 1 paths with arbitrary initial and terminal
orders, the two switch families, and the exact label in every slot. -/
theorem kuhn_osthus_lemma_10_3_claim_one (C ε ε' d : ℝ)
    (hC : 0 < C) (hε : 0 < ε) (hTol : 4*ε ≤ ε') (hGap : 2*ε' < d) (hd : d ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (A : ℕ → Finset V) (m n r s : ℕ),
      11 ≤ n → 0 < m → N ≤ 2*m → 2*(Fintype.card V:ℝ) ≤ C*((2*m:ℕ):ℝ) →
      (∀ i ≤ n, (A i).card = 2*m) →
      (∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (A i) (A j)) →
      (∀ i < n, IsLowerSuperregularPair G ε d (A i) (A (i+1))) →
      0 < r → (m:ℝ)*ε' ≤ (r:ℝ) → 28*((r:ℝ)+1) < (d-2*ε')^14*((d-ε')*(m:ℝ)) →
      0 < s → ((2*m:ℕ):ℝ)*ε ≤ (s:ℝ) → 28*((s:ℝ)+1) < (d-2*ε)^14*((d-ε)*((2*m:ℕ):ℝ)) →
      ∀ (e : Fin (2*m) ≃ A 0) (f : Fin (2*m) ≃ A n),
      ∃ Q : CycleAbsorberClaimOne G A m n,
        (∀ j, Q.paths.vertex 0 j = (e j).val) ∧ ∀ j, Q.paths.vertex n j = (f j).val := by
  obtain ⟨N,hN⟩ := kuhn_osthus_spanning_switch_copies.{u} C ε ε' d hC hε hTol hGap hd
  refine ⟨N,?_⟩
  intro V _ G A m n r s hn hm hNm hProfiles hSize hDis hPairs hr hCut hBudget hs hCut' hBudget' e f
  obtain ⟨u,hu,huE,huA,huB⟩ := hN G (A 3) (A 4) m r hm hNm
    (hSize 3 (by omega)) (hSize 4 (by omega)) (hDis 3 4 (by omega) (by omega) (by decide))
    hProfiles (hPairs 3 (by omega)) hr hCut hBudget
  obtain ⟨v,hv,hvE,hvA,hvB⟩ := hN G (A 7) (A 8) m r hm hNm
    (hSize 7 (by omega)) (hSize 8 (by omega)) (hDis 7 8 (by omega) (by omega) (by decide))
    hProfiles (hPairs 7 (by omega)) hr hCut hBudget
  let U := OrderedSwitchCopies.of_spanning (cycleAbsorberSwitchSlot m) u hu huE huA huB
  let W := OrderedSwitchCopies.of_spanning (alternateCycleAbsorberSwitchSlot m) v hv hvE hvA hvB
  let M₀ := OrderedClusterPaths.of_pair G A 3 U.source U.target U.matching
  let M₁ := OrderedClusterPaths.of_pair G A 7 W.source W.target W.matching
  have hd' : 2*ε < d := by linarith
  have route (a b : ℕ) (hab : a+3 ≤ b) (hb : b ≤ n) (l : Fin (2*m) ≃ A a) (r' : Fin (2*m) ≃ A b) :=
    exists_ordered_cluster_paths G A a b (2*m) s hab l r' ε d hε.le hd' hd hs hCut' hBudget'
      (fun i _ hi => hSize i (hi.trans hb))
      (fun i j _ hi _ hj he => hDis i j (hi.trans hb) (hj.trans hb) he)
      (fun i _ hi => hPairs i (hi.trans_le hb))
  obtain ⟨P₀,hP₀,hP₃⟩ := route 0 3 (by decide) (by omega) e U.source
  obtain ⟨P₁,hP₄,hP₇⟩ := route 4 7 (by decide) (by omega) U.target W.source
  obtain ⟨P₂,hP₈,hPn⟩ := route 8 n (by omega) le_rfl W.target f
  let T₁ := M₁.concat P₂ (fun j => by simp [M₁,hP₈ j])
  let T₂ := P₁.concat T₁ (fun j => by simp [T₁,OrderedClusterPaths.concat_left,hP₇ j,M₁])
  let T₃ := M₀.concat T₂ (fun j => by simp [T₂,OrderedClusterPaths.concat_left,hP₄ j,M₀])
  let T := P₀.concat T₃ (fun j => by simp [T₃,OrderedClusterPaths.concat_left,hP₃ j,M₀])
  refine ⟨⟨T,U,W,?_,?_,?_,?_⟩,?_,?_⟩
  · intro j
    simp [T,OrderedClusterPaths.concat_left,hP₃ j]
  · intro j
    rw [show T.vertex 4 j = T₃.vertex 4 j from
      OrderedClusterPaths.concat_right _ _ _ (by decide) j]
    simp [T₃,OrderedClusterPaths.concat_left,M₀]
  · intro j
    have h₁ : T.vertex 7 j = T₃.vertex 7 j := OrderedClusterPaths.concat_right _ _ _ (by decide) j
    have h₂ : T₃.vertex 7 j = T₂.vertex 7 j := OrderedClusterPaths.concat_right _ _ _ (by decide) j
    rw [h₁,h₂]
    simp [T₂,OrderedClusterPaths.concat_left,hP₇ j]
  · intro j
    have h₁ : T.vertex 8 j = T₃.vertex 8 j := OrderedClusterPaths.concat_right _ _ _ (by decide) j
    have h₂ : T₃.vertex 8 j = T₂.vertex 8 j := OrderedClusterPaths.concat_right _ _ _ (by decide) j
    have h₃ : T₂.vertex 8 j = T₁.vertex 8 j := OrderedClusterPaths.concat_right _ _ _ (by decide) j
    rw [h₁,h₂,h₃]
    simp [T₁,OrderedClusterPaths.concat_left,M₁]
  · intro j
    change T.vertex 0 j = (e j).val
    simp [T,OrderedClusterPaths.concat_left,hP₀ j]
  · intro j
    change T.vertex n j = (f j).val
    have h₁ : T.vertex n j = T₃.vertex n j := OrderedClusterPaths.concat_right _ _ _ (by omega) j
    have h₂ : T₃.vertex n j = T₂.vertex n j := OrderedClusterPaths.concat_right _ _ _ (by omega) j
    have h₃ : T₂.vertex n j = T₁.vertex n j := OrderedClusterPaths.concat_right _ _ _ (by omega) j
    have h₄ : T₁.vertex n j = P₂.vertex n j := OrderedClusterPaths.concat_right _ _ _ (by omega) j
    rw [h₁,h₂,h₃,h₄,hPn j]

end OverfullWork.DirectedRobustExpansion
