module

public import OverfullWork.FactorMergeLocalBatch
public import OverfullWork.SequentialFactorMerges

@[expose] public section


/-! Merge a batch of factors on the same disjoint selected pairs.
Fixed target labels allow arc-disjoint replacements across factors. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
theorem exists_sequential_batch_cut_merges {k : ℕ} (σ : Fin k → Equiv.Perm V) (n : ℕ)
    (S : Fin n → Finset V) (D : ∀ i, Digraph (↑(S i)))
    (target : ∀ i, ↑(S i) ↪ V) (p : ∀ i, Fin k → Equiv.Perm (↑(S i)))
    (hTarget : ∀ i j (x : S i), σ j x.val = target i (p i j x))
    (hDis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hStep : ∀ i (ρ : Fin k → Equiv.Perm V), ∃ M : Fin k → Equiv.Perm (↑(S i)),
      (∀ j x, (D i).Adj x (M j x)) ∧
      (∀ j l, j ≠ l → ∀ x, M j x ≠ M l x) ∧
      ∀ j, let ρ' := replacedSuccessor (ρ j) (S i) ((M j).trans (p i j).symm)
        (∀ x y, (ρ j).SameCycle x y → ρ'.SameCycle x y) ∧
        ∀ x ∈ S i, ∀ y ∈ S i, ρ'.SameCycle x y) :
    ∃ ρ : Fin k → Equiv.Perm V,
      (∀ j x y, (σ j).SameCycle x y → (ρ j).SameCycle x y) ∧
      (∀ j i, ∀ x ∈ S i, ∀ y ∈ S i, (ρ j).SameCycle x y) ∧
      (∀ j x, (∀ i, x ∉ S i) → ρ j x = σ j x) ∧
      ∀ i, ∃ M : Fin k → Equiv.Perm (↑(S i)),
        (∀ j x, (D i).Adj x (M j x)) ∧
        (∀ j l, j ≠ l → ∀ x, M j x ≠ M l x) ∧
        ∀ j (x : S i), ρ j x.val = target i (M j x) := by
  induction n with
  | zero => exact ⟨σ,fun _ _ _ h => h,fun _ i => i.elim0,fun _ _ _ => rfl,fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨ρ,hOld,hDone,hKeep,hUsed⟩ := ih (fun i => S i.castSucc)
      (fun i => D i.castSucc) (fun i => target i.castSucc) (fun i => p i.castSucc)
      (fun i => hTarget i.castSucc)
      (fun i j h => hDis _ _ (fun he => h (Fin.castSucc_injective _ he))) (fun i => hStep i.castSucc)
    let i := Fin.last n
    obtain ⟨M,hM,hApart,hMerge⟩ := hStep i ρ
    let F := fun j => (M j).trans (p i j).symm
    let ρ' := fun j => replacedSuccessor (ρ j) (S i) (F j)
    have hOff (a : Fin n) : Disjoint (S a.castSucc) (S i) := hDis _ _ (Fin.castSucc_ne_last a)
    refine ⟨ρ',fun j x y h => (hMerge j).1 x y (hOld j x y h),?_,?_,?_⟩
    · intro j l
      refine Fin.lastCases (hMerge j).2
        (fun a x hx y hy => (hMerge j).1 x y (hDone j a x hx y hy)) l
    · intro j x hx
      exact (replacedSuccessor_of_not_mem (ρ j) (S i) (F j) (hx i)).trans (hKeep j x (fun a => hx a.castSucc))
    · intro l
      refine Fin.lastCases ?_ (fun a => ?_) l
      · refine ⟨M,hM,hApart,fun j x => ?_⟩
        calc
          ρ' j x.val = ρ j (F j x).val := replacedSuccessor_at _ _ _ _
          _ = σ j (F j x).val := hKeep j _ (fun a hm => disjoint_left.mp (hOff a) hm (F j x).prop)
          _ = target i (M j x) := by rw [hTarget i j]; simp [F]
      · obtain ⟨B,hB,hBDis,hArc⟩ := hUsed a
        exact ⟨B,hB,hBDis,fun j x => (replacedSuccessor_of_not_mem (ρ j) (S i) (F j)
          (fun hm => disjoint_left.mp (hOff a) x.prop hm)).trans (hArc j x)⟩

/-- With the bridge paths verified for each factor, the sequential
replacements produce a batch of pairwise arc-disjoint Hamilton cycles. -/
theorem exists_batch_cycles_of_cut_merges {k n : ℕ} (σ : Fin k → Equiv.Perm V)
    (S : Fin n → Finset V) (D : ∀ i, Digraph (↑(S i)))
    (target : ∀ i, ↑(S i) ↪ V) (p : ∀ i, Fin k → Equiv.Perm (↑(S i)))
    (hTarget : ∀ i j (x : S i), σ j x.val = target i (p i j x))
    (hOriginal : ∀ j l, j ≠ l → ∀ v, σ j v ≠ σ l v)
    (hDis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (r : Fin n → Fin n → Prop) (i₀ : Fin n)
    (hNonempty : ∀ i, (S i).Nonempty) (hConnected : ∀ i, Relation.EqvGen r i₀ i)
    (hCover : ∀ j x, ∃ i, touchesCut (σ j) (S i) x)
    (hBridge : ∀ j i l, r i l → ∃ x y, touchesCut (σ j) (S i) x ∧ touchesCut (σ j) (S l) y ∧
      ∃ L : List V, x ∈ L ∧ y ∈ L ∧ L.IsChain (fun a b => (∀ m, a ∉ S m) ∧ σ j a = b))
    (hStep : ∀ i (ρ : Fin k → Equiv.Perm V), ∃ M : Fin k → Equiv.Perm (↑(S i)),
      (∀ j x, (D i).Adj x (M j x)) ∧
      (∀ j l, j ≠ l → ∀ x, M j x ≠ M l x) ∧
      ∀ j, let ρ' := replacedSuccessor (ρ j) (S i) ((M j).trans (p i j).symm)
        (∀ x y, (ρ j).SameCycle x y → ρ'.SameCycle x y) ∧
        ∀ x ∈ S i, ∀ y ∈ S i, ρ'.SameCycle x y) :
    ∃ ρ : Fin k → Equiv.Perm V, (∀ j, HasSpanningCycle (fun x y => ρ j x = y)) ∧
      (∀ j l, j ≠ l → ∀ v, ρ j v ≠ ρ l v) ∧
      (∀ j x, (∀ i, x ∉ S i) → ρ j x = σ j x) ∧
      ∀ i, ∃ M : Fin k → Equiv.Perm (↑(S i)),
        (∀ j x, (D i).Adj x (M j x)) ∧ ∀ j (x : S i), ρ j x.val = target i (M j x) := by
  obtain ⟨ρ,hOld,hDone,hKeep,hUsed⟩ := exists_sequential_batch_cut_merges σ n S D target p hTarget hDis hStep
  refine ⟨ρ,fun j => spanning_cycle_of_cut_merge_bridges (σ j) (ρ j) S r i₀ hNonempty hConnected
    (hCover j) (hOld j) (hDone j) (hKeep j) (hBridge j),?_,hKeep,?_⟩
  · intro j l hjl v he
    by_cases h : ∃ i, v ∈ S i
    · obtain ⟨i,hi⟩ := h
      obtain ⟨M,_,hMDis,hArc⟩ := hUsed i
      exact hMDis j l hjl ⟨v,hi⟩ ((target i).injective
        ((hArc j ⟨v,hi⟩).symm.trans (he.trans (hArc l ⟨v,hi⟩))))
    · have hOut (i : Fin n) : v ∉ S i := fun hi => h ⟨i,hi⟩
      exact hOriginal j l hjl v ((hKeep j v hOut).symm.trans (he.trans (hKeep l v hOut)))
  · intro i
    obtain ⟨M,hM,_,hArc⟩ := hUsed i
    exact ⟨M,hM,hArc⟩

/-- A block of the merging stage in Osthus–Staden §5.11. Each pair
has a common reserve, and it supplies separate arcs to each factor. -/
theorem exists_hamilton_batch_of_merge_reserves (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {k n : ℕ} (σ : Fin k → Equiv.Perm W)
      (S : Fin n → Finset W) (D : ∀ i, Digraph (↑(S i)))
      (target : ∀ i, ↑(S i) ↪ W) (p : ∀ i, Fin k → Equiv.Perm (↑(S i)))
      (r : Fin n → Fin n → Prop) (i₀ : Fin n),
      (∀ i j (x : S i), σ j x.val = target i (p i j x)) →
      (∀ j l, j ≠ l → ∀ v, σ j v ≠ σ l v) →
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, (S i).Nonempty ∧ N ≤ (S i).card) →
      (∀ i, (k:ℝ)+ν*((S i).card:ℝ) ≤ d*τ*((S i).card:ℝ)) →
      (∀ i, γ*((S i).card:ℝ)+(k:ℝ) ≤ d*((S i).card:ℝ)) →
      (∀ i, ∀ A B : Finset (↑(S i)), ε*((S i).card:ℝ) ≤ (A.card:ℝ) →
        ε*((S i).card:ℝ) ≤ (B.card:ℝ) →
        d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences (D i) A B:ℝ)) →
      (∀ i v, d*((S i).card:ℝ) ≤ (inDegree (D i) v:ℝ)) →
      (∀ i v, d*((S i).card:ℝ) ≤ (outDegree (D i) v:ℝ)) →
      (∀ i, Relation.EqvGen r i₀ i) → (∀ j x, ∃ i, touchesCut (σ j) (S i) x) →
      (∀ j i l, r i l → ∃ x y, touchesCut (σ j) (S i) x ∧ touchesCut (σ j) (S l) y ∧
        ∃ L : List W, x ∈ L ∧ y ∈ L ∧ L.IsChain (fun a b => (∀ m, a ∉ S m) ∧ σ j a = b)) →
      ∃ ρ : Fin k → Equiv.Perm W, (∀ j, HasSpanningCycle (fun x y => ρ j x = y)) ∧
        (∀ j l, j ≠ l → ∀ v, ρ j v ≠ ρ l v) ∧
        (∀ j x, (∀ i, x ∉ S i) → ρ j x = σ j x) ∧
        ∀ i, ∃ M : Fin k → Equiv.Perm (↑(S i)),
          (∀ j x, (D i).Adj x (M j x)) ∧ ∀ j (x : S i), ρ j x.val = target i (M j x) := by
  obtain ⟨N,hN⟩ := exists_batch_coarsening_on_pair.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ k n σ S D target p r i₀ hTarget hOriginal hDis hn hCost hDeg hRect hIn hOut hConn hCover hBridge
  exact exists_batch_cycles_of_cut_merges σ S D target p hTarget hOriginal hDis r i₀
    (fun i => (hn i).1) hConn hCover hBridge (fun i ρ =>
      hN (S i) (D i) k ρ (p i) (hn i).2 (hCost i) (hDeg i) (hRect i) (hIn i) (hOut i))

end OverfullWork.DirectedRobustExpansion
