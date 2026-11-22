module

public import OverfullWork.FactorMergeCoarsening
public import OverfullWork.MergeConnectedCycles

@[expose] public section


/-! Compose replacements on distinct source sets. Every old arc outside
their union survives, and old cycles can only coalesce. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

omit [Fintype V] in
theorem exists_sequential_cut_merges (σ : Equiv.Perm V) (n : ℕ)
    (S : Fin n → Finset V) (D : ∀ i, Digraph (↑(S i)))
    (hDis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hStep : ∀ i (ρ : Equiv.Perm V), ∃ M : Equiv.Perm (↑(S i)),
      (∀ x, (D i).Adj x (M x)) ∧
      (∀ x y, ρ.SameCycle x y → (replacedSuccessor ρ (S i) M).SameCycle x y) ∧
      ∀ x ∈ S i, ∀ y ∈ S i, (replacedSuccessor ρ (S i) M).SameCycle x y) :
    ∃ ρ : Equiv.Perm V,
      (∀ x y, σ.SameCycle x y → ρ.SameCycle x y) ∧
      (∀ i, ∀ x ∈ S i, ∀ y ∈ S i, ρ.SameCycle x y) ∧
      (∀ x, (∀ i, x ∉ S i) → ρ x = σ x) ∧
      ∀ i, ∃ M : Equiv.Perm (↑(S i)), (∀ x, (D i).Adj x (M x)) ∧
        ∀ x : S i, ρ x.val = σ (M x).val := by
  induction n with
  | zero =>
    exact ⟨σ,fun _ _ h => h,fun i => i.elim0,fun _ _ => rfl,fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨ρ,hOld,hDone,hKeep,hUse⟩ := ih (fun i => S i.castSucc)
      (fun i => D i.castSucc)
      (fun i j h => hDis _ _ (fun he => h (Fin.castSucc_injective _ he)))
      (fun i => hStep i.castSucc)
    let j := Fin.last n
    obtain ⟨M,hM,hGrow,hMerge⟩ := hStep j ρ
    let ρ' := replacedSuccessor ρ (S j) M
    have hApart (i : Fin n) : Disjoint (S i.castSucc) (S j) :=
      hDis _ _ (Fin.castSucc_ne_last i)
    refine ⟨ρ',fun x y h => hGrow x y (hOld x y h),?_,?_,?_⟩
    · intro i
      refine Fin.lastCases hMerge (fun a x hx y hy => hGrow x y (hDone a x hx y hy)) i
    · intro x hx
      exact (replacedSuccessor_of_not_mem ρ (S j) M (hx j)).trans
        (hKeep x (fun i => hx i.castSucc))
    · intro i
      refine Fin.lastCases ?_ (fun a => ?_) i
      · refine ⟨M,hM,fun x => (replacedSuccessor_at ρ (S j) M x).trans ?_⟩
        exact hKeep _ (fun a hm => disjoint_left.mp (hApart a) hm (M x).prop)
      · obtain ⟨F,hF,hArc⟩ := hUse a
        exact ⟨F,hF,fun x => (replacedSuccessor_of_not_mem ρ (S j) M
          (fun hm => disjoint_left.mp (hApart a) x.prop hm)).trans (hArc x)⟩

omit [Fintype V] in
/-- Only nonterminal vertices of a bridge path need to avoid the cuts. -/
theorem bridgeChain_of_dropLast {n : ℕ} (σ : Equiv.Perm V) (S : Fin n → Finset V)
    (L : List V) (hChain : L.IsChain (fun a b => σ a = b))
    (hOff : ∀ v ∈ L.dropLast, ∀ i, v ∉ S i) :
    L.IsChain (fun a b => (∀ i, a ∉ S i) ∧ σ a = b) := by
  apply List.isChain_iff_getElem.mpr
  intro j hj
  have hj' : j < L.dropLast.length := by rw [List.length_dropLast]; omega
  have hm : L[j] ∈ L.dropLast := by
    rw [←List.getElem_dropLast hj']
    exact List.getElem_mem _
  exact ⟨hOff _ hm,List.isChain_iff_getElem.mp hChain j hj⟩

/-- Paths between consecutive positions of an enumeration suffice for
connectivity of the selected pairs. -/
theorem cutOrder_connected (n : ℕ) (i : Fin (n+1)) :
    Relation.EqvGen (fun a b : Fin (n+1) => a.val+1 = b.val) 0 i := by
  induction i using Fin.induction with
  | zero => exact Relation.EqvGen.refl _
  | succ j ih =>
    exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ rfl)

/-- The bridge paths of Lemma 4.5(iii) use only unchanged successors.
The equivalence closure records which selected pairs they connect. -/
theorem spanning_cycle_of_cut_merge_bridges {n : ℕ} (σ ρ : Equiv.Perm V)
    (S : Fin n → Finset V) (r : Fin n → Fin n → Prop) (i₀ : Fin n)
    (hNonempty : ∀ i, (S i).Nonempty) (hConnected : ∀ i, Relation.EqvGen r i₀ i)
    (hCover : ∀ x, ∃ i, touchesCut σ (S i) x)
    (hOld : ∀ x y, σ.SameCycle x y → ρ.SameCycle x y)
    (hMerged : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i, ρ.SameCycle x y)
    (hKeep : ∀ x, (∀ i, x ∉ S i) → ρ x = σ x)
    (hBridge : ∀ i j, r i j → ∃ x y, touchesCut σ (S i) x ∧ touchesCut σ (S j) y ∧
      ∃ l : List V, x ∈ l ∧ y ∈ l ∧ l.IsChain (fun a b => (∀ k, a ∉ S k) ∧ σ a = b)) :
    HasSpanningCycle (fun x y => ρ x = y) := by
  choose rep hrep using hNonempty
  have hToRep (i : Fin n) (v : V) (hv : touchesCut σ (S i) v) : ρ.SameCycle v (rep i) := by
    obtain ⟨w,hw,hvw⟩ := hv
    exact (hOld v w hvw).trans (hMerged i w hw (rep i) (hrep i))
  have hConnect (i j : Fin n) (h : Relation.EqvGen r i j) : ρ.SameCycle (rep i) (rep j) := by
    induction h with
    | rel i j h =>
      obtain ⟨x,y,hx,hy,l,hxl,hyl,hChain⟩ := hBridge i j h
      have hPath := sameCycle_of_successor_chain ρ
        (hChain.imp fun a _ h => (hKeep a h.1).trans h.2) hxl hyl
      exact (hToRep i x hx).symm.trans (hPath.trans (hToRep j y hy))
    | refl => exact Equiv.Perm.SameCycle.refl _ _
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  apply spanning_cycle_of_single_orbit ρ (rep i₀)
  intro v
  obtain ⟨i,hi⟩ := hCover v
  exact (hConnect i₀ i (hConnected i)).trans (hToRep i v hi).symm

/-- The multi-pair merge with the quantitative reserve hypotheses and the
unchanged bridge paths of Osthus–Staden Lemma 4.5. The returned matchings
use the original target labels of each selected pair. -/
theorem exists_multi_pair_factor_merge (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1)
    (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] (σ : Equiv.Perm W) (n : ℕ)
      (S : Fin n → Finset W) (D H : ∀ i, Digraph (↑(S i))) (k : Fin n → ℕ)
      (r : Fin n → Fin n → Prop) (i₀ : Fin n),
      (∀ i, (S i).Nonempty ∧ N ≤ (S i).card) →
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, H i ≤ D i) →
      (∀ i, (k i:ℝ)+ν*((S i).card:ℝ) ≤ d*τ*((S i).card:ℝ)) →
      (∀ i, γ*((S i).card:ℝ)+(k i:ℝ) ≤ d*((S i).card:ℝ)) →
      (∀ i, ∀ A B : Finset (↑(S i)), ε*((S i).card:ℝ) ≤ (A.card:ℝ) →
        ε*((S i).card:ℝ) ≤ (B.card:ℝ) →
        d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences (D i) A B:ℝ)) →
      (∀ i v, d*((S i).card:ℝ) ≤ (inDegree (D i) v:ℝ)) →
      (∀ i v, d*((S i).card:ℝ) ≤ (outDegree (D i) v:ℝ)) →
      (∀ i v, inDegree (H i) v ≤ k i ∧ outDegree (H i) v ≤ k i) →
      (∀ x, ∃ i, touchesCut σ (S i) x) → (∀ i, Relation.EqvGen r i₀ i) →
      (∀ i j, r i j → ∃ x y, touchesCut σ (S i) x ∧ touchesCut σ (S j) y ∧
        ∃ l : List W, x ∈ l ∧ y ∈ l ∧ l.IsChain (fun a b => (∀ l, a ∉ S l) ∧ σ a = b)) →
      ∃ ρ : Equiv.Perm W, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x, (∀ i, x ∉ S i) → ρ x = σ x) ∧
        ∀ i, ∃ M : Equiv.Perm (↑(S i)), (∀ x, ((D i) \ (H i)).Adj x (M x)) ∧
          ∀ x : S i, ρ x.val = σ (M x).val := by
  obtain ⟨N,hN⟩ := exists_touched_cycle_merge.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ σ n S D H k r i₀ hn hDis hLe hCost hDegrees hRect hIn hOut hLoss hCover hConn hBridge
  have hStep (i : Fin n) (ρ : Equiv.Perm W) : ∃ M : Equiv.Perm (↑(S i)),
      (∀ x, ((D i) \ (H i)).Adj x (M x)) ∧
      (∀ x y, ρ.SameCycle x y → (replacedSuccessor ρ (S i) M).SameCycle x y) ∧
      ∀ x ∈ S i, ∀ y ∈ S i, (replacedSuccessor ρ (S i) M).SameCycle x y := by
    obtain ⟨M,hM,T,z,_,_,hChain,hSupport⟩ := hN ρ (S i) (D i) (H i) (k i)
      (hn i).2 (hLe i) (hCost i) (hDegrees i) (hRect i) (hIn i) (hOut i) (hLoss i)
    obtain ⟨hOld,hMerged⟩ := coarsening_of_touched_cycle ρ _ M T z hChain hSupport
    exact ⟨M,hM,hOld,fun x hx y hy => hMerged x y (touchesCut_of_mem ρ hx) (touchesCut_of_mem ρ hy)⟩
  obtain ⟨ρ,hOld,hMerged,hKeep,hUse⟩ := exists_sequential_cut_merges σ n S
    (fun i => D i \ H i) hDis hStep
  exact ⟨ρ,spanning_cycle_of_cut_merge_bridges σ ρ S r i₀ (fun i => (hn i).1) hConn
    hCover hOld hMerged hKeep hBridge,hKeep,hUse⟩

end OverfullWork.DirectedRobustExpansion
