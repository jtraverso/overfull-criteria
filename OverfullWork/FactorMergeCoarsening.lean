module

public import OverfullWork.SinglePairFactorMerge

@[expose] public section


/-! A replacement combines whole old orbits. Away from the chosen
sources, both the successor and every unchanged path are preserved. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset Function
open scoped Classical
universe u
variable {V : Type u}

theorem sameCycle_of_successor_chain (σ : Equiv.Perm V) {l : List V}
    (h : l.IsChain (fun x y => σ x = y)) {x y : V} (hx : x ∈ l) (hy : y ∈ l) :
    σ.SameCycle x y := by
  have fromHead (a : V) (t : List V) (hc : (a :: t).IsChain (fun x y => σ x = y))
      (w : V) (hw : w ∈ a :: t) : σ.SameCycle a w := by
    induction t generalizing a with
    | nil =>
      have he : w = a := List.mem_singleton.mp hw
      subst w
      exact Equiv.Perm.SameCycle.refl σ a
    | cons b t ih =>
      rcases List.mem_cons.mp hw with rfl | hw'
      · exact Equiv.Perm.SameCycle.refl σ w
      · have he : σ a = b := hc.rel
        exact (he ▸ (Equiv.Perm.SameCycle.refl σ a).apply_right).trans
          (ih b hc.tail hw')
  cases l with
  | nil => simp at hx
  | cons a t => exact (fromHead a t h x hx).symm.trans (fromHead a t h y hy)

theorem replacedSuccessor_of_not_mem (σ : Equiv.Perm V) (S : Finset V)
    (M : Equiv.Perm (↑S)) {x : V} (hx : x ∉ S) :
    replacedSuccessor σ S M x = σ x :=
  (replaceCutMatching_adj_iff σ S M x _).mp (Or.inl ⟨hx,rfl⟩)

theorem replacedSuccessor_at (σ : Equiv.Perm V) (S : Finset V)
    (M : Equiv.Perm (↑S)) (x : S) :
    replacedSuccessor σ S M x.val = σ (M x).val :=
  (replaceCutMatching_adj_iff σ S M x.val _).mp (Or.inr ⟨x,rfl,rfl⟩)

theorem coarsening_of_touched_cycle [Fintype V] (σ : Equiv.Perm V) (S : Finset V)
    (M : Equiv.Perm (↑S)) (T : List V) (z : V)
    (hChain : (T ++ [z]).IsChain (replaceCutMatching σ S M).Adj)
    (hSupport : ∀ v, v ∈ T ↔ touchesCut σ S v) :
    (∀ x y, σ.SameCycle x y → (replacedSuccessor σ S M).SameCycle x y) ∧
    ∀ x y, touchesCut σ S x → touchesCut σ S y → (replacedSuccessor σ S M).SameCycle x y := by
  let ρ := replacedSuccessor σ S M
  have hMerge (x y : V) (hx : touchesCut σ S x) (hy : touchesCut σ S y) :
      ρ.SameCycle x y := sameCycle_of_successor_chain ρ
    (hChain.imp fun a b => (replaceCutMatching_adj_iff σ S M a b).mp)
    (List.mem_append_left _ ((hSupport x).mpr hx)) (List.mem_append_left _ ((hSupport y).mpr hy))
  refine ⟨?_,hMerge⟩
  intro x y hxy
  by_cases hx : touchesCut σ S x
  · exact hMerge x y hx ((touchesCut_congr hxy).mp hx)
  · obtain ⟨n,_,hn⟩ := hxy.exists_pow_eq'
    have hPow (k : ℕ) : (ρ^k) x = (σ^k) x := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,ih]
        apply replacedSuccessor_of_not_mem
        intro hk
        exact hx ⟨(σ^k) x,hk,(Equiv.Perm.SameCycle.refl σ x).pow_right⟩
    rw [←hn,←hPow n]
    exact (Equiv.Perm.SameCycle.refl ρ x).pow_right

end OverfullWork.DirectedRobustExpansion
