module

public import OverfullWork.OsthusStadenMergeConfiguration

@[expose] public section


/-! Invoke the verified merge theorem on the actual finite set of red
pairs. No artificial equality between the number of pairs and factors
is necessary. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u v
variable {V : Type u} [Fintype V] {R : Type v}

structure RotationReserve {k : ℕ} (F : Fin k → Equiv.Perm V) (cut : R → Finset V) where
  pair : ∀ a, Digraph ↥(cut a)
  target : ∀ a, ↥(cut a) ↪ V
  matching : ∀ a, Fin k → Equiv.Perm ↥(cut a)
  agrees : ∀ a f (x : cut a), F f x.val = target a (matching a f x)

/-- The bounds needed by the merge lemma on a particular rotation
family. The size bound comes from the uniform merge theorem. -/
structure RotationReserveMargins {k : ℕ} {F : Fin k → Equiv.Perm V} {cut : R → Finset V}
    (D : RotationReserve F cut) (d ε ν τ γ : ℝ) (N : ℕ) : Prop where
  size : ∀ a, (cut a).Nonempty ∧ N ≤ (cut a).card
  cutBudget : ∀ a, (k:ℝ)+ν*((cut a).card:ℝ) ≤ d*τ*((cut a).card:ℝ)
  degreeBudget : ∀ a, γ*((cut a).card:ℝ)+(k:ℝ) ≤ d*((cut a).card:ℝ)
  rectangles : ∀ a, ∀ X Y : Finset ↥(cut a),
    ε*((cut a).card:ℝ) ≤ (X.card:ℝ) → ε*((cut a).card:ℝ) ≤ (Y.card:ℝ) →
    d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences (D.pair a) X Y:ℝ)
  inBound : ∀ a x, d*((cut a).card:ℝ) ≤ (inDegree (D.pair a) x:ℝ)
  outBound : ∀ a x, d*((cut a).card:ℝ) ≤ (outDegree (D.pair a) x:ℝ)

private theorem eqvGen_reindex {R J : Type*} (e : R ≃ J) (r : R → R → Prop)
    {a b : R} (h : Relation.EqvGen r a b) :
    Relation.EqvGen (fun i j => r (e.symm i) (e.symm j)) (e a) (e b) := by
  induction h with
  | rel x y h => exact .rel _ _ (by simpa only [e.symm_apply_apply] using h)
  | refl x => exact .refl _
  | symm x y _ ih => exact .symm _ _ ih
  | trans x y z _ _ ih ih' => exact .trans _ _ _ ih ih'

/-- Merge a whole rotation family from the covered cuts and their
common link relation, with the resulting arc choices exposed. -/
theorem exists_indexed_hamilton_batch (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {R : Type v} [Fintype R] {k : ℕ}
      (F : Fin k → Equiv.Perm V) (cut : R → Finset V) (D : RotationReserve F cut)
      (r : R → R → Prop) (root : R),
      RotationReserveMargins D d ε ν τ γ N →
      (∀ f g, f ≠ g → ∀ v, F f v ≠ F g v) →
      (∀ a b, a ≠ b → Disjoint (cut a) (cut b)) →
      (∀ a, Relation.EqvGen r root a) →
      (∀ f x, ∃ a, touchesCut (F f) (cut a) x) →
      (∀ f a b, r a b → OsthusStadenLink (F f) cut a b) →
      ∃ G : Fin k → Equiv.Perm V,
        (∀ f, HasSpanningCycle (fun x y => G f x = y)) ∧
        (∀ f g, f ≠ g → ∀ x, G f x ≠ G g x) ∧
        (∀ f x, (∀ a, x ∉ cut a) → G f x = F f x) ∧
        ∀ a, ∃ M : Fin k → Equiv.Perm ↥(cut a),
          (∀ f x, (D.pair a).Adj x (M f x)) ∧
          ∀ f (x : cut a), G f x.val = D.target a (M f x) := by
  obtain ⟨N,hN⟩ := exists_hamilton_batch_of_merge_reserves.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro V _ R _ k F cut D r root hm hOrig hDis hConn hCover hLink
  let e := Fintype.equivFin R
  let S := cut ∘ e.symm
  let rel := fun i j => r (e.symm i) (e.symm j)
  have hConn' (i : Fin (Fintype.card R)) : Relation.EqvGen rel (e root) i := by
    have h := eqvGen_reindex e r (hConn (e.symm i))
    simpa only [e.apply_symm_apply] using h
  obtain ⟨G,hG,hGDis,hKeep,hNew⟩ := hN F S (fun i => D.pair (e.symm i))
    (fun i => D.target (e.symm i)) (fun i => D.matching (e.symm i)) rel (e root)
    (fun i => D.agrees (e.symm i)) hOrig
    (fun i j h => hDis _ _ (fun he => h (e.symm.injective he)))
    (fun i => hm.size (e.symm i)) (fun i => hm.cutBudget (e.symm i))
    (fun i => hm.degreeBudget (e.symm i)) (fun i => hm.rectangles (e.symm i))
    (fun i => hm.inBound (e.symm i)) (fun i => hm.outBound (e.symm i)) hConn'
    (fun f x => by
      obtain ⟨a,ha⟩ := hCover f x
      exact ⟨e a,by simpa only [S,Function.comp_apply,e.symm_apply_apply] using ha⟩)
    (fun f i j h => by
      obtain ⟨x,y,hx,hy,L,hxL,hyL,hL⟩ := (hLink f _ _ h).bridge
      refine ⟨x,y,hx,hy,L,hxL,hyL,?_⟩
      exact hL.imp (fun _ _ hz => ⟨fun m => hz.1 (e.symm m),hz.2⟩))
  refine ⟨G,hG,hGDis,fun f x h => hKeep f x (fun i => h (e.symm i)),?_⟩
  intro a
  obtain ⟨i,rfl⟩ := e.symm.surjective a
  exact hNew i

end OverfullWork.DirectedRobustExpansion
