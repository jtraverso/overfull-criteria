module

public import OverfullWork.ChenShanNestedAbsorptionStep
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

private theorem card_eq_of_unique_relation {X Y : Type*} [Fintype X] [Fintype Y]
    (P : X → Prop) (Q : Y → Prop) (R : X → Y → Prop)
    (hSupport : ∀ x y, R x y → P x ∧ Q y)
    (hX : ∀ x, P x → ∃! y, R x y) (hY : ∀ y, Q y → ∃! x, R x y) :
    Fintype.card {x // P x} = Fintype.card {y // Q y} := by
  let f (x : {x // P x}) : {y // Q y} :=
    ⟨(hX x.1 x.2).exists.choose, (hSupport _ _ (hX x.1 x.2).exists.choose_spec).2⟩
  have hR (x : {x // P x}) : R x.1 (f x).1 := (hX x.1 x.2).exists.choose_spec
  apply Fintype.card_congr (Equiv.ofBijective f ⟨?_,?_⟩)
  · intro x x' he
    obtain ⟨z,_,hz⟩ := hY (f x).1 (f x).2
    have hx' : R x'.1 (f x).1 := by rw [he]; exact hR x'
    exact Subtype.ext ((hz _ (hR x)).trans (hz _ hx').symm)
  · intro y
    obtain ⟨x,hxy,_⟩ := hY y.1 y.2
    let a : {x // P x} := ⟨x,(hSupport x y hxy).1⟩
    obtain ⟨z,_,hz⟩ := hX x a.2
    exact ⟨a,Subtype.ext ((hz _ (hR a)).trans (hz _ hxy).symm)⟩

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]

/-- Exact triangle coverage pairs the two kinds of incident edges
at every vertex. -/
theorem TripartiteTriangleDecomposition.locallyBalanced
    {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}
    (D : TripartiteTriangleDecomposition E L R) : TripartiteLocallyBalanced E L R := by
  refine ⟨?_,?_,?_⟩
  · intro a
    exact card_eq_of_unique_relation (E a) (L a) (D.triangle a)
      (fun b w ht => ⟨(D.supported a b w ht).1,(D.supported a b w ht).2.1⟩)
      (D.coversBase a) (D.coversLeft a)
  · intro b
    exact card_eq_of_unique_relation (fun a => E a b) (R b) (fun a w => D.triangle a b w)
      (fun a w ht => ⟨(D.supported a b w ht).1,(D.supported a b w ht).2.2⟩)
      (fun a => D.coversBase a b) (D.coversRight b)
  · intro w
    exact card_eq_of_unique_relation (fun a => L a w) (fun b => R b w)
      (fun a b => D.triangle a b w) (fun a b ht => (D.supported a b w ht).2)
      (fun a => D.coversLeft a w) (fun b => D.coversRight b w)

private theorem sdiff_preserves_inside {V : Type*}
    {G H : Finset (V × V)} {U : Finset V} (hD : Disjoint H (U ×ˢ U)) :
    (G \ H) ∩ (U ×ˢ U) = G ∩ (U ×ˢ U) := by
  ext e
  simp only [mem_inter,mem_sdiff]
  constructor
  · rintro ⟨⟨hG,_⟩,hU⟩
    exact ⟨hG,hU⟩
  · rintro ⟨hG,hU⟩
    exact ⟨⟨hG,fun hH => disjoint_left.mp hD hH hU⟩,hU⟩

/-- The starting state of (4.22). Deleting the absorber preserves
local balance and the induced graph on the first proper prefix. -/
theorem absorber_sdiff_initial_state {V : Type*}
    (G H : Finset (V × V)) (U : Finset V) (Bnd : ℝ)
    (hBal : ArcBalanced G) (hAbsBal : ArcBalanced H)
    (hSub : H ⊆ G) (hDisj : Disjoint H (U ×ˢ U))
    (hDegree : ∀ v, (incidentDegree H v : ℝ) ≤ Bnd) :
    let G₀ := G \ H
    ArcBalanced G₀ ∧ G₀ ∩ (U ×ˢ U) = G ∩ (U ×ˢ U) ∧
      (∀ v, (incidentDegree (G \ G₀) v : ℝ) ≤ Bnd) := by
  dsimp only
  refine ⟨arcBalanced_sdiff hSub hBal hAbsBal, sdiff_preserves_inside hDisj,?_⟩
  intro v
  have hLost : G \ (G \ H) = H := by
    ext e
    simp only [mem_sdiff]
    have h : e ∈ H → e ∈ G := fun he => hSub he
    tauto
  rw [hLost]
  exact hDegree v

end OverfullWork.ChenShan
