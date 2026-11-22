module

public import OverfullWork.KuhnOsthusResidualExtender
public import OverfullWork.KuhnOsthusPreprocessingAssembly

@[expose] public section


/-! Apply the residual extender on the ordinary vertices in each
iteration, and keep the exact regular residue of Corollary 8.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset InducedDigraphSampling
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem induced_reserve_deletion_degrees {D : Digraph V} (Z : Finset V) (k : ℕ)
    (h : ∀ v, inDegree D v ≤ k ∧ outDegree D v ≤ k) (v : ↥Zᶜ) :
    inDegree (induced D Zᶜ) v ≤ k ∧ outDegree (induced D Zᶜ) v ≤ k := by
  rw [induced_inDegree,induced_outDegree]
  exact ⟨(card_le_card inter_subset_right).trans ((inProfile_card D v.val).trans_le (h v.val).1),
    (card_le_card inter_subset_right).trans ((outProfile_card D v.val).trans_le (h v.val).2)⟩

omit [Fintype V] in
private theorem induced_sdiff_eq (A B : Digraph V) (Z : Finset V) :
    induced (A \ B) Z = induced A Z \ induced B Z := by
  ext x y
  rfl

/-- Lemma 8.4 and Corollary 8.5 with the bounded extension property
supplied by the common physical extender on the ordinary vertices. -/
theorem kuhn_osthus_preprocessing_of_residual_extender
    {r l t : ℕ} {label : V → Fin 50} {Z : Finset V}
    (P H R : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l)
    (hRegH : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hRegP : ∀ v, let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
      inDegree P v+r = a ∧ outDegree P v+r = a)
    (hLoop : ∀ v, ¬ H.Adj v v)
    (hIndependent : ∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y)
    (hDisPH : Disjoint P H)
    (hCSub : ∀ j, (C j).digraph ≤ P)
    (hRSub : R ≤ P)
    (hDisRC : ∀ j, Disjoint (C j).digraph R)
    (hDisC : ∀ i j, i ≠ j → Disjoint (C i).digraph (C j).digraph)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1))
    (hExtend : HasBoundedPathExtension (induced R Zᶜ) (fun v => label v.val)
      ⌊1230 * (Fintype.card V : ℝ) / (50*l+1)⌋₊ (r*(50*l+1))) :
    ∃ F : Fin (r*(50*l+1)) → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      H ⊔ (⨆ j, (C j).digraph) ≤ matchingUnion F ∧
      matchingUnion F ≤ P ⊔ H ∧
      let D := (P ⊔ H) \ matchingUnion F
      (∀ x y, D.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
      ∀ v : ↥Zᶜ, inDegree (induced D Zᶜ) v = t ∧ outDegree (induced D Zᶜ) v = t := by
  apply kuhn_osthus_preprocessing_assembly P H R C hRegH hRegP hLoop hIndependent
    hDisPH hCSub hRSub hDisRC hDisC hL hN hZ
  intro Q L hSub hQ hCover hSize hStyles _ hBudget
  have hNo (x y : V) (h : Q.Adj x y) (hx : x ∈ Z) : y ∉ Z := by
    rcases (Digraph.sup_adj _ _ _ _).mp (hSub h) with hH | hE
    · exact fun hy => hIndependent x y hx hy hH
    · obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp hE
      obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp hj
      exact (C j).no_internal i hi hx
  obtain ⟨S,hS,hSupport⟩ := hStyles
  obtain ⟨hStyle,hCard⟩ := basicExceptionalPathSystem.bounds hQ hSupport
  have hBSize : Fintype.card (Arc (basicExceptionalPathSystem Q Z)) ≤
      ⌊1230 * (Fintype.card V : ℝ) / (50*l+1)⌋₊ := by
    exact hCard.trans (Nat.le_floor hSize)
  obtain ⟨σ,hHam,hKeep,hEdges⟩ := hExtend _ (induced L Zᶜ)
    (basicExceptionalPathSystem.isDirectedPathSystem hQ) hBSize ⟨S,hS,hStyle⟩
    (induced_reserve_deletion_degrees Z _ hBudget)
  apply expand_basic_exceptional_cycle Q (R \ L) Z hQ hCover hNo σ hHam hKeep
  simpa only [induced_sdiff_eq] using hEdges

end OverfullWork.DirectedRobustExpansion
