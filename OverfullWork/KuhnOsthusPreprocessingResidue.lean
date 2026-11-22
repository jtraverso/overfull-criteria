module

public import OverfullWork.HamiltonResidueAssembly
public import OverfullWork.InducedDigraphSampling

@[expose] public section


/-! After the path-system extender has supplied its Hamilton cycles,
Kühn–Osthus Corollary 8.5 leaves an exact regular factor on the
nonexceptional vertices. The exceptional vertices are isolated. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem delete_sup_of_disjoint (D H : Digraph V) (h : Disjoint D H) :
    (D ⊔ H) \ H = D := by
  ext x y
  rw [Digraph.sdiff_adj,Digraph.sup_adj]
  constructor
  · rintro ⟨hD | hH,hn⟩
    · exact hD
    · exact (hn hH).elim
  · intro hd
    exact ⟨Or.inl hd,fun hh => (disjoint_iff_inf_le.mp h) ⟨hd,hh⟩⟩

/-- Once the preprocessing cycles cover the entire approximate residue,
only preprocessing arcs are left. Their two semidegrees are zero on
the exceptional vertices and equal to the absorber input elsewhere. -/
theorem preprocessing_residue_degrees
    (P H : Digraph V) (Z : Finset V) (r k t : ℕ)
    (F : Fin k → Equiv.Perm V)
    (hDis : Disjoint P H)
    (hRegH : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hRegP : ∀ v, let a := if v ∈ Z then k else k+t
      inDegree P v+r = a ∧ outDegree P v+r = a)
    (hCycleSupport : ∀ i v, (P ⊔ H).Adj v (F i v))
    (hPack : ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v)
    (hCover : H ≤ matchingUnion F) :
    let R := P \ matchingUnion F
    R = (P ⊔ H) \ matchingUnion F ∧
    (∀ v, inDegree R v = (if v ∈ Z then 0 else t) ∧
      outDegree R v = (if v ∈ Z then 0 else t)) ∧
    ∀ x y, R.Adj x y → x ∉ Z ∧ y ∉ Z := by
  let R := P \ matchingUnion F
  have hEq : R = (P ⊔ H) \ matchingUnion F := by
    ext x y
    simp only [R,Digraph.sdiff_adj,Digraph.sup_adj]
    constructor
    · exact fun ⟨hp,hn⟩ => ⟨Or.inl hp,hn⟩
    · rintro ⟨hp | hh,hn⟩
      · exact ⟨hp,hn⟩
      · exact (hn (hCover hh)).elim
  have hUnion : matchingUnion F ≤ P ⊔ H := by
    rintro x y ⟨i,rfl⟩
    exact hCycleSupport i x
  have hDegrees (v : V) :
      inDegree R v = (if v ∈ Z then 0 else t) ∧
      outDegree R v = (if v ∈ Z then 0 else t) := by
    obtain ⟨h₁,h₂⟩ := residual_semidegrees (P ⊔ H) H le_sup_right v
    rw [delete_sup_of_disjoint _ _ hDis,(hRegH v).1] at h₁
    rw [delete_sup_of_disjoint _ _ hDis,(hRegH v).2] at h₂
    obtain ⟨h₃,h₄⟩ := residual_semidegrees (P ⊔ H) (matchingUnion F) hUnion v
    rw [←hEq,(matchingUnion_exact_semidegrees F hPack v).1] at h₃
    rw [←hEq,(matchingUnion_exact_semidegrees F hPack v).2] at h₄
    have hp := hRegP v
    by_cases hv : v ∈ Z <;> simp only [hv,if_true,if_false] at hp ⊢ <;> omega
  refine ⟨hEq,hDegrees,?_⟩
  intro x y h
  constructor
  · intro hx
    have he : outDegree R x = 0 := by simpa only [hx,if_true] using (hDegrees x).2
    have hPos : 0 < outDegree R x := by
      letI : DecidablePred (R.Adj x) := Classical.decPred _
      exact card_pos.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,h⟩⟩
    omega
  · intro hy
    have he : inDegree R y = 0 := by simpa only [hy,if_true] using (hDegrees y).1
    have hPos : 0 < inDegree R y := by
      letI : DecidablePred (fun v => R.Adj v y) := Classical.decPred _
      exact card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,h⟩⟩
    omega

/-- Removing the isolated exceptional vertices preserves the prescribed
semidegrees on the complement. -/
theorem preprocessing_complement_factor (R : Digraph V) (Z : Finset V) (t : ℕ)
    (hSupport : ∀ x y, R.Adj x y → x ∉ Z ∧ y ∉ Z)
    (hDeg : ∀ v ∉ Z, inDegree R v = t ∧ outDegree R v = t) :
    let H := InducedDigraphSampling.induced R Zᶜ
    ∀ x : ↥Zᶜ, inDegree H x = t ∧ outDegree H x = t := by
  intro H x
  let e : ↥Zᶜ ↪ V := Function.Embedding.subtype _
  have hEq (P : V → Prop) (hP : ∀ y, P y → y ∉ Z) :
      ((univ : Finset ↥Zᶜ).filter (fun y => P y.val)).map e =
        (univ : Finset V).filter P := by
    ext y
    simp only [mem_map,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hy
      exact ⟨⟨y,mem_compl.mpr (hP y hy)⟩,hy,rfl⟩
  have hi := congrArg Finset.card (hEq (fun y => R.Adj y x.val) (fun y h => (hSupport y x.val h).1))
  have ho := congrArg Finset.card (hEq (R.Adj x.val) (fun y h => (hSupport x.val y h).2))
  simp only [card_map] at hi ho
  exact ⟨hi.trans (hDeg x.val (mem_compl.mp x.property)).1,
    ho.trans (hDeg x.val (mem_compl.mp x.property)).2⟩

end OverfullWork.DirectedRobustExpansion
