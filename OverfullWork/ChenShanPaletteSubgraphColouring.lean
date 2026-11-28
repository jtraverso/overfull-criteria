module

public import OverfullWork.ChenShanCriticalCore
public import OverfullWork.ChenShanPaletteBudgetAssembly
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem multiplicity_le_endpoint_degree (M : MultiGraph V) (x v : V) :
    M.mult s(x,v) ≤ M.degree v := by
  rw [M.degree_eq_sum_mult, Sym2.eq_swap]
  exact single_le_sum (f := fun y => M.mult s(v,y)) (fun _ _ => Nat.zero_le _) (mem_univ x)

/-- The coloring step in §5.1.4. Given a coloring of the edges between
exceptional vertices and the core edges at inactive exceptional vertices,
extend it in existence to a coloring of the entire selected multigraph
with the same palette size. -/
theorem palette_subgraph_colourable_of_active_degrees
    (G base : MultiGraph V) (U active : Finset V) (k a : ℕ)
    (hDisj : Disjoint U active) (hLarge : 2*a < k)
    (hDegrees : ∀ v, G.degree v ≤ k) (hCore : ∀ v ∈ U, G.degree v ≤ a)
    (hActive : ∀ v ∈ active, 2*a < G.degreeInto U v)
    (hBase : ∀ u v, ¬ (u ∈ U ∧ v ∈ U) → ¬ (u ∈ active ∧ v ∈ U) →
      ¬ (v ∈ active ∧ u ∈ U) → G.mult s(u,v) ≤ base.mult s(u,v))
    (hColour : Nonempty (base.EdgeColoring k)) :
    Nonempty (G.EdgeColoring k) := by
  classical
  by_contra hNo
  obtain ⟨N,hNG,hCritical⟩ := G.exists_copy_critical k hNo
  have hDegree (v : V) : N.degree v ≤ k :=
    (G.degree_le_of_mult_le N hNG v).trans (hDegrees v)
  have hLow (v : V) (hv : v ∈ U) : N.degree v ≤ a :=
    (G.degree_le_of_mult_le N hNG v).trans (hCore v hv)
  let X := U.filter (fun v => 0 < N.degree v)
  have hX : X ⊆ U := filter_subset _ _
  have hXlow (v : V) (hv : v ∈ X) : N.degree v ≤ a := hLow v (hX hv)
  have hOut (x : V) : N.degreeInto Xᶜ x ≤ G.degreeInto Uᶜ x := by
    have hSub : Uᶜ ⊆ Xᶜ := compl_subset_compl.mpr hX
    have hZero (v : V) (hv : v ∈ Xᶜ) (hn : v ∉ Uᶜ) : N.mult s(x,v) = 0 := by
      have hU : v ∈ U := by simpa only [mem_compl,not_not] using hn
      have hNot : v ∉ X := mem_compl.mp hv
      have hDegreeZero : N.degree v = 0 := by
        by_contra h
        exact hNot (mem_filter.mpr ⟨hU,Nat.pos_of_ne_zero h⟩)
      exact Nat.eq_zero_of_le_zero ((multiplicity_le_endpoint_degree N x v).trans_eq hDegreeZero)
    have hSum : (∑ v ∈ Uᶜ, N.mult s(x,v)) = ∑ v ∈ Xᶜ, N.mult s(x,v) := sum_subset hSub hZero
    unfold MultiGraph.degreeInto
    rw [← hSum]
    exact sum_le_sum fun v _ => hNG s(x,v)
  have hAcross (x : V) (hx : x ∈ active) (v : V) (hv : v ∈ U) : N.mult s(x,v) = 0 := by
    have hBudget (w : V) (hw : w ∈ X) : N.degreeInto Xᶜ x + N.mult s(x,w) ≤ k-a+1 := by
      have hG := G.degreeInto_add_compl U x
      have hLargeX := hActive x hx
      have hDeg := hDegrees x
      have hOutside := hOut x
      have hMultiplicity := (multiplicity_le_endpoint_degree N x w).trans (hXlow w hw)
      omega
    by_contra h
    have hPos : 0 < N.degree v := (Nat.pos_of_ne_zero h).trans_le (multiplicity_le_endpoint_degree N x v)
    exact h (copyCritical_no_low_degree_neighbour hCritical hDegree x X
      (fun hx' => disjoint_left.mp hDisj (hX hx') hx) hXlow (by omega) hBudget v
      (mem_filter.mpr ⟨hv,hPos⟩))
  have hInside (x v : V) (hx : x ∈ U) (hv : v ∈ U) : N.mult s(x,v) = 0 := by
    by_contra h
    have hh := copyCritical_endpoint_degree_sum hCritical hDegree x v (Nat.pos_of_ne_zero h)
    have hx' := hLow x hx
    have hv' := hLow v hv
    omega
  have hNB (e : Sym2 V) : N.mult e ≤ base.mult e := by
    induction e using Sym2.inductionOn with
    | hf x v =>
      by_cases hUV : x ∈ U ∧ v ∈ U
      · rw [hInside x v hUV.1 hUV.2]
        exact Nat.zero_le _
      by_cases hA : x ∈ active ∧ v ∈ U
      · rw [hAcross x hA.1 v hA.2]
        exact Nat.zero_le _
      by_cases hB : v ∈ active ∧ x ∈ U
      · rw [Sym2.eq_swap, hAcross v hB.1 x hB.2]
        exact Nat.zero_le _
      exact (hNG s(x,v)).trans (hBase x v hUV hA hB)
  obtain ⟨C⟩ := hColour
  exact hCritical.uncolourable (CanonicalColouringPullback.restrict_copies N base C hNB)


open MultiGraph.GeneralCopies

/-- The submultigraph induced by retaining a prescribed set of
indexed copies of the original residual multigraph. -/
noncomputable def paletteCopySubgraph (M : MultiGraph V) (S : Finset (Copies M)) :
    MultiGraph V where
  mult e := (S.filter (fun d => d.1 = e)).card
  loopless e he := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro d hd
    have h := (mem_filter.mp hd).2
    have hn := d.2.isLt
    have hZero : M.mult d.1 = 0 := (congrArg M.mult h).trans (M.loopless e he)
    exact (Nat.ne_of_gt (Nat.zero_lt_of_lt hn)) hZero

/-- Retaining indexed copies cannot increase any edge multiplicity. -/
theorem paletteCopySubgraph_mult_le (M : MultiGraph V) (S : Finset (Copies M)) (e : Sym2 V) :
    (paletteCopySubgraph M S).mult e ≤ M.mult e :=
  (card_le_card (filter_subset_filter _ (subset_univ S))).trans_eq (edge_fibre_card M e)

/-- The vertex degrees in the selected multigraph are exactly the
incidence counts used in the palette selection theorem. -/
theorem paletteCopySubgraph_degree (M : MultiGraph V) (S : Finset (Copies M)) (v : V) :
    (paletteCopySubgraph M S).degree v = paletteCopyDegree (ends M) S v := by
  unfold MultiGraph.degree paletteCopySubgraph paletteCopyDegree
  rw [sum_card_fiberwise_eq_card_filter S _ Sigma.fst]
  congr 1
  ext d
  have h := incident_iff M d v
  change ((ends M d).1 = v ∨ (ends M d).2 = v) ↔ v ∈ d.1 at h
  simp only [mem_filter,mem_univ,true_and,h]

omit [Fintype V] in
/-- All colors are incident at an exceptional vertex of saturated
degree. This property gives equality in the palette degree bound. -/
theorem paletteCopyDegree_filter_eq_palette_card {D K : Type*} [Fintype D] [DecidableEq K]
    (edgeEnds : D → V × V) (colour : D → K) (P : Finset K) (v : V)
    (hProper : Set.InjOn colour {d | (edgeEnds d).1 = v ∨ (edgeEnds d).2 = v})
    (hCovered : ∀ i ∈ P, ∃ d, ((edgeEnds d).1 = v ∨ (edgeEnds d).2 = v) ∧ colour d = i) :
    paletteCopyDegree edgeEnds (univ.filter (fun d => colour d ∈ P)) v = P.card := by
  let S := (univ.filter (fun d => colour d ∈ P)).filter
    (fun d => (edgeEnds d).1 = v ∨ (edgeEnds d).2 = v)
  have hImage : S.image colour = P := by
    ext i
    constructor
    · intro hi
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hi
      exact (mem_filter.mp (mem_filter.mp hd).1).2
    · intro hi
      obtain ⟨d,hd,hColour⟩ := hCovered i hi
      exact mem_image.mpr ⟨d,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hColour.symm ▸ hi⟩,hd⟩,hColour⟩
  have hS : paletteCopyDegree edgeEnds (univ.filter (fun d => colour d ∈ P)) v = S.card := by
    unfold paletteCopyDegree
    congr 1
    ext d
    simp only [S, mem_filter]
  rw [hS, ← hImage]
  exact (card_image_of_injOn
    (fun d hd e he h => hProper (mem_filter.mp hd).2 (mem_filter.mp he).2 h)).symm

noncomputable def paletteSelectedCopies {D W : Type*} (e : D → W × W)
    (role : W → PaletteVertexRole) (original core : Finset D) : Finset D :=
  paletteExceptionalCopies e role original ∪ core

/-- Transport the degree preservation and the core balance of a
selected palette to its actual submultigraph. -/
theorem paletteCopySubgraph_properties (M : MultiGraph V) (role : V → PaletteVertexRole)
    (A B block : Finset V) (original available core : Finset (Copies M))
    (hA : ∀ v, role v = .coreA ↔ v ∈ A) (hB : ∀ v, role v = .coreB ↔ v ∈ B)
    (hSel : IsPaletteBlockSelection (ends M) role block original available core) :
    let S := paletteSelectedCopies (ends M) role original core
    let N := paletteCopySubgraph M S
    (∀ v, (role v).isCore = false → N.degree v = (paletteCopySubgraph M original).degree v) ∧
      (∑ v ∈ A, N.degree v) = ∑ v ∈ B, N.degree v := by
  intro S N
  constructor
  · intro v hv
    change (paletteCopySubgraph M S).degree v = _
    rw [paletteCopySubgraph_degree,paletteCopySubgraph_degree]
    exact hSel.degree v hv
  have h := hSel.balanced
  change paletteCopyCoreGap (ends M) role S = 0 at h
  rw [paletteCopyCoreGap_eq_degree_sum _ _ _ (fun d _ => MultiGraph.GeneralCopies.loopless M d)] at h
  have hRole (v : V) : (role v).coreSign =
      (if v ∈ A then (1:ℤ) else 0) - (if v ∈ B then 1 else 0) := by
    cases hv : role v <;> simp [PaletteVertexRole.coreSign, ← hA v, ← hB v, hv]
  have hN (v : V) : paletteCopyDegree (ends M) S v = N.degree v :=
    (paletteCopySubgraph_degree M S v).symm
  have hDegree (v : V) : (S.filter (fun d => (ends M d).1 = v ∨ (ends M d).2 = v)).card =
      paletteCopyDegree (ends M) S v := by
    unfold paletteCopyDegree
    congr 1
    ext d
    simp only [mem_filter]
  simp_rw [hDegree] at h
  simp_rw [hN,hRole,sub_mul,sum_sub_distrib,ite_mul,one_mul,zero_mul,← sum_filter] at h
  have hFilter (T : Finset V) : univ.filter (fun v => v ∈ T) = T := by
    ext v
    simp
  rw [hFilter A,hFilter B,sub_eq_zero] at h
  exact_mod_cast h


/-- A subset of the original copies whose colors lie in one palette
inherits a proper coloring with exactly that palette's color type. -/
theorem paletteCopySubgraph_colourable_in_original_palette {K : Type*}
    (M : MultiGraph V) (S : Finset (Copies M)) (P : Finset K) (colour : Copies M → K)
    (hProper : ∀ v, Set.InjOn colour {d | v ∈ d.1})
    (hPalette : ∀ d ∈ S, colour d ∈ P) :
    Nonempty ((paletteCopySubgraph M S).EdgeColoring P.card) := by
  classical
  let E (d : ↥S) := ends M d.val
  let e : ↥P ≃ Fin P.card := Fintype.equivOfCardEq (by simp)
  let c (d : ↥S) := e ⟨colour d.val,hPalette d.val d.property⟩
  refine MultiGraph.GeneralCopies.colourable_of_labelled_family (paletteCopySubgraph M S) E P.card ?_ c ?_
  · intro p
    change (univ.filter (fun d : ↥S => s((E d).1,(E d).2) = p)).card =
      (S.filter (fun d => d.1 = p)).card
    apply card_bij (fun d _ => d.val)
    · intro d hd
      refine mem_filter.mpr ⟨d.property,?_⟩
      exact (endpoints_eq d.val.1).symm.trans (mem_filter.mp hd).2
    · intro d _ f _ h
      exact Subtype.ext h
    · intro d hd
      obtain ⟨hS,hP⟩ := mem_filter.mp hd
      exact ⟨⟨d,hS⟩,mem_filter.mpr ⟨mem_univ _,(endpoints_eq d.1).trans hP⟩,rfl⟩
  · intro d f hdf hInc hEq
    obtain ⟨v,hd,hf⟩ := hInc
    have hColour := congrArg Subtype.val (e.injective hEq)
    have h := hProper v ((incident_iff M d.val v).mp hd)
      ((incident_iff M f.val v).mp hf) hColour
    exact hdf (Subtype.ext h)


/-- Apply the coloring argument directly to a set of residual edge
copies. The exceptional edges outside the scope of Lemma 3.5 retain
colors in the designated palette in the original coloring. -/
theorem paletteCopySubgraph_colourable_of_retained_colors {K : Type*}
    (M : MultiGraph V) (S : Finset (Copies M)) (P : Finset K) (colour : Copies M → K)
    (U active : Finset V) (a : ℕ)
    (hDisj : Disjoint U active) (hLarge : 2*a < P.card)
    (hDegrees : ∀ v, (paletteCopySubgraph M S).degree v ≤ P.card)
    (hCore : ∀ v ∈ U, (paletteCopySubgraph M S).degree v ≤ a)
    (hActive : ∀ v ∈ active, 2*a < (paletteCopySubgraph M S).degreeInto U v)
    (hProper : ∀ v, Set.InjOn colour {d | v ∈ d.1})
    (hRetained : ∀ d ∈ S,
      ¬ ((ends M d).1 ∈ U ∧ (ends M d).2 ∈ U) →
      ¬ ((ends M d).1 ∈ active ∧ (ends M d).2 ∈ U) →
      ¬ ((ends M d).2 ∈ active ∧ (ends M d).1 ∈ U) →
      colour d ∈ P) :
    Nonempty ((paletteCopySubgraph M S).EdgeColoring P.card) := by
  classical
  let T := S.filter (fun d => colour d ∈ P)
  refine palette_subgraph_colourable_of_active_degrees (paletteCopySubgraph M S)
    (paletteCopySubgraph M T) U active P.card a hDisj hLarge hDegrees hCore hActive ?_
    (paletteCopySubgraph_colourable_in_original_palette M T P colour hProper
      (fun _ h => (mem_filter.mp h).2))
  intro x y hXY hX hY
  unfold paletteCopySubgraph
  apply card_le_card
  intro d hd
  obtain ⟨hs,he⟩ := mem_filter.mp hd
  have hab : s((ends M d).1,(ends M d).2) = s(x,y) := (endpoints_eq d.1).trans he
  have hC : colour d ∈ P := by
    rcases Sym2.eq_iff.mp hab with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact hRetained d hs (by simpa only [h₁,h₂] using hXY)
        (by simpa only [h₁,h₂] using hX) (by simpa only [h₁,h₂] using hY)
    · exact hRetained d hs (by simpa only [h₁,h₂,and_comm] using hXY)
        (by simpa only [h₁,h₂] using hY) (by simpa only [h₁,h₂] using hX)
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hs,hC⟩,he⟩

end OverfullWork.ChenShan
