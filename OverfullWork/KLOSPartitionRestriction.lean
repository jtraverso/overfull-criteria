module

public import OverfullWork.KLOSCutSeparation

@[expose] public section

/-! Transporting the robust component conditions to an induced copy. -/

namespace OverfullWork.KLOS

open Finset SimpleGraph PrunedCore RobustExpansion OddCutDeficit
open scoped Classical

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
variable (e : V ↪ W) (hAdj : ∀ v w, H.Adj (e v) (e w) ↔ G.Adj v w)

include hAdj in
theorem neighboursIn_map_induced (U : Finset V) (v : V) :
    neighboursIn H (U.map e) (e v) = neighboursIn G U v := by
  simp only [neighboursIn_eq_filter_card, filter_map, card_map, Function.comp_apply, hAdj]

include hAdj in
theorem robustNeighbourhoodIn_map_induced (ν : ℝ) (U S : Finset V) :
    robustNeighbourhoodIn H ν (U.map e) (S.map e) =
      (robustNeighbourhoodIn G ν U S).map e := by
  simp only [robustNeighbourhoodIn, filter_map, card_map, Function.comp_apply, neighboursIn_map_induced G H e hAdj]

include hAdj in
theorem expandsInside_of_induced_map (ν τ : ℝ) (U : Finset V)
    (h : ExpandsInside H ν τ (U.map e)) : ExpandsInside G ν τ U := by
  intro S hS hLo hHi
  have h' := h (S.map e) (map_subset_map.mpr hS) (by simpa only [card_map] using hLo)
    (by simpa only [card_map] using hHi)
  simpa only [card_map, robustNeighbourhoodIn_map_induced G H e hAdj] using h'

include hAdj in
theorem expandsAcross_of_induced_map (ν τ : ℝ) (A B : Finset V)
    (h : ExpandsAcross H ν τ (A.map e) (B.map e)) : ExpandsAcross G ν τ A B := by
  intro S hS hLo hHi
  have h' := h (S.map e) (map_subset_map.mpr hS) (by simpa only [card_map] using hLo)
    (by simpa only [card_map] using hHi)
  simpa only [← map_union, robustNeighbourhoodIn_map_induced G H e hAdj,
    ← map_inter, card_map] using h'

include hAdj in
theorem incidences_map_induced (U T : Finset V) :
    incidences H (U.map e) (T.map e) = incidences G U T := by
  simp only [incidences, sum_map, neighboursIn_map_induced G H e hAdj]

include hAdj in
theorem internalEdges_map_induced (U : Finset V) :
    internalEdges H (U.map e) = internalEdges G U := by
  have h := incidences_map_induced G H e hAdj U U
  rw [incidences_self, incidences_self] at h
  omega

include hAdj in
theorem cutEdges_le_map_induced (U : Finset V) :
    cutEdges G U ≤ cutEdges H (U.map e) := by
  have hSub : (Uᶜ : Finset V).map e ⊆ (U.map e)ᶜ := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
    apply mem_compl.mpr
    intro hz
    obtain ⟨z, hz, he⟩ := mem_map.mp hz
    exact (mem_compl.mp hw) (e.injective he ▸ hz)
  rw [← incidences_compl_self, ← incidences_compl_self, ← incidences_map_induced G H e hAdj]
  exact incidences_mono H Subset.rfl hSub

private theorem sqrt_four_mul (ρ : ℝ) :
    Real.sqrt (4 * ρ) = 2 * Real.sqrt ρ := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show Real.sqrt 4 = 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]

include hAdj in
/-- The change from ambient order `2n` to `n` is paid for by replacing
the boundary parameter by `4ρ`. -/
theorem sparseComponent_of_induced_copy (ρ : ℝ) (U : Finset V)
    (hn : Fintype.card W = 2 * Fintype.card V)
    (h : IsSparseComponent H ρ (U.map e)) :
    IsSparseComponent G (4 * ρ) U := by
  have hnR : (Fintype.card W : ℝ) = 2 * (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hCard := h.1
  rw [hnR, card_map] at hCard
  have hCut : (cutEdges G U : ℝ) ≤ cutEdges H (U.map e) := by
    exact_mod_cast cutEdges_le_map_induced G H e hAdj U
  refine ⟨?_, hCut.trans ?_⟩
  · rw [sqrt_four_mul]
    linarith only [hCard]
  · have hh := h.2
    rw [hnR] at hh
    nlinarith only [hh]

include hAdj in
theorem closeToBipartite_of_induced_copy (ρ : ℝ) (hρ : 0 ≤ ρ) (A B : Finset V)
    (hn : Fintype.card W = 2 * Fintype.card V)
    (h : CloseToBipartite H ρ (A.map e) (B.map e)) :
    CloseToBipartite G (4 * ρ) A B := by
  have hnR : (Fintype.card W : ℝ) = 2 * (Fintype.card V : ℝ) := by exact_mod_cast hn
  obtain ⟨hDis, hA, hB, hBal, hCut⟩ := h
  rw [hnR, card_map] at hA hB
  rw [hnR, card_map, card_map] at hBal
  rw [hnR, ← map_union, internalEdges_map_induced G H e hAdj,
    internalEdges_map_induced G H e hAdj] at hCut
  have hNonneg : 0 ≤ ρ * (Fintype.card V : ℝ) := by positivity
  have hCutMono : (cutEdges G (A ∪ B) : ℝ) ≤ cutEdges H ((A ∪ B).map e) := by
    exact_mod_cast cutEdges_le_map_induced G H e hAdj (A ∪ B)
  refine ⟨(disjoint_map e).mp hDis, ?_, ?_, ?_, ?_⟩
  · rw [sqrt_four_mul]
    linarith only [hA]
  · rw [sqrt_four_mul]
    linarith only [hB]
  · linarith only [hBal, hNonneg]
  · nlinarith only [hCut, hCutMono]

include hAdj in
/-- Restrict a collection of whole parts to an induced copy of half the
ambient order. The component count for the selected side is the only
condition that must be supplied separately. -/
theorem robustPartition_of_induced_copy {D D' : ℕ} {ρ ν τ : ℝ}
    (P : RobustPartition H D' ρ ν τ) (J : Finset ↥P.labels)
    (hCover : ∀ v, P.assign (e v) ∈ J)
    (hRange : ∀ i ∈ J, ∀ w ∈ assignmentPart P.assign i, w ∈ Set.range e)
    (hn : Fintype.card W = 2 * Fintype.card V) (hρ : 0 ≤ ρ) (hDegree : D ≤ D')
    (hCount : ((J.card : ℝ) + ((J ∩ P.bipartite).card : ℝ)) * D ≤
      (1 + (4 * ρ) ^ ((1 : ℝ) / 3)) * (Fintype.card V : ℝ)) :
    Nonempty (RobustPartition G D (4 * ρ) ν τ) := by
  let pull (S : Finset W) : Finset V := univ.filter (fun v => e v ∈ S)
  have hMem (S : Finset W) (v : V) : v ∈ pull S ↔ e v ∈ S := by simp [pull]
  have hMap (S : Finset W) (hS : ∀ w ∈ S, w ∈ Set.range e) : (pull S).map e = S := by
    ext w
    constructor
    · intro hw
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
      exact (hMem S v).mp hv
    · intro hw
      obtain ⟨v, rfl⟩ := hS w hw
      exact mem_map.mpr ⟨v, (hMem S v).mpr hw, rfl⟩
  let U := assignmentPart P.assign
  let label (i : ↥P.labels) := pull (U i)
  let newLabels := J.image label
  have hLabelMap (i : ↥P.labels) (hi : i ∈ J) : (label i).map e = U i :=
    hMap (U i) (hRange i hi)
  have hInject : Set.InjOn label J := by
    intro i hi j hj hij
    have hEq : U i = U j := by
      rw [← hLabelMap i hi, ← hLabelMap j hj, hij]
    by_contra hne
    obtain ⟨w, hw⟩ := P.nonempty_part i
    have hwj : w ∈ U j := hEq ▸ hw
    exact Finset.disjoint_left.mp (P.disjoint_parts H hne) hw hwj
  let newLabel (i : ↥P.labels) (hi : i ∈ J) : ↥newLabels :=
    ⟨label i, mem_image.mpr ⟨i, hi, rfl⟩⟩
  let f (v : V) : ↥newLabels := newLabel (P.assign (e v)) (hCover v)
  have hFiber (i : ↥P.labels) (hi : i ∈ J) :
      assignmentPart f (newLabel i hi) = label i := by
    ext v
    change _ ↔ v ∈ pull (U i)
    rw [hMem]
    simp only [assignmentPart, mem_filter, mem_univ, true_and, U]
    constructor
    · intro hv
      exact hInject (hCover v) hi (congrArg Subtype.val hv)
    · intro hv
      exact Subtype.ext (congrArg label hv)
  have hSurj (j : ↥newLabels) : ∃ (i : ↥P.labels) (hi : i ∈ J), newLabel i hi = j := by
    obtain ⟨i, hi, hEq⟩ := mem_image.mp j.property
    exact ⟨i, hi, Subtype.ext hEq⟩
  let bipEmbed : ↥(J ∩ P.bipartite) ↪ ↥newLabels :=
    ⟨fun i => newLabel i.val (mem_inter.mp i.property).1, by
      intro i j hij
      apply Subtype.ext
      exact hInject (mem_inter.mp i.property).1 (mem_inter.mp j.property).1 (congrArg Subtype.val hij)⟩
  let newBip := (J ∩ P.bipartite).attach.map bipEmbed
  have hBip (i : ↥P.labels) (hi : i ∈ J) : newLabel i hi ∈ newBip ↔ i ∈ P.bipartite := by
    constructor
    · intro h
      obtain ⟨j, _, hEq⟩ := mem_map.mp h
      have hj : j.val = i := hInject (mem_inter.mp j.property).1 hi (congrArg Subtype.val hEq)
      exact hj ▸ (mem_inter.mp j.property).2
    · intro h
      exact mem_map.mpr ⟨⟨i, mem_inter.mpr ⟨hi, h⟩⟩, by simp, rfl⟩
  have hDeg (i : ↥P.labels) (hi : i ∈ J) (v : V) :
      neighboursIn G (assignmentPart f (newLabel i hi)) v = neighboursIn H (U i) (e v) := by
    rw [hFiber i hi, ← hLabelMap i hi, neighboursIn_map_induced G H e hAdj]
  have hnR : (Fintype.card W : ℝ) = 2 * (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hNonneg : 0 ≤ ρ * (Fintype.card V : ℝ) := by positivity
  refine ⟨⟨newLabels, f, newBip, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j
    obtain ⟨i, hi, rfl⟩ := hSurj j
    rw [hFiber i hi]
    obtain ⟨w, hw⟩ := P.nonempty_part i
    obtain ⟨v, rfl⟩ := hRange i hi w hw
    exact ⟨v, (hMem (U i) v).mpr hw⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := hSurj j
    have h := P.ordinary i (fun hb => hj ((hBip i hi).mpr hb))
    rw [hFiber i hi]
    exact ⟨sparseComponent_of_induced_copy G H e hAdj ρ (label i) hn
      (by rw [hLabelMap i hi]; exact h.1),
      expandsInside_of_induced_map G H e hAdj ν τ (label i) (by rw [hLabelMap i hi]; exact h.2)⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := hSurj j
    obtain ⟨A, B, hAB, hClose, hExpand, hA, hB⟩ := P.bipartite_component i ((hBip i hi).mp hj)
    have hAmap : (pull A).map e = A := hMap A
      (fun w hw => hRange i hi w (hAB ▸ mem_union_left _ hw))
    have hBmap : (pull B).map e = B := hMap B
      (fun w hw => hRange i hi w (hAB ▸ mem_union_right _ hw))
    have hSide (S : Finset W) (hS : (pull S).map e = S) (v : V) :
        neighboursIn H S (e v) = neighboursIn G (pull S) v := by
      exact (congrArg (fun T => neighboursIn H T (e v)) hS.symm).trans
        (neighboursIn_map_induced G H e hAdj (pull S) v)
    refine ⟨pull A, pull B, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hFiber i hi]
      ext v
      simp only [mem_union, hMem, label]
      change e v ∈ A ∨ e v ∈ B ↔ e v ∈ assignmentPart P.assign i
      rw [← hAB, mem_union]
    · exact closeToBipartite_of_induced_copy G H e hAdj ρ hρ (pull A) (pull B) hn
        (by rwa [hAmap, hBmap])
    · exact expandsAcross_of_induced_map G H e hAdj ν τ (pull A) (pull B)
        (by rwa [hAmap, hBmap])
    · intro v hv
      rw [← hSide A hAmap v, ← hSide B hBmap v]
      exact hA (e v) ((hMem A v).mp hv)
    · intro v hv
      rw [← hSide A hAmap v, ← hSide B hBmap v]
      exact hB (e v) ((hMem B v).mp hv)
  · intro v j
    obtain ⟨i, hi, rfl⟩ := hSurj j
    change neighboursIn G (assignmentPart f (newLabel i hi)) v ≤
      neighboursIn G (assignmentPart f (newLabel (P.assign (e v)) (hCover v))) v
    rw [hDeg i hi, hDeg (P.assign (e v)) (hCover v)]
    exact P.dominance (e v) i
  · have hL : newLabels.card = J.card := card_image_of_injOn hInject
    have hB : newBip.card = (J ∩ P.bipartite).card := by simp [newBip]
    rw [hL, hB]
    exact hCount
  · intro j
    obtain ⟨i, hi, rfl⟩ := hSurj j
    dsimp only
    let S := (assignmentPart f (newLabel i hi)).filter (fun v =>
      (neighboursIn G (assignmentPart f (newLabel i hi)) v : ℝ) <
        (D : ℝ) - 4 * ρ * (Fintype.card V : ℝ))
    let T := (U i).filter (fun w => (neighboursIn H (U i) w : ℝ) <
      (D' : ℝ) - ρ * (Fintype.card W : ℝ))
    have hSub : S.map e ⊆ T := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := mem_map.mp hw
      obtain ⟨hvPart, hvDeg⟩ := mem_filter.mp hv
      have hvU : e v ∈ U i := by
        rw [hFiber i hi] at hvPart
        exact (hMem (U i) v).mp hvPart
      have hD : (D : ℝ) ≤ D' := by exact_mod_cast hDegree
      rw [hDeg i hi] at hvDeg
      refine mem_filter.mpr ⟨hvU, ?_⟩
      rw [hnR]
      linarith only [hvDeg, hD, hNonneg]
    have hCard := card_le_card hSub
    rw [card_map] at hCard
    have hCardR : (S.card : ℝ) ≤ T.card := by exact_mod_cast hCard
    have hCore := P.core i
    change (T.card : ℝ) ≤ ρ * (Fintype.card W : ℝ) at hCore
    rw [hnR] at hCore
    change (S.card : ℝ) ≤ _
    linarith only [hCardR, hCore, hNonneg]

end OverfullWork.KLOS
