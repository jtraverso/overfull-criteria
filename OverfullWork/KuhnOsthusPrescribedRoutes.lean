module

public import OverfullWork.KuhnOsthusTileBudgets
public import OverfullWork.MergeReserveReindex

@[expose] public section


/-! Kühn–Osthus Corollary 4.15, the four-cluster case. Identify the
prescribed first and last vertices and use a tripartite triangle
factor on the three resulting parts. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Swap two disjoint parts by the specified bijection, keeping every
vertex in their complement fixed. -/
private noncomputable def swapParts {A B : Finset V} (f : A ≃ B) (hd : Disjoint A B) : Equiv.Perm V := by
  let e (x : V) := if ha : x ∈ A then (f ⟨x,ha⟩).val
    else if hb : x ∈ B then (f.symm ⟨x,hb⟩).val else x
  have he (x : V) : e (e x) = x := by
    by_cases ha : x ∈ A
    · have hb' : (f ⟨x,ha⟩).val ∈ B := (f ⟨x,ha⟩).prop
      have ha' : (f ⟨x,ha⟩).val ∉ A := fun h => disjoint_left.mp hd h hb'
      simp only [e,dif_pos ha,dif_neg ha',dif_pos hb']
      exact congrArg Subtype.val (f.symm_apply_apply ⟨x,ha⟩)
    · by_cases hb : x ∈ B
      · have ha' : (f.symm ⟨x,hb⟩).val ∈ A := (f.symm ⟨x,hb⟩).prop
        simp only [e,dif_neg ha,dif_pos hb,dif_pos ha']
        exact congrArg Subtype.val (f.apply_symm_apply ⟨x,hb⟩)
      · simp [e,ha,hb]
  exact ⟨e,e,he,he⟩

omit [Fintype V] in
private theorem swapParts_apply {A B : Finset V} (f : A ≃ B) (hd : Disjoint A B) (a : A) :
    swapParts f hd a.val = (f a).val := by
  simp only [swapParts,Equiv.coe_fn_mk,dif_pos a.prop]

omit [Fintype V] in
private theorem swapParts_image {A B : Finset V} (f : A ≃ B) (hd : Disjoint A B) :
    A.image (swapParts f hd) = B := by
  ext y
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    rw [show swapParts f hd a = (f ⟨a,ha⟩).val from swapParts_apply f hd ⟨a,ha⟩]
    exact (f ⟨a,ha⟩).prop
  · intro hy
    let x : A := f.symm ⟨y,hy⟩
    exact mem_image.mpr ⟨x.val,x.prop,(swapParts_apply f hd x).trans
      (congrArg Subtype.val (f.apply_symm_apply ⟨y,hy⟩))⟩

omit [Fintype V] in
private noncomputable def slotEquiv {p m : ℕ} {X : Fin p → Finset V}
    {E : Fin p → Fin p → Bool} {R : Fin p → Fin p → Digraph V}
    (P : LayeredTilePacking X E R m) (a : Fin p) (hSize : (X a).card = m) : Fin m ≃ X a :=
  Equiv.ofBijective (fun i => ⟨P.vertices (i,a),P.mem i a⟩) ⟨fun i j h =>
    congrArg (fun z : Fin m × Fin p => z.1) (P.vertices.injective (congrArg Subtype.val h)),
    fun v => by obtain ⟨i,hi⟩ := P.covers_part a hSize v.val v.prop; exact ⟨i,Subtype.ext hi⟩⟩

/-- There are m disjoint paths of length three matching the given
endpoints on the first and fourth clusters. The bijections to the
two middle clusters witness disjointness and complete coverage. -/
theorem kuhn_osthus_corollary_4_15_four_clusters (G : Digraph V)
    (A B C T : Finset V) (m r : ℕ) (ε d : ℝ) (f : A ≃ T)
    (hA : A.card = m) (hB : B.card = m) (hC : C.card = m) (hT : T.card = m)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAT : Disjoint A T) (hBC : Disjoint B C)
    (h₀ : IsLowerSuperregularPair G ε d A B)
    (h₁ : IsLowerSuperregularPair G ε d B C)
    (h₂ : IsLowerSuperregularPair G ε d C T)
    (hε : 0 ≤ ε) (hGap : 2*ε < d) (hd : d ≤ 1) (hr : 0 < r)
    (hCut : (m:ℝ)*ε ≤ (r:ℝ))
    (hBudget : 28*((r:ℝ)+1) < (d-2*ε)^14*((d-ε)*(m:ℝ))) :
    ∃ p : A ≃ B, ∃ q : A ≃ C, ∀ a : A,
      G.Adj a (p a) ∧ G.Adj (p a) (q a) ∧ G.Adj (q a) (f a) := by
  let e := swapParts f hAT
  let H := reindexSources (reverseArcs G) e
  let X : Fin 3 → Finset V := ![A,B,C]
  let R (a b : Fin 3) : Digraph V := if a = 0 ∧ b = 2 then H else G
  have hSize (a : Fin 3) : (X a).card = m := by fin_cases a <;> assumption
  have hDis (a b : Fin 3) (hne : a ≠ b) : Disjoint (X a) (X b) := by
    fin_cases a <;> fin_cases b <;> first
      | exact (hne rfl).elim
      | exact hAB
      | exact hAC
      | exact hBC
      | exact hAB.symm
      | exact hAC.symm
      | exact hBC.symm
  obtain ⟨hRect₀,hOut₀,hIn₀⟩ := h₀.tile_bounds G A B d ε m r hA hB hCut
  obtain ⟨hRect₁,hOut₁,hIn₁⟩ := h₁.tile_bounds G B C d ε m r hB hC hCut
  obtain ⟨hRect₂,hOut₂,hIn₂⟩ := h₂.tile_bounds G C T d ε m r hC hT hCut
  have hImg : A.image e = T := swapParts_image f hAT
  have hRectH : TileRectangleBound H A C r (d-2*ε) := by
    intro S hS U hU hs hu
    have hImg' : S.image e ⊆ T := hImg ▸ image_subset_image hS
    have hD := hRect₂.reverse (S.image e) hImg' U hU
      (by rwa [card_image_of_injective _ e.injective]) hu
    simpa only [H,reindexSources_incidences,card_image_of_injective _ e.injective] using hD
  have hOutH (v : V) (hv : v ∈ A) : (d-ε)*(m:ℝ) ≤ (outTo H C v:ℝ) := by
    have hvT : e v ∈ T := hImg ▸ mem_image_of_mem e hv
    exact hIn₂ (e v) hvT
  have hInH (v : V) (hv : v ∈ C) : (d-ε)*(m:ℝ) ≤ (inNeighbours H A v:ℝ) := by
    have he : inNeighbours H A v = outTo G T v := by
      have hI := reindexSources_incidences (reverseArcs G) e A {v}
      rw [hImg] at hI
      have he' : inNeighbours (reverseArcs G) T v = outTo G T v := by
        unfold inNeighbours outTo
        apply congrArg Finset.card
        ext x
        simp only [mem_filter]
        rfl
      simpa only [H,incidences,sum_singleton,he'] using hI
    rw [he]
    exact hOut₂ v hv
  have hRects (a b : Fin 3) (hab : a < b) : TileRectangleBound (R a b) (X a) (X b) r (d-2*ε) := by
    fin_cases a <;> fin_cases b <;> first
      | exact (by decide : ¬ (_ < _ : Prop)) hab |>.elim
      | exact hRect₀
      | exact hRect₁
      | exact hRectH
  have hOut (a b : Fin 3) (hab : a < b) : ∀ v ∈ X a, (d-ε)*(m:ℝ) ≤ (outTo (R a b) (X b) v:ℝ) := by
    fin_cases a <;> fin_cases b <;> first
      | exact hOut₀
      | exact hOut₁
      | exact hOutH
      | exact (not_lt_of_ge (by decide) hab).elim
  have hIn (a b : Fin 3) (hab : a < b) : ∀ v ∈ X b, (d-ε)*(m:ℝ) ≤ (inNeighbours (R a b) (X a) v:ℝ) := by
    fin_cases a <;> fin_cases b <;> first
      | exact hIn₀
      | exact hIn₁
      | exact hInH
      | exact (not_lt_of_ge (by decide) hab).elim
  have hη : 0 ≤ d-2*ε := by linarith
  have hη₁ : d-2*ε ≤ 1 := by linarith
  have hδ : 0 ≤ d-ε := by linarith
  obtain ⟨hs,hSeed,hAdd,hRepair⟩ := geometric_tile_budgets m r 3 6 (d-2*ε) (d-ε)
    (by decide) (by decide) hη hη₁ hδ hBudget
  obtain ⟨P⟩ := exists_superregular_triangle_tile_factor X R r (d-2*ε) (d-ε) _
    hr hη hη₁ (by linarith) hs hSeed hAdd hRepair hSize hDis hRects hOut hIn
  let aMap : Fin m ≃ A := slotEquiv P 0 hA
  let bMap : Fin m ≃ B := slotEquiv P 1 hB
  let cMap : Fin m ≃ C := slotEquiv P 2 hC
  refine ⟨aMap.symm.trans bMap,aMap.symm.trans cMap,?_⟩
  rintro a
  obtain ⟨i,rfl⟩ := aMap.surjective a
  simp only [Equiv.trans_apply,aMap.symm_apply_apply]
  refine ⟨P.edge i 0 1 (by decide),P.edge i 1 2 (by decide),?_⟩
  have h := P.edge i 0 2 (by decide)
  change G.Adj (cMap i).val (e (aMap i).val) at h
  rw [show e (aMap i).val = (f (aMap i)).val from swapParts_apply f hAT (aMap i)] at h
  exact h

end OverfullWork.DirectedRobustExpansion
