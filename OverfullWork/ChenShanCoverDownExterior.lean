module

public import OverfullWork.ChenShanCoverDownTransport
import OverfullWork.ChenShanAbsorberCatalogue
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

def touches {V : Type*} (v : V) (e : V × V) : Prop :=
  e.1 = v ∨ e.2 = v

def shareEndpoint {V : Type*} (e f : V × V) : Prop :=
  touches e.1 f ∨ touches e.2 f

private theorem shareEndpoint_symm {V : Type*} {e f : V × V} (h : shareEndpoint e f) :
    shareEndpoint f e := by
  unfold shareEndpoint touches at *
  rcases h with (h | h) | (h | h)
  · exact Or.inl (Or.inl h.symm)
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inl (Or.inr h.symm)
  · exact Or.inr (Or.inr h.symm)

private theorem shareEndpoint_card {V : Type*} (D : Finset (V × V)) (e : V × V) :
    (D.filter (shareEndpoint e)).card ≤ incidentDegree D e.1 + incidentDegree D e.2 := by
  have hEq : D.filter (shareEndpoint e) =
      (D.filter (touches e.1)) ∪ D.filter (touches e.2) := by
    ext x
    simp only [mem_filter,mem_union,shareEndpoint]
    tauto
  have h := card_union_le (D.filter (touches e.1)) (D.filter (touches e.2))
  rw [hEq]
  unfold incidentDegree
  convert h using 1
  congr 4

/-- Greedily give each arc a label from its own list. Used labels at
either endpoint account for at most the sum of the two arc degrees. -/
theorem exists_exterior_arc_labels {V : Type*} (D : Finset (V × V))
    (C : (V × V) → Finset V)
    (hBudget : ∀ e ∈ D, incidentDegree D e.1 + incidentDegree D e.2 < (C e).card) :
    ∃ label : (V × V) → V,
      (∀ e ∈ D, label e ∈ C e) ∧
      ∀ e ∈ D, ∀ f ∈ D, e ≠ f → shareEndpoint e f → label e ≠ label f := by
  induction D using Finset.induction_on with
  | empty =>
    exact ⟨Prod.fst,by simp⟩
  | @insert a D ha ih =>
    have hSub : D ⊆ insert a D := subset_insert _ _
    have hBudget' (e) (he : e ∈ D) : incidentDegree D e.1 + incidentDegree D e.2 < (C e).card :=
      (Nat.add_le_add (incidentDegree_mono hSub _) (incidentDegree_mono hSub _)).trans_lt
        (hBudget e (hSub he))
    obtain ⟨old,hOld,hDist⟩ := ih hBudget'
    let bad := (D.filter (shareEndpoint a)).image old
    have hBad : bad.card < (C a).card :=
      card_image_le.trans_lt ((shareEndpoint_card D a).trans_lt
        ((Nat.add_le_add (incidentDegree_mono hSub _) (incidentDegree_mono hSub _)).trans_lt
          (hBudget a (mem_insert_self _ _))))
    obtain ⟨z,hz,hFresh⟩ := exists_mem_notMem_of_card_lt_card hBad
    let label (e : V × V) := if e = a then z else old e
    have hNew (f) (hf : f ∈ D) (hs : shareEndpoint a f) : z ≠ old f := by
      intro heq
      exact hFresh (mem_image.mpr ⟨f,mem_filter.mpr ⟨hf,hs⟩,heq.symm⟩)
    refine ⟨label,?_,?_⟩
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · simpa [label] using hz
      · have hne : e ≠ a := fun heq => ha (heq ▸ he)
        simpa [label,hne] using hOld e he
    · intro e he f hf hne hs
      rcases mem_insert.mp he with rfl | heD
      · have hf' : f ∈ D := (mem_insert.mp hf).resolve_left hne.symm
        simpa [label,hne.symm] using hNew f hf' hs
      · have he' : e ≠ a := fun heq => ha (heq ▸ heD)
        rcases mem_insert.mp hf with rfl | hf
        · simpa [label,he'] using (hNew e heD (shareEndpoint_symm hs)).symm
        · have hf' : f ≠ a := fun heq => ha (heq ▸ hf)
          simpa [label,he',hf'] using hDist e heD f hf hne hs

noncomputable def exteriorReserveArcs {V : Type*} (e : V × V) (z : V) : Finset (V × V) :=
  {(e.2,z),(z,e.1)}

noncomputable def exteriorTriangle {V : Type*} (e : V × V) (z : V) : Finset (V × V) :=
  insert e (exteriorReserveArcs e z)

noncomputable def usedExteriorReserve {V : Type*} (D : Finset (V × V))
    (label : (V × V) → V) : Finset (V × V) :=
  D.biUnion (fun e => exteriorReserveArcs e (label e))

theorem exteriorTriangle_cover_eq {V : Type*} (D : Finset (V × V)) (label : (V × V) → V) :
    coveredEdges (D.image (fun e => exteriorTriangle e (label e))) =
      D ∪ usedExteriorReserve D label := by
  ext x
  simp only [mem_coveredEdges,mem_image,exists_exists_and_eq_and,mem_union,
    usedExteriorReserve,mem_biUnion,exteriorTriangle,mem_insert]
  constructor
  · rintro ⟨e,he,rfl | hx⟩
    · exact Or.inl he
    · exact Or.inr ⟨e,he,hx⟩
  · rintro (hx | ⟨e,he,hx⟩)
    · exact ⟨x,hx,Or.inl rfl⟩
    · exact ⟨e,he,Or.inr hx⟩

theorem exteriorReserveArcs_disjoint {V : Type*} (U : Finset V) {e f : V × V} {z w : V}
    (he : e.1 ∉ U ∧ e.2 ∉ U) (hf : f.1 ∉ U ∧ f.2 ∉ U)
    (hz : z ∈ U) (hw : w ∈ U)
    (hdist : shareEndpoint e f → z ≠ w) :
    Disjoint (exteriorReserveArcs e z) (exteriorReserveArcs f w) := by
  apply disjoint_left.mpr
  intro x h₁ h₂
  simp only [exteriorReserveArcs,mem_insert,mem_singleton] at h₁ h₂
  rcases h₁ with rfl | rfl <;> rcases h₂ with h | h
  · exact hdist (Or.inr (Or.inr (congrArg Prod.fst h).symm)) (congrArg Prod.snd h)
  · have hEq : e.2 = w := congrArg Prod.fst h
    exact he.2 (hEq.symm ▸ hw)
  · have hEq : z = f.2 := congrArg Prod.fst h
    exact hf.2 (hEq ▸ hz)
  · exact hdist (Or.inl (Or.inl (congrArg Prod.snd h).symm)) (congrArg Prod.fst h)

/-- Cover all exterior edges using two crossing reserve arcs per edge. -/
theorem exists_exterior_triangle_cover {V : Type*} (U : Finset V)
    (D R : Finset (V × V)) (C : (V × V) → Finset V)
    (hOuter : ∀ e ∈ D, e.1 ∉ U ∧ e.2 ∉ U)
    (hDisj : Disjoint D R)
    (hCandidates : ∀ e ∈ D, ∀ z ∈ C e, z ∈ U ∧ (e.2,z) ∈ R ∧ (z,e.1) ∈ R)
    (hBudget : ∀ e ∈ D, incidentDegree D e.1 + incidentDegree D e.2 < (C e).card) :
    ∃ label : (V × V) → V,
      (∀ e ∈ D, label e ∈ C e) ∧
      usedExteriorReserve D label ⊆ R ∧
      (∀ e ∈ D, ∀ f ∈ D, e ≠ f →
        Disjoint (exteriorTriangle e (label e)) (exteriorTriangle f (label f))) := by
  obtain ⟨label,hLabel,hDistinct⟩ := exists_exterior_arc_labels D C hBudget
  have hCand (e) (he : e ∈ D) := hCandidates e he (label e) (hLabel e he)
  have hRes (e) (he : e ∈ D) : exteriorReserveArcs e (label e) ⊆ R := by
    intro x hx
    simp only [exteriorReserveArcs,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (hCand e he).2.1
    · exact (hCand e he).2.2
  refine ⟨label,hLabel,?_,?_⟩
  · intro x hx
    obtain ⟨e,he,hx⟩ := mem_biUnion.mp hx
    exact hRes e he hx
  · intro e he f hf hne
    have hContact := exteriorReserveArcs_disjoint U (hOuter e he) (hOuter f hf)
      (hCand e he).1 (hCand f hf).1 (hDistinct e he f hf hne)
    apply disjoint_left.mpr
    intro x hx hx'
    rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hx' with h | h
    · exact hne h
    · exact disjoint_left.mp hDisj he (hRes f hf h)
    · exact disjoint_left.mp hDisj (h ▸ hf) (hRes e he hx)
    · exact disjoint_left.mp hContact hx h

/-- Each exterior edge consumes at most one reserve edge at a given
exterior vertex. -/
theorem usedExteriorReserve_degree {V : Type*} (U : Finset V)
    (D : Finset (V × V)) (label : (V × V) → V)
    (hLabel : ∀ e ∈ D, label e ∈ U) (hLoop : ∀ e ∈ D, e.1 ≠ e.2)
    (v : V) (hv : v ∉ U) :
    incidentDegree (usedExteriorReserve D label) v ≤ incidentDegree D v := by
  have hFilter : (usedExteriorReserve D label).filter (touches v) =
      D.biUnion (fun e => (exteriorReserveArcs e (label e)).filter (touches v)) := by
    ext x
    simp only [usedExteriorReserve,mem_filter,mem_biUnion]
    constructor
    · rintro ⟨⟨e,he,hx⟩,ht⟩
      exact ⟨e,he,hx,ht⟩
    · rintro ⟨e,he,hx,ht⟩
      exact ⟨⟨e,he,hx⟩,ht⟩
  have hEach (e) (he : e ∈ D) :
      ((exteriorReserveArcs e (label e)).filter (touches v)).card ≤
        if touches v e then 1 else 0 := by
    have hz : label e ≠ v := fun hh => hv (hh ▸ hLabel e he)
    by_cases h₁ : e.1 = v <;> by_cases h₂ : e.2 = v
    · exact False.elim (hLoop e he (h₁.trans h₂.symm))
    · simp [exteriorReserveArcs,touches,h₁,h₂,hz,filter_insert,filter_singleton]
    · simp [exteriorReserveArcs,touches,h₁,h₂,hz,filter_insert,filter_singleton]
    · simp [exteriorReserveArcs,touches,h₁,h₂,hz,filter_insert,filter_singleton]
  have hCard : ((usedExteriorReserve D label).filter (touches v)).card ≤
      (D.filter (touches v)).card := by
    rw [hFilter,card_filter]
    exact card_biUnion_le.trans (sum_le_sum hEach)
  unfold touches at hCard
  unfold incidentDegree
  convert hCard using 1 <;> congr 1 <;> ext x <;> simp only [mem_filter]

theorem exteriorTriangle_balanced {V : Type*} {e : V × V} {z : V}
    (huv : e.1 ≠ e.2) (huz : e.1 ≠ z) (hvz : e.2 ≠ z) :
    ArcBalanced (exteriorTriangle e z) := by
  rcases e with ⟨u,v⟩
  dsimp only at huv huz hvz
  intro x
  unfold exteriorTriangle exteriorReserveArcs
  by_cases hu : x = u
  · subst x
    simp [filter_insert,filter_singleton,huv.symm,huz.symm]
  by_cases hv : x = v
  · subst x
    simp [filter_insert,filter_singleton,huv,hvz.symm]
  by_cases hz : x = z
  · subst x
    simp [filter_insert,filter_singleton,huz,hvz]
  simp [filter_insert,filter_singleton,Ne.symm hu,Ne.symm hv,Ne.symm hz]

/-- The exterior triangles cover a balanced arc set, exactly the
exterior leave together with the reserve arcs used in the triangles. -/
theorem exterior_cover_balanced {V : Type*} (U : Finset V) (D : Finset (V × V))
    (label : (V × V) → V)
    (hOuter : ∀ e ∈ D, e.1 ∉ U ∧ e.2 ∉ U)
    (hLabel : ∀ e ∈ D, label e ∈ U) (hLoop : ∀ e ∈ D, e.1 ≠ e.2)
    (hDisj : ∀ e ∈ D, ∀ f ∈ D, e ≠ f →
      Disjoint (exteriorTriangle e (label e)) (exteriorTriangle f (label f))) :
    ArcBalanced (D ∪ usedExteriorReserve D label) := by
  rw [← exteriorTriangle_cover_eq]
  apply arcBalanced_coveredEdges
  · intro K hK M hM hne
    obtain ⟨e,he,rfl⟩ := mem_image.mp hK
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hM
    exact hDisj e he f hf (fun h => hne (congrArg (fun e => exteriorTriangle e (label e)) h))
  · intro K hK
    obtain ⟨e,he,rfl⟩ := mem_image.mp hK
    exact exteriorTriangle_balanced (hLoop e he)
      (fun h => (hOuter e he).1 (h ▸ hLabel e he))
      (fun h => (hOuter e he).2 (h ▸ hLabel e he))

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]

private theorem reserve_triangle_orient
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    {R : TripartiteArcSet A B W} (hR : R ⊆ tripartiteArcs E P Q)
    {u v z : TripartiteVertex A B W} (he : tripartiteArc E P Q u v)
    (hu : (u,z) ∈ R ∨ (z,u) ∈ R) (hv : (v,z) ∈ R ∨ (z,v) ∈ R) :
    (v,z) ∈ R ∧ (z,u) ∈ R := by
  have hAdj (a b : TripartiteVertex A B W)
      (h : (a,b) ∈ R ∨ (b,a) ∈ R) : tripartiteAdjacent E P Q a b :=
    h.imp (fun ha => mem_tripartiteArcs.mp (hR ha)) (fun ha => mem_tripartiteArcs.mp (hR ha))
  have hu' := hAdj u z hu
  have hv' := hAdj v z hv
  have hImpossible : ¬tripartiteArc E P Q u z ∧ ¬tripartiteArc E P Q z v := by
    rcases u with a | (b | w) <;> rcases v with a' | (b' | w') <;>
      rcases z with a'' | (b'' | w'') <;>
      simp only [tripartiteAdjacent,tripartiteArc] at he hu' hv' ⊢ <;> tauto
  exact ⟨hv.resolve_right (fun h => hImpossible.2 (mem_tripartiteArcs.mp (hR h))),
    hu.resolve_left (fun h => hImpossible.1 (mem_tripartiteArcs.mp (hR h)))⟩

/-- The lower bound in (R3) supplies the third vertices needed to cover
all edges of the leave on the exterior of the next level. -/
theorem exists_reserve_cover_of_outer_leave
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (U X : Finset (TripartiteVertex A B W))
    (L R : TripartiteArcSet A B W) (hXU : Disjoint X U)
    (hL : L ⊆ tripartiteArcs E P Q) (hR : R ⊆ tripartiteArcs E P Q)
    (hLR : Disjoint L R)
    {ζ μ ρ n : ℝ} (hSlack : 2*ζ*n < μ^2*ρ*n/20)
    (hDegree : ∀ v, (incidentDegree L v : ℝ) ≤ ζ*n)
    (hR3 : ∀ u ∈ X, ∀ v ∈ X, u ≠ v → tripartiteAdjacent E P Q u v →
      μ^2*ρ*n/20 ≤ ((U.filter (fun z =>
        ((u,z) ∈ R ∨ (z,u) ∈ R) ∧ ((v,z) ∈ R ∨ (z,v) ∈ R))).card : ℝ)) :
    let D := L ∩ (X ×ˢ X)
    ∃ label : (TripartiteVertex A B W × TripartiteVertex A B W) → TripartiteVertex A B W,
      (∀ e ∈ D, label e ∈ U) ∧ usedExteriorReserve D label ⊆ R ∧
      (∀ e ∈ D, ∀ f ∈ D, e ≠ f →
        Disjoint (exteriorTriangle e (label e)) (exteriorTriangle f (label f))) ∧
      (∀ v ∉ U, incidentDegree (usedExteriorReserve D label) v ≤ incidentDegree L v) ∧
      ArcBalanced (D ∪ usedExteriorReserve D label) := by
  intro D
  let C (e : TripartiteVertex A B W × TripartiteVertex A B W) := U.filter (fun z =>
    ((e.1,z) ∈ R ∨ (z,e.1) ∈ R) ∧ ((e.2,z) ∈ R ∨ (z,e.2) ∈ R))
  have hDL : D ⊆ L := inter_subset_left
  have hDX : D ⊆ X ×ˢ X := inter_subset_right
  have hArc (e) (he : e ∈ D) : tripartiteArc E P Q e.1 e.2 :=
    mem_tripartiteArcs.mp (hL (hDL he))
  have hLoop (e) (he : e ∈ D) : e.1 ≠ e.2 := by
    rcases e with ⟨u,v⟩
    intro h
    change u = v at h
    subst v
    have h' := hArc (u,u) he
    rcases u with a | (b | w) <;> exact h'
  have hOut (e) (he : e ∈ D) : e.1 ∉ U ∧ e.2 ∉ U :=
    let hx := mem_product.mp (hDX he)
    ⟨fun h => disjoint_left.mp hXU hx.1 h,fun h => disjoint_left.mp hXU hx.2 h⟩
  have hCand (e) (he : e ∈ D) (z) (hz : z ∈ C e) :
      z ∈ U ∧ (e.2,z) ∈ R ∧ (z,e.1) ∈ R := by
    obtain ⟨hz,ha,hb⟩ := mem_filter.mp hz
    exact ⟨hz,reserve_triangle_orient hR (hArc e he) ha hb⟩
  have hBudget (e) (he : e ∈ D) :
      incidentDegree D e.1 + incidentDegree D e.2 < (C e).card := by
    have hx := mem_product.mp (hDX he)
    have hLow := hR3 e.1 hx.1 e.2 hx.2 (hLoop e he) (Or.inl (hArc e he))
    change μ^2*ρ*n/20 ≤ ((C e).card : ℝ) at hLow
    have h₁ : (incidentDegree D e.1 : ℝ) ≤ incidentDegree L e.1 := by
      exact_mod_cast incidentDegree_mono hDL e.1
    have h₂ : (incidentDegree D e.2 : ℝ) ≤ incidentDegree L e.2 := by
      exact_mod_cast incidentDegree_mono hDL e.2
    exact_mod_cast (show (incidentDegree D e.1 : ℝ) + incidentDegree D e.2 < (C e).card by
      linarith only [h₁,h₂,hDegree e.1,hDegree e.2,hSlack,hLow])
  obtain ⟨label,hLabel,hUsed,hDisj⟩ :=
    exists_exterior_triangle_cover U D R C hOut (hLR.mono_left hDL) hCand hBudget
  have hWhere (e) (he : e ∈ D) : label e ∈ U := (hCand e he _ (hLabel e he)).1
  refine ⟨label,hWhere,hUsed,hDisj,?_,?_⟩
  · intro v hv
    exact (usedExteriorReserve_degree U D label hWhere hLoop v hv).trans (incidentDegree_mono hDL v)
  · have h := exterior_cover_balanced U D label hOut hWhere hLoop hDisj
    convert h using 1
    ext e
    simp only [mem_union]

end OverfullWork.ChenShan
