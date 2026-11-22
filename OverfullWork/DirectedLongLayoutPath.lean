module

public import OverfullWork.DirectedCoverStitching
public import OverfullWork.DirectedMarkerSplit
public import OverfullWork.AlmostRegularDirectedPathCover
public import OverfullWork.DirectedSpanningConfiguration

@[expose] public section


/-! The distinguished flexible edge in GGKLO Lemma 7.3(i). Its endpoints
are contracted to a marker before covering the dense part. -/
namespace OverfullWork.DirectedLongLayoutPath

open Finset DirectedRobustExpansion RankedDirectedPathCover
  DirectedReserveStitching DirectedSpanningConfiguration
open scoped Classical
universe u v w

/-- In the bulk the marker inherits its outgoing arcs from the first
endpoint and its incoming arcs from the second endpoint. -/
def markerBulk {V W Y : Type*} (D : Digraph V) (e : W ↪ V) (d : Y ↪ V) (a b : V) :
    Digraph (W ⊕ Option Y) where
  Adj x y := D.Adj (x.elim e (fun y => y.elim a d)) (y.elim e (fun y => y.elim b d))

def denseWithMarker {V W Y : Type*} (D : Digraph V) (e : W ↪ V) (d : Y ↪ V) (a b : V) :
    Digraph (Option Y) where
  Adj x y := (markerBulk D e d a b).Adj (.inr x) (.inr y)

/-- Realize the long edge with prescribed interior support. Every arc is
a bulk arc or an arc induced by the designated reserve block. -/
theorem exists_long_path_uniform_in_density (ν τ α d₀ ρ η : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) (hd₀ : 0 < d₀) (hρ : 0 < ρ) (hη : 0 < η)
    (hGap : 8*η ≤ d₀) (hScale : 52*η ≤ ρ*d₀) :
    ∃ N₀ N₁ : ℕ, ∀ (δ : ℝ), d₀ ≤ δ → δ ≤ 1 → ∀ {V : Type u} {W : Type v} [Fintype W]
      {Y : Type w} [Fintype Y] (D : Digraph V) (Γ : Digraph W) (e : W ↪ V) (d : Y ↪ V)
      (a b : V), N₀ ≤ Fintype.card W → N₁ ≤ Fintype.card (Option Y) →
      a ≠ b → Disjoint (Set.range d) (Set.range e) →
      a ∉ Set.range d → b ∉ Set.range d → a ∉ Set.range e → b ∉ Set.range e →
      Nonempty W → IsRealRobust Γ ν τ →
      (∀ w, α*(Fintype.card W:ℝ) ≤ (inDegree Γ w:ℝ)) →
      (∀ w, α*(Fintype.card W:ℝ) ≤ (outDegree Γ w:ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (inDegree (denseWithMarker D e d a b) x:ℝ) ∧
        (inDegree (denseWithMarker D e d a b) x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (outDegree (denseWithMarker D e d a b) x:ℝ) ∧
        (outDegree (denseWithMarker D e d a b) x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      ρ*(Fintype.card (Option Y):ℝ) ≤ (ν/4)^3*(Fintype.card W:ℝ) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset W).filter (fun w => D.Adj (y.elim a d) (e w))).card:ℝ)) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset W).filter (fun w => D.Adj (e w) (y.elim b d))).card:ℝ)) →
      ∃ l : List V, l ≠ [] ∧ (a :: l ++ [b]).Nodup ∧
        (a :: l ++ [b]).IsChain (mixed D Γ e).Adj ∧
        (∀ x, x ∈ l ↔ x ∈ Set.range e ∨ x ∈ Set.range d) := by
  obtain ⟨N₀,hStitch⟩ := exists_cycle_of_dense_cover_threshold.{max v w,v,w}
    ν τ α hν hντ hτα hα
  obtain ⟨N₁,hC⟩ :=
    AdjacentLayerPathCover.exists_small_cover_uniform_in_density.{w} d₀ ρ η hd₀ hρ hη hGap hScale
  refine ⟨N₀,N₁,?_⟩
  intro δ hδ₀ hδ₁
  intro V W _ Y _ D Γ e d a b hN₀ hN₁ hab hApart haD hbD haE hbE hW hR hIn hOut
    hDenseIn hDenseOut hBudget hTo hFrom
  let B := markerBulk D e d a b
  let e' : W ↪ W ⊕ Option Y := ⟨Sum.inl,Sum.inl_injective⟩
  let d' : Option Y ↪ W ⊕ Option Y := ⟨Sum.inr,Sum.inr_injective⟩
  let z : W ⊕ Option Y := .inr none
  let f : W ⊕ Option Y → V := fun x => x.elim e (fun y => y.elim a d)
  obtain ⟨H,hHB,⟨C⟩,hC⟩ := hC δ hδ₀ hδ₁ (denseWithMarker D e d a b) hN₁ hDenseIn hDenseOut
  have hDis : Disjoint (Set.range d') (Set.range e') := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,rfl⟩ ⟨y,he⟩
    cases he
  have hLift : ∀ {x y}, H.Adj x y → B.Adj (d' x) (d' y) := fun {_ _} h => hHB h
  have hTo' : ∀ y : Option Y, 2*(terminals H.Adj (univ : Finset (Option Y))).card ≤
      ((univ : Finset W).filter (fun w => B.Adj (d' y) (e' w))).card := by
    intro y
    have hBound : (2:ℝ)*((terminals H.Adj (univ : Finset (Option Y))).card:ℝ) ≤
        (((univ : Finset W).filter (fun w => B.Adj (d' y) (e' w))).card:ℝ) := calc
      _ ≤ 2*ρ*(Fintype.card (Option Y):ℝ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hC (by norm_num)
      _ ≤ _ := hTo y
    exact_mod_cast hBound
  have hFrom' : ∀ y : Option Y, 2*(terminals H.Adj (univ : Finset (Option Y))).card ≤
      ((univ : Finset W).filter (fun w => B.Adj (e' w) (d' y))).card := by
    intro y
    have hBound : (2:ℝ)*((terminals H.Adj (univ : Finset (Option Y))).card:ℝ) ≤
        (((univ : Finset W).filter (fun w => B.Adj (e' w) (d' y))).card:ℝ) := calc
      _ ≤ 2*ρ*(Fintype.card (Option Y):ℝ) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hC (by norm_num)
      _ ≤ _ := hFrom y
    exact_mod_cast hBound
  obtain ⟨T,root,hND,hHead,hCycle,hSpans,_⟩ := hStitch B Γ e' H d' hN₀ hR hIn hOut
    hLift hDis C (hC.trans hBudget) hTo' hFrom'
  have hAll (x : W ⊕ Option Y) : x ∈ T := (hSpans x).2 (by
    cases x with
    | inl y => exact Or.inl ⟨y,rfl⟩
    | inr y => exact Or.inr ⟨y,rfl⟩)
  have hFresh : ∀ x : W ⊕ Option Y, x ≠ z → f x ≠ a ∧ f x ≠ b := by
    rintro (x | (_ | y)) hx
    · exact ⟨fun h => haE ⟨x,h⟩,fun h => hbE ⟨x,h⟩⟩
    · exact (hx rfl).elim
    · exact ⟨fun h => haD ⟨y,h⟩,fun h => hbD ⟨y,h⟩⟩
  have hInj : Set.InjOn f {x | x ≠ z} := by
    rintro (x | (_ | x)) hx (y | (_ | y)) hy he
    · exact congrArg Sum.inl (e.injective he)
    · exact (hy rfl).elim
    · exact (Set.disjoint_left.mp hApart ⟨y,he.symm⟩ ⟨x,rfl⟩).elim
    · exact (hx rfl).elim
    · exact (hx rfl).elim
    · exact (hx rfl).elim
    · exact (Set.disjoint_left.mp hApart ⟨x,he⟩ ⟨y,rfl⟩).elim
    · exact (hy rfl).elim
    · exact congrArg (Sum.inr ∘ some) (d.injective he)
  have hOutMap (x : W ⊕ Option Y) :
      (if x = z then a else f x) = x.elim e (fun y => y.elim a d) := by
    rcases x with x | (_ | x) <;> simp [z,f]
  have hInMap (x : W ⊕ Option Y) :
      (if x = z then b else f x) = x.elim e (fun y => y.elim b d) := by
    rcases x with x | (_ | x) <;> simp [z,f]
  have hRangeOut (x : W ⊕ Option Y) :
      x.elim e (fun y => y.elim a d) ∈ Set.range e ↔ x ∈ Set.range e' := by
    rcases x with x | (_ | x)
    · exact ⟨fun _ => ⟨x,rfl⟩,fun _ => ⟨x,rfl⟩⟩
    · simpa [e',Set.mem_range,Sum.inl_ne_inr] using haE
    · have h := fun he => Set.disjoint_left.mp hApart (Set.mem_range_self x) he
      simpa [e',Set.mem_range,Sum.inl_ne_inr] using h
  have hRangeIn (x : W ⊕ Option Y) :
      x.elim e (fun y => y.elim b d) ∈ Set.range e ↔ x ∈ Set.range e' := by
    rcases x with x | (_ | x)
    · exact ⟨fun _ => ⟨x,rfl⟩,fun _ => ⟨x,rfl⟩⟩
    · simpa [e',Set.mem_range,Sum.inl_ne_inr] using hbE
    · have h := fun he => Set.disjoint_left.mp hApart (Set.mem_range_self x) he
      simpa [e',Set.mem_range,Sum.inl_ne_inr] using h
  have hDecode : ∀ ⦃x y⦄, (mixed B Γ e').Adj x y →
      (mixed D Γ e).Adj (if x = z then a else f x) (if y = z then b else f y) := by
    intro x y h
    rw [hOutMap,hInMap]
    rcases h with ⟨p,q,hpq,rfl,rfl⟩ | ⟨hOutside,hBulk⟩
    · exact Or.inl ⟨p,q,hpq,rfl,rfl⟩
    · exact Or.inr ⟨by simpa only [hRangeOut,hRangeIn] using hOutside,hBulk⟩
  obtain ⟨l,hPerm,hPath,hSimple,_⟩ :=
    DirectedMarkerSplit.exists_path_of_split_marker (mixed B Γ e') (mixed D Γ e)
      T root z f a b hHead hCycle hND (hAll z) hab hInj (fun x _ => hFresh x) (by
        intro x y h
        by_cases hx : x = z <;> by_cases hy : y = z <;> simpa [hx,hy] using hDecode h)
  have hz : z ∉ l := (List.nodup_cons.mp (hPerm.nodup_iff.mpr hND)).1
  have hTail {x : W ⊕ Option Y} (hx : x ≠ z) : x ∈ l :=
    (List.mem_cons.mp (hPerm.mem_iff.mpr (hAll x))).resolve_left hx
  have hInterior (x : V) : x ∈ l.map f ↔ x ∈ Set.range e ∨ x ∈ Set.range d := by
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
      rcases y with y | (_ | y)
      · exact Or.inl ⟨y,rfl⟩
      · exact (hz hy).elim
      · exact Or.inr ⟨y,rfl⟩
    · rintro (⟨y,rfl⟩ | ⟨y,rfl⟩)
      · exact List.mem_map.mpr ⟨.inl y,hTail (by simp [z]),rfl⟩
      · exact List.mem_map.mpr ⟨.inr (some y),hTail (by simp [z]),rfl⟩
  refine ⟨l.map f,?_,hSimple,hPath,hInterior⟩
  intro hEmpty
  obtain ⟨x⟩ := hW
  have hX := (hInterior (e x)).2 (Or.inl ⟨x,rfl⟩)
  simp [hEmpty] at hX

theorem exists_long_path_threshold (ν τ α δ ρ : ℝ) (hν : 0 < ν) (hντ : ν ≤ τ)
    (hτα : 256*τ ≤ α) (hα : α ≤ 1) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ N₁ : ℕ, ∀ {V : Type u} {W : Type v} [Fintype W]
      {Y : Type w} [Fintype Y] (D : Digraph V) (Γ : Digraph W) (e : W ↪ V) (d : Y ↪ V)
      (a b : V), N₀ ≤ Fintype.card W → N₁ ≤ Fintype.card (Option Y) →
      a ≠ b → Disjoint (Set.range d) (Set.range e) →
      a ∉ Set.range d → b ∉ Set.range d → a ∉ Set.range e → b ∉ Set.range e →
      Nonempty W → IsRealRobust Γ ν τ →
      (∀ w, α*(Fintype.card W:ℝ) ≤ (inDegree Γ w:ℝ)) →
      (∀ w, α*(Fintype.card W:ℝ) ≤ (outDegree Γ w:ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (inDegree (denseWithMarker D e d a b) x:ℝ) ∧
        (inDegree (denseWithMarker D e d a b) x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (outDegree (denseWithMarker D e d a b) x:ℝ) ∧
        (outDegree (denseWithMarker D e d a b) x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      ρ*(Fintype.card (Option Y):ℝ) ≤ (ν/4)^3*(Fintype.card W:ℝ) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset W).filter (fun w => D.Adj (y.elim a d) (e w))).card:ℝ)) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset W).filter (fun w => D.Adj (e w) (y.elim b d))).card:ℝ)) →
      ∃ l : List V, l ≠ [] ∧ (a :: l ++ [b]).Nodup ∧
        (a :: l ++ [b]).IsChain (mixed D Γ e).Adj ∧
        (∀ x, x ∈ l ↔ x ∈ Set.range e ∨ x ∈ Set.range d) := by
  let η := min (δ/8) (ρ*δ/52)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hGap : 8*η ≤ δ := by
    have h : η ≤ δ/8 := min_le_left _ _
    linarith only [h]
  have hScale : 52*η ≤ ρ*δ := by
    have h : η ≤ ρ*δ/52 := min_le_right _ _
    linarith only [h]
  obtain ⟨N₀,N₁,hN⟩ := exists_long_path_uniform_in_density.{u,v,w} ν τ α δ ρ η
    hν hντ hτα hα hδ hρ hη hGap hScale
  exact ⟨η,hη,N₀,N₁,hN δ le_rfl hδ₁⟩

end OverfullWork.DirectedLongLayoutPath
