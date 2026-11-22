module

public import OverfullWork.DirectedLayoutRound
public import OverfullWork.DirectedLongLayoutPath
public import OverfullWork.InducedDigraphSampling

@[expose] public section


/-! Construct the long portion on exactly the remaining vertices of a round. -/
namespace OverfullWork.DirectedSpanningConfiguration

open Finset DirectedRobustExpansion DirectedReserveStitching DirectedLongLayoutPath
  InducedDigraphSampling
open scoped Classical
universe u v

noncomputable def ShortPortion.denseVertices {V I : Type*} [Fintype V]
    {D : Digraph V} {L : Layout V I} {long : I}
    (S : ShortPortion D L long) (A : Finset V) : Finset V :=
  univ.filter (fun x => S.remaining x ∧ x ∉ A)

/-- Given the short portion and the residual estimates on its complement,
construct the whole round, including its fixed copies. The conclusion
retains the separate bulk and reserve provenance of the long path. -/
theorem exists_completed_round_uniform_in_density (ν τ α d₀ ρ η : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1)
    (hd₀ : 0 < d₀) (hρ : 0 < ρ) (hη : 0 < η)
    (hGap : 8*η ≤ d₀) (hScale : 52*η ≤ ρ*d₀) :
    ∃ N₀ N₁ : ℕ, ∀ (δ : ℝ), d₀ ≤ δ → δ ≤ 1 → ∀ {V : Type u} [Fintype V] {I : Type v}
      (D Γ K : Digraph V) (L : Layout V I) (long : I) (A : Finset V)
      (S : ShortPortion K L long),
      let e : A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      let Y := S.denseVertices A
      let d : Y ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      let B := denseWithMarker D e d (L.source long) (L.target long)
      long ∉ L.fixed → 0 < A.card → N₀ ≤ A.card → N₁ ≤ Fintype.card (Option Y) →
      (∀ x ∈ A, S.remaining x) → IsRealRobust (induced Γ A) ν τ →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (inDegree (induced Γ A) v:ℝ)) →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (outDegree (induced Γ A) v:ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (inDegree B x:ℝ) ∧
        (inDegree B x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (outDegree B x:ℝ) ∧
        (outDegree B x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      ρ*(Fintype.card (Option Y):ℝ) ≤ (ν/4)^3*(Fintype.card A:ℝ) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset A).filter (fun w => D.Adj (y.elim (L.source long) d) (e w))).card:ℝ)) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset A).filter (fun w => D.Adj (e w) (y.elim (L.target long) d))).card:ℝ)) →
      ∃ R : Realization (K ⊔ mixed D (induced Γ A) e) L,
        (∀ i ∉ insert long L.fixed, R.interior i = S.interior i) ∧
        wordGraph (R.word long) ≤ mixed D (induced Γ A) e ∧
        (∀ i ∉ insert long L.fixed, wordGraph (R.word i) ≤ K) := by
  obtain ⟨N₀,N₁,hExec⟩ := exists_long_path_uniform_in_density.{u,u,u} ν τ α d₀ ρ η hν hντ
    hτα hα hd₀ hρ hη hGap hScale
  refine ⟨N₀,N₁,?_⟩
  intro δ hδ₀ hδ₁
  intro V _ I D Γ K L long A S
  dsimp only
  intro hlong hPos hN₀ hN₁ hA hR hIn hOut hDenseIn hDenseOut hBudget hFrom hTo
  let e : A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let Y := S.denseVertices A
  let d : Y ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have hA' (v : V) : v ∈ Set.range e ↔ v ∈ A := by
    exact ⟨fun ⟨x,hx⟩ => hx ▸ x.prop,fun hx => ⟨⟨v,hx⟩,rfl⟩⟩
  have hY (v : V) : v ∈ Set.range d ↔ S.remaining v ∧ v ∉ A := by
    have hMem : v ∈ Y ↔ S.remaining v ∧ v ∉ A := by simp [Y,ShortPortion.denseVertices]
    exact ⟨fun ⟨x,hx⟩ => hMem.mp (hx ▸ x.prop),fun hx => ⟨⟨v,hMem.mpr hx⟩,rfl⟩⟩
  have hApart : Disjoint (Set.range d) (Set.range e) :=
    Set.disjoint_left.mpr fun v hd he => ((hY v).1 hd).2 ((hA' v).1 he)
  have hS := (L.ends long).1
  have hT := (L.ends long).2.1
  obtain ⟨w,hw⟩ := card_pos.mp hPos
  obtain ⟨l,hNE,hND,hChain,hSpans⟩ := hExec δ hδ₀ hδ₁ D (induced Γ A) e d (L.source long) (L.target long)
    (by simpa only [Fintype.card_coe] using hN₀) hN₁ (L.ends long).2.2 hApart
    (fun hx => ((hY _).1 hx).1.1 hS) (fun hx => ((hY _).1 hx).1.1 hT)
    (fun hx => (hA _ ((hA' _).1 hx)).1 hS) (fun hx => (hA _ ((hA' _).1 hx)).1 hT)
    ⟨⟨w,hw⟩⟩ hR hIn hOut hDenseIn hDenseOut hBudget hFrom hTo
  have hSupport (x : V) : x ∈ l ↔ S.remaining x := by
    rw [hSpans,hA',hY]
    by_cases hx : x ∈ A
    · simp [hx,hA x hx]
    · simp [hx]
  obtain ⟨R,_,hShort,hLong,hShortGraph⟩ :=
    complete_round hlong S l hNE hND hChain hSupport
  exact ⟨R,hShort,hLong,hShortGraph⟩

theorem exists_completed_round_threshold (ν τ α δ ρ : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1)
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hρ : 0 < ρ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ N₁ : ℕ, ∀ {V : Type u} [Fintype V] {I : Type v}
      (D Γ K : Digraph V) (L : Layout V I) (long : I) (A : Finset V)
      (S : ShortPortion K L long),
      let e : A ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      let Y := S.denseVertices A
      let d : Y ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
      let B := denseWithMarker D e d (L.source long) (L.target long)
      long ∉ L.fixed → 0 < A.card → N₀ ≤ A.card → N₁ ≤ Fintype.card (Option Y) →
      (∀ x ∈ A, S.remaining x) → IsRealRobust (induced Γ A) ν τ →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (inDegree (induced Γ A) v:ℝ)) →
      (∀ v : A, α*(Fintype.card A:ℝ) ≤ (outDegree (induced Γ A) v:ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (inDegree B x:ℝ) ∧
        (inDegree B x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      (∀ x, (δ-η)*(Fintype.card (Option Y):ℝ) ≤ (outDegree B x:ℝ) ∧
        (outDegree B x:ℝ) ≤ (δ+η)*(Fintype.card (Option Y):ℝ)) →
      ρ*(Fintype.card (Option Y):ℝ) ≤ (ν/4)^3*(Fintype.card A:ℝ) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset A).filter (fun w => D.Adj (y.elim (L.source long) d) (e w))).card:ℝ)) →
      (∀ y : Option Y, 2*ρ*(Fintype.card (Option Y):ℝ) ≤
        (((univ : Finset A).filter (fun w => D.Adj (e w) (y.elim (L.target long) d))).card:ℝ)) →
      ∃ R : Realization (K ⊔ mixed D (induced Γ A) e) L,
        (∀ i ∉ insert long L.fixed, R.interior i = S.interior i) ∧
        wordGraph (R.word long) ≤ mixed D (induced Γ A) e ∧
        (∀ i ∉ insert long L.fixed, wordGraph (R.word i) ≤ K) := by
  let η := min (δ/8) (ρ*δ/52)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hGap : 8*η ≤ δ := by
    have h : η ≤ δ/8 := min_le_left _ _
    linarith only [h]
  have hScale : 52*η ≤ ρ*δ := by
    have h : η ≤ ρ*δ/52 := min_le_right _ _
    linarith only [h]
  obtain ⟨N₀,N₁,hN⟩ := exists_completed_round_uniform_in_density.{u,v} ν τ α δ ρ η
    hν hντ hτα hα hδ hρ hη hGap hScale
  exact ⟨η,hη,N₀,N₁,hN δ le_rfl hδ₁⟩

end OverfullWork.DirectedSpanningConfiguration
