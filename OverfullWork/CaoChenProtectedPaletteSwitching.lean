module

public import OverfullWork.CaoChenPaletteSwitching

@[expose] public section


/-! # Switching with exact protection of colours outside its three-colour set

The witness is constructed by the actual Kempe swap and edge replacement.
No low-degree or palette-A assumption is needed once the auxiliary common
missing colour has been supplied. This module leaves the existing Lemma 6
interface unchanged.
-/
namespace OverfullWork.CaoChenPalettes
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- The conclusions of the constructed switching needed to preserve a
specified two-colour Kempe graph. -/
structure ProtectedPaletteSwitching (c c' : PEC G (Fin G.maxDegree))
    (x y w : V) (η θ δ : Fin G.maxDegree) : Prop where
  cm : IsColMinus c' x y
  leftRow : ∀ z, c'.col x z=c.col x z
  etaMissing : c'.IsFree y η
  newColour : c'.col y w=some θ
  otherEdges : ∀ γ, γ≠η → γ≠θ → γ≠δ → ∀ a b,
    (c'.col a b=some γ ↔ c.col a b=some γ)
  uncoloured : ∀ a b, c'.col a b=none ↔ c.col a b=none

/-- Perform the protected switching, rather than assuming its outcome.
The edge y-w is overwritten only after theta has been made free at w. -/
theorem exists_protected_palette_switching (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y w : V} (hcm : IsColMinus c x y)
    (η θ δ : Fin G.maxDegree) (hyw : c.col y w=some η)
    (hθy : c.IsFree y θ) (hδx : c.IsFree x δ) (hδw : c.IsFree w δ) :
    ∃ c' : PEC G (Fin G.maxDegree),ProtectedPaletteSwitching c c' x y w η θ δ := by
  have hadj := c.col_adj hyw
  have hxw : x≠w := by
    intro he
    subst w
    rw [c.col_symm,hcm.uncol] at hyw
    contradiction
  have hlink := (hcm.ab_facts hG).2 δ θ hδx hθy
  have hoffx : ¬(c.kempeGraph δ θ).Reachable w x := by
    intro h
    exact not_three_linked c hcm.adj.ne hxw hadj.ne
      (Or.inl hδx) (Or.inr hθy) (Or.inl hδw) hlink h.symm
  have hoffy : ¬(c.kempeGraph δ θ).Reachable w y := fun h => hoffx (h.trans hlink.symm)
  have hηδ : η≠δ := by
    intro he
    exact hδw y (by rw [c.col_symm,hyw,he])
  have hηθ : η≠θ := by intro he;exact hθy w (he ▸ hyw)
  let c₁ := c.kempeSwap δ θ w
  have hcm₁ : IsColMinus c₁ x y := hcm.kempeSwap δ θ w
  have hyw₁ : c₁.col y w=some η := kempeSwap_col_of_ne c δ θ w y w hyw hηδ hηθ
  have hθy₁ : c₁.IsFree y θ :=
    (isFree_kempeSwap_of_not_reachable c δ θ hoffy θ).mpr hθy
  have hθw₁ : c₁.IsFree w θ := by
    rw [isFree_kempeSwap_of_reachable c δ θ (SimpleGraph.Reachable.refl w),Equiv.swap_apply_right]
    exact hδw
  let c₂ := c₁.setEdge θ hadj hθy₁ hθw₁
  have hleft : ∀ z,c₂.col x z=c.col x z := by
    intro z
    rw [setEdge_col_of_ne_left c₁ θ hadj hθy₁ hθw₁ hcm.adj.ne hxw,
      kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hoffx]
  have hpair : ∀ γ,γ≠θ → γ≠δ → ∀ a b,(c₁.col a b=some γ ↔ c.col a b=some γ) := by
    intro γ hγθ hγδ a b
    by_cases hr : (c.kempeGraph δ θ).Reachable w a
    · rw [kempeSwap_col,kempeSwapFun_of_reachable c δ θ hr b]
      cases he : c.col a b with
      | none => simp
      | some ε => simp only [Option.map_some,Option.some.injEq,Equiv.swap_apply_eq_iff,
          Equiv.swap_apply_of_ne_of_ne hγδ hγθ]
    · rw [kempeSwap_col,kempeSwapFun_of_not_reachable c δ θ hr b]
  refine ⟨c₂,⟨?_,hleft,?_,by simp [c₂],?_,?_⟩⟩
  · exact ⟨hcm.adj,by rw [hleft,hcm.uncol],fun a b hab hne =>
      extends_setEdge c₁ θ hadj hθy₁ hθw₁ a b (hcm₁.total a b hab hne)⟩
  · exact isFree_setEdge_old c₁ θ hadj hθy₁ hθw₁ hyw₁
  · intro γ hγη hγθ hγδ a b
    by_cases he : (a=y ∧ b=w) ∨ (a=w ∧ b=y)
    · have hold : c.col a b=some η := by
        rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hyw
        · rw [c.col_symm];exact hyw
      have hnew : c₂.col a b=some θ := by
        rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [c₂,setEdge_col,updFun]
      rw [hnew,hold]
      simp [Ne.symm hγθ,Ne.symm hγη]
    · change (updFun c₁.col y w (some θ) a b=some γ ↔ _)
      rw [updFun_of_ne _ he]
      exact hpair γ hγθ hγδ a b
  · intro a b
    by_cases he : (a=y ∧ b=w) ∨ (a=w ∧ b=y)
    · have hold : c.col a b=some η := by
        rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hyw
        · rw [c.col_symm];exact hyw
      have hnew : c₂.col a b=some θ := by
        rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [c₂,setEdge_col,updFun]
      rw [hnew,hold]
      simp
    · change (updFun c₁.col y w (some θ) a b=none ↔ _)
      rw [updFun_of_ne _ he,kempeSwap_col]
      by_cases hr : (c.kempeGraph δ θ).Reachable w a
      · rw [kempeSwapFun_of_reachable c δ θ hr b]
        cases hec : c.col a b <;> simp
      · rw [kempeSwapFun_of_not_reachable c δ θ hr b]

end OverfullWork.CaoChenPalettes
