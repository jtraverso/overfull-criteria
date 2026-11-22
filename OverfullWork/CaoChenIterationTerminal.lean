module

public import OverfullWork.CaoChenInitialFiniteState

@[expose] public section


/-! # A terminal finite state contradicts the actual fan certificate

The terminal subset Xi, its protected auxiliary and its B1 role are all
derived from the initial data and the final finite state. No terminal
certificate is supplied as a hypothesis.
-/
namespace OverfullWork.CaoChenIterationTerminal
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenFiniteIteration CaoChenInitialFiniteState
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

/-- The actual terminal selected palette supplies Xi and all hypotheses
of the already proved contradiction. -/
theorem no_terminal_finite_state (hG : IsClassTwo G)
    {c₀ c d : PEC G (Fin G.maxDegree)} {x y z u : V} {α β δ : Fin G.maxDegree}
    {T₀ T I F : Finset (Fin G.maxDegree)} {k : ℕ}
    (ε : ℝ) (hε : 0<ε)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ)) (hβα : β≠α)
    (hi : InitialData c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y z u α β δ T₀ I F k)
    (hs : State c d ((1-ε)*(G.maxDegree:ℝ)) x y u α T₀ T I F k (2*k+5) k) : False := by
  have hβF : β∈F := by rw [hi.protectedFamily];simp
  have hδF : δ∈F := by rw [hi.protectedFamily];simp
  have hxz : d.col x z=some α := by rw [hs.rootRow];exact hi.specialSpine
  have hxu : d.col x u=some β := by rw [hs.rootRow];exact hi.betaSpine
  obtain ⟨Ξ,hΞsub,hΞcard⟩:=exists_subset_card_eq hs.score
  have hΞ : Ξ⊆missing d x∩badColours d ((1-ε)*(G.maxDegree:ℝ)) u := by
    intro γ hγ
    obtain ⟨hγT,hγX⟩:=mem_inter.mp (hΞsub hγ)
    exact mem_inter.mpr ⟨hγX,(mem_inter.mp (hs.selected hγT)).1⟩
  have hsize : 1≤ε*((Ξ.card:ℝ)+1) := by
    simpa only [hΞcard,Nat.cast_add,Nat.cast_one] using hscale
  have hrole := hs.spine_role hi.specialSpine hi.specialNotExceptional
  have hrole' : CaoChenSecondarySpineNormalization.SpineRole d ((1-ε)*(G.maxDegree:ℝ))
      x y α (Ξ.card+1) := by
    rcases hrole with hfree|⟨v,hyv,hvlow,hvlarge⟩
    · exact Or.inl hfree
    · exact Or.inr ⟨v,hyv,hvlow,by dsimp [margin] at hvlarge;omega⟩
  have halt : d.IsFree z β ∨ ∃t : V,∃η : Fin G.maxDegree,
      d.col z t=some β ∧ d.IsFree x η ∧ d.IsFree t η ∧ η∉Ξ := by
    rcases hi.alternative with hfree|⟨t,hzt,hδt⟩
    · exact Or.inl ((hs.protected_free_iff hβF z).mpr hfree)
    · have hδT : δ∉T := by
        intro h
        exact hi.auxiliaryNotSelected ((hs.protectedMembership δ hδF).mp h)
      exact Or.inr ⟨t,δ,(hs.protectedColours z t β hβF).mpr hzt,
        (hs.protected_free_iff hδF x).mpr hi.auxiliaryMissing,
        (hs.protected_free_iff hδF t).mpr hδt,
        fun h => hδT (mem_inter.mp (hΞsub h)).1⟩
  exact CaoChenTerminalAssembly.no_large_root_spine_certificate hG hs.cm hxz hxu hβα
    ε hε hx Ξ hΞ hsize hrole' halt

end OverfullWork.CaoChenIterationTerminal
