module

public import OverfullWork.CaoChenLemma7Terminal
public import OverfullWork.CaoChenFullPaletteSwitching
public import OverfullWork.CaoChenSecondarySpineNormalization

@[expose] public section


/-! # Transporting the Claim-5.3 certificate to the terminal contradiction

The certificate concerns a feasible neighbour z, while the current deleted
edge is xy. The first construction shifts the hole to xz and proves exact
protection of every other colour. The final assembly also handles the
weaker B1 alternative in which the special colour is in A with a large
missing-palette overlap.
-/
namespace OverfullWork.CaoChenTerminalAssembly
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenLemma7Terminal
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

/-- Move the hole from xy to xz, preserving the root's missing palette
and every entire colour class other than the moved colour. -/
theorem exists_shift_with_colour_protection
    {c : PEC G (Fin G.maxDegree)} {x y z : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α) (hα : c.IsFree y α) :
    ∃ψ : PEC G (Fin G.maxDegree),IsColMinus ψ x z ∧
      (∀γ,ψ.IsFree x γ↔c.IsFree x γ) ∧
      ∀a b γ,γ≠α → (ψ.col a b=some γ↔c.col a b=some γ) := by
  have hyz : y≠z := by
    intro he
    subst z
    rw [hcm.uncol] at hxz
    contradiction
  obtain ⟨ψ,hψ,hyx,hoff,hfx,_,_⟩:=exists_shift hcm.symm hxz hα hyz
  refine ⟨ψ,hψ.symm,hfx,?_⟩
  intro a b γ hγα
  by_cases hxy : (a=y ∧ b=x) ∨ (a=x ∧ b=y)
  · have hold : c.col a b=none := by
      rcases hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · rw [c.col_symm,hcm.uncol]
      · exact hcm.uncol
    have hnew : ψ.col a b=some α := by
      rcases hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact hyx
      · rw [ψ.col_symm];exact hyx
    rw [hold,hnew]
    simp [Ne.symm hγα]
  · by_cases hxz' : (a=x ∧ b=z) ∨ (a=z ∧ b=x)
    · have hold : c.col a b=some α := by
        rcases hxz' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hxz
        · rw [c.col_symm];exact hxz
      have hnew : ψ.col a b=none := by
        rcases hxz' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rw [ψ.col_symm];exact hψ.uncol
        · exact hψ.uncol
      rw [hold,hnew]
      simp [Ne.symm hγα]
    · rw [hoff a b hxy hxz']

/-- The terminal certificate at a feasible neighbour is contradictory
even though the original uncoloured edge has the other endpoint y. -/
theorem no_certificate_at_feasible_neighbour (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α) (hα : c.IsFree y α)
    (hxu : c.col x u=some β) (hβα : β≠α)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (Ξ : Finset (Fin G.maxDegree))
    (hΞ : Ξ⊆missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u)
    (hsize : 1≤ε*((Ξ.card:ℝ)+1))
    (halt : c.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      c.col z t=some β ∧ c.IsFree x δ ∧ c.IsFree t δ ∧ δ∉Ξ) : False := by
  obtain ⟨ψ,hψ,hfree,hclasses⟩:=exists_shift_with_colour_protection hcm hxz hα
  have hxu' : ψ.col x u=some β := (hclasses x u β hβα).mpr hxu
  have hΞ' : Ξ⊆missing ψ x∩badColours ψ ((1-ε)*(G.maxDegree:ℝ)) u := by
    intro γ hγ
    obtain ⟨hγx,hγbad⟩:=mem_inter.mp (hΞ hγ)
    have hf := mem_missing.mp hγx
    have hγα : γ≠α := by intro he;exact hf z (he ▸ hxz)
    refine mem_inter.mpr ⟨mem_missing.mpr ((hfree γ).mpr hf),?_⟩
    apply (mem_badColours ψ _ u γ).mpr
    rcases (mem_badColours c _ u γ).mp hγbad with hmissing|⟨w,hw,hd⟩
    · exact Or.inl (fun w hw => hmissing w ((hclasses u w γ hγα).mp hw))
    · exact Or.inr ⟨w,(hclasses u w γ hγα).mpr hw,hd⟩
  have halt' : ψ.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      ψ.col z t=some β ∧ ψ.IsFree x δ ∧ ψ.IsFree t δ ∧ δ∉Ξ := by
    rcases halt with hβ|⟨t,δ,hzt,hδx,hδt,hδΞ⟩
    · exact Or.inl (fun w hw => hβ w ((hclasses z w β hβα).mp hw))
    · have hδα : δ≠α := by intro he;exact hδx z (he ▸ hxz)
      exact Or.inr ⟨t,δ,(hclasses z t β hβα).mpr hzt,(hfree δ).mpr hδx,
        fun w hw => hδt w ((hclasses t w δ hδα).mp hw),hδΞ⟩
  exact no_terminal_palette_certificate hG hψ hxu' ε hε hx Ξ hΞ' hsize halt'

private theorem setEdge_other_colour_iff
    (c : PEC G (Fin G.maxDegree)) {y w : V} {α θ γ : Fin G.maxDegree}
    (hyw : c.col y w=some α) (hθy : c.IsFree y θ) (hθw : c.IsFree w θ)
    (hγα : γ≠α) (hγθ : γ≠θ) (a b : V) :
    (c.setEdge θ (c.col_adj hyw) hθy hθw).col a b=some γ ↔ c.col a b=some γ := by
  by_cases he : (a=y ∧ b=w) ∨ (a=w ∧ b=y)
  · have hold : c.col a b=some α := by
      rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact hyw
      · rw [c.col_symm];exact hyw
    have hnew : (c.setEdge θ (c.col_adj hyw) hθy hθw).col a b=some θ := by
      rcases he with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [setEdge_col,updFun]
    rw [hold,hnew]
    simp [Ne.symm hγα,Ne.symm hγθ]
  · rw [setEdge_col,updFun_of_ne _ he]

/-- A large A-leaf overlap supplies the auxiliary colour outside a
specified root-missing set. If the leaf shares a missing colour with y,
a direct recolouring is constructed instead. The spine colour beta is
protected in either construction. -/
theorem exists_special_colour_missing_with_protection (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y w u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (q : ℝ) (hαA : α∈paletteA c q x y)
    (hyw : c.col y w=some α) (hxu : c.col x u=some β)
    (hβα : β≠α) (hβy : ¬c.IsFree y β)
    (F : Finset (Fin G.maxDegree)) (hF : F⊆missing c x)
    (hlarge : F.card<(missing c w∩(missing c x∪missing c y)).card) :
    ∃c' : PEC G (Fin G.maxDegree),IsColMinus c' x y ∧
      (∀v,c'.col x v=c.col x v) ∧ c'.IsFree y α ∧
      ∀a b γ,γ∈F∪{β} → (c'.col a b=some γ↔c.col a b=some γ) := by
  have hxw : x≠w := by
    intro he
    subst w
    rw [c.col_symm,hcm.uncol] at hyw
    contradiction
  have hFα : ∀γ∈F,γ≠α := by
    intro γ hγ he
    subst γ
    exact (mem_presentColours c x α).mp ((mem_paletteA c q x y α).mp hαA).1
      (mem_missing.mp (hF hγ))
  by_cases hc : (missing c w∩missing c y).Nonempty
  · obtain ⟨θ,hθ⟩:=hc
    obtain ⟨hθw,hθy⟩:=mem_inter.mp hθ
    have hfreew := mem_missing.mp hθw
    have hfreey := mem_missing.mp hθy
    let c' := c.setEdge θ (c.col_adj hyw) hfreey hfreew
    have hrow : ∀v,c'.col x v=c.col x v := by
      intro v
      exact setEdge_col_of_ne_left c θ (c.col_adj hyw) hfreey hfreew hcm.adj.ne hxw v
    refine ⟨c',⟨hcm.adj,by rw [hrow,hcm.uncol],?_⟩,hrow,?_,?_⟩
    · intro a b hab hne
      exact extends_setEdge c θ (c.col_adj hyw) hfreey hfreew a b (hcm.total a b hab hne)
    · exact isFree_setEdge_old c θ (c.col_adj hyw) hfreey hfreew hyw
    · intro a b γ hγ
      have hγα : γ≠α := by
        rcases mem_union.mp hγ with hγF|hγβ
        · exact hFα γ hγF
        · have he : γ=β := mem_singleton.mp hγβ
          exact he.trans_ne hβα
      have hγθ : γ≠θ := by
        rcases mem_union.mp hγ with hγF|hγβ
        · intro he
          subst γ
          exact (hcm.ab_facts hG).1 θ (mem_missing.mp (hF hγF)) hfreey
        · have he : γ=β := mem_singleton.mp hγβ
          subst γ
          intro he
          exact hβy (he ▸ hfreey)
      exact setEdge_other_colour_iff c hyw hfreey hfreew hγα hγθ a b
  · have hnotY : ∀γ∈missing c w,γ∉missing c y := by
      intro γ hw hy
      exact hc ⟨γ,mem_inter.mpr ⟨hw,hy⟩⟩
    have hsub : missing c w∩(missing c x∪missing c y)⊆missing c w∩missing c x := by
      intro γ hγ
      obtain ⟨hw,hxy⟩:=mem_inter.mp hγ
      exact mem_inter.mpr ⟨hw,(mem_union.mp hxy).resolve_right (hnotY γ hw)⟩
    obtain ⟨δ,hδ,hδF⟩:=exists_mem_notMem_of_card_lt_card
      (hlarge.trans_le (card_le_card hsub))
    obtain ⟨hδw,hδx⟩:=mem_inter.mp hδ
    obtain ⟨θ,hθy⟩:=hcm.exists_free_right
    obtain ⟨c',hsw,hprotected⟩:=exists_full_palette_switching hG hcm q α θ δ hαA hyw
      hθy (mem_missing.mp hδx) (mem_missing.mp hδw)
    refine ⟨c',hsw.cm,hsw.leftRow,hsw.etaMissing,?_⟩
    intro a b γ hγ
    have hγα : γ≠α := by
      rcases mem_union.mp hγ with hγF|hγβ
      · exact hFα γ hγF
      · have he : γ=β := mem_singleton.mp hγβ
        exact he.trans_ne hβα
    have hγθ : γ≠θ := by
      rcases mem_union.mp hγ with hγF|hγβ
      · intro he
        subst γ
        exact (hcm.ab_facts hG).1 θ (mem_missing.mp (hF hγF)) hθy
      · have he : γ=β := mem_singleton.mp hγβ
        subst γ
        intro he
        exact hβy (he ▸ hθy)
    have hγδ : γ≠δ := by
      rcases mem_union.mp hγ with hγF|hγβ
      · intro he
        exact hδF (he ▸ hγF)
      · have he : γ=β := mem_singleton.mp hγβ
        subst γ
        intro he
        exact (mem_missing.mp hδx) u (he ▸ hxu)
    exact hprotected.otherEdges γ hγα hγθ hγδ a b

/-- The selected beta is present at y in the initial feasible state.
The auxiliary branch uses the actual four-vertex Kierstead theorem,
including the strict degree hypothesis at the root. -/
theorem selected_spine_colour_present_right (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α) (hα : c.IsFree y α)
    (hβα : β≠α) (hx : G.degree x<G.maxDegree)
    (halt : c.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      c.col z t=some β ∧ c.IsFree x δ ∧ c.IsFree t δ) : ¬c.IsFree y β := by
  intro hβy
  have hyz : y≠z := by
    intro he
    subst z
    rw [hcm.uncol] at hxz
    contradiction
  rcases halt with hβz|⟨t,δ,hzt,hδx,hδt⟩
  · exact (fan_bau hG hcm.symm hxz hα hyz).1 β hβy hβz
  · have hyt : y≠t := by
      intro he
      subst t
      exact hβy z (by rw [c.col_symm];exact hzt)
    have hxt : x≠t := by
      intro he
      subst t
      have heq : β=α := Option.some.inj (hzt.symm.trans ((c.col_symm z x).trans hxz))
      exact hβα heq
    have hK : IsK4 c y x z t α β := ⟨hcm.symm,hxz,hzt,hα,Or.inl hβy,hyz,hyt,hxt⟩
    exact hK.not_common_of_degree_b hG hx (Or.inr hδx) hδt

/-- The whole terminal implication after Claim 5.3, with the weaker
special-spine role B1. A protected finite set contains Xi and, when
needed, the auxiliary colour for beta at z. All recolourings and the
final hole shift are constructed inside the proof. -/
theorem no_certificate_with_flexible_special_spine (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α)
    (hxu : c.col x u=some β) (hβα : β≠α)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (Ξ F : Finset (Fin G.maxDegree))
    (hΞ : Ξ⊆missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u)
    (hsize : 1≤ε*((Ξ.card:ℝ)+1)) (hΞF : Ξ⊆F) (hF : F⊆missing c x)
    (hrole : c.IsFree y α ∨ α∈paletteA c ((1-ε)*(G.maxDegree:ℝ)) x y ∧
      ∃w,c.col y w=some α ∧ F.card<(missing c w∩(missing c x∪missing c y)).card)
    (halt : c.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      c.col z t=some β ∧ c.IsFree x δ ∧ c.IsFree t δ ∧ δ∈F ∧ δ∉Ξ) : False := by
  by_cases hβy : c.IsFree y β
  · exact no_terminal_palette_of_missing_spine hG hcm hxu hβy ε hε hx Ξ hΞ hsize
  have halt₀ : c.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      c.col z t=some β ∧ c.IsFree x δ ∧ c.IsFree t δ ∧ δ∉Ξ := by
    rcases halt with h|⟨t,δ,ht,hx,hw,_,hnot⟩
    · exact Or.inl h
    · exact Or.inr ⟨t,δ,ht,hx,hw,hnot⟩
  rcases hrole with hα|⟨hαA,w,hyw,hlarge⟩
  · exact no_certificate_at_feasible_neighbour hG hcm hxz hα hxu hβα ε hε hx Ξ hΞ hsize halt₀
  · obtain ⟨c',hcm',hrow,hα',hclasses⟩:=exists_special_colour_missing_with_protection
      hG hcm ((1-ε)*(G.maxDegree:ℝ)) hαA hyw hxu hβα hβy F hF hlarge
    have hxz' : c'.col x z=some α := by rw [hrow];exact hxz
    have hxu' : c'.col x u=some β := by rw [hrow];exact hxu
    have hfree : ∀γ,c'.IsFree x γ↔c.IsFree x γ := by
      intro γ
      simp only [IsFree,hrow]
    have hΞ' : Ξ⊆missing c' x∩badColours c' ((1-ε)*(G.maxDegree:ℝ)) u := by
      intro γ hγ
      obtain ⟨hγx,hγbad⟩:=mem_inter.mp (hΞ hγ)
      have hγF : γ∈F∪{β} := mem_union_left _ (hΞF hγ)
      refine mem_inter.mpr ⟨mem_missing.mpr ((hfree γ).mpr (mem_missing.mp hγx)),?_⟩
      apply (mem_badColours c' _ u γ).mpr
      rcases (mem_badColours c _ u γ).mp hγbad with hf|⟨v,hv,hd⟩
      · exact Or.inl (fun v hv => hf v ((hclasses u v γ hγF).mp hv))
      · exact Or.inr ⟨v,(hclasses u v γ hγF).mpr hv,hd⟩
    have hβF : β∈F∪{β} := mem_union_right _ (mem_singleton_self _)
    have halt' : c'.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
        c'.col z t=some β ∧ c'.IsFree x δ ∧ c'.IsFree t δ ∧ δ∉Ξ := by
      rcases halt with hβ|⟨t,δ,hzt,hδx,hδt,hδF,hδΞ⟩
      · exact Or.inl (fun v hv => hβ v ((hclasses z v β hβF).mp hv))
      · have hδF' : δ∈F∪{β} := mem_union_left _ hδF
        exact Or.inr ⟨t,δ,(hclasses z t β hβF).mpr hzt,(hfree δ).mpr hδx,
          fun v hv => hδt v ((hclasses t v δ hδF').mp hv),hδΞ⟩
    exact no_certificate_at_feasible_neighbour hG hcm' hxz' hα' hxu' hβα ε hε hx Ξ hΞ' hsize halt'

/-- The final contradiction directly in the root-only B1 interface used
by secondary normalization and finite palette progress. The protected
auxiliary set is constructed, rather than left to the caller. -/
theorem no_large_root_spine_certificate (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y z u : V} {α β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α)
    (hxu : c.col x u=some β) (hβα : β≠α)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (Ξ : Finset (Fin G.maxDegree))
    (hΞ : Ξ⊆missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u)
    (hsize : 1≤ε*((Ξ.card:ℝ)+1))
    (hrole : CaoChenSecondarySpineNormalization.SpineRole c ((1-ε)*(G.maxDegree:ℝ))
      x y α (Ξ.card+1))
    (halt : c.IsFree z β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      c.col z t=some β ∧ c.IsFree x δ ∧ c.IsFree t δ ∧ δ∉Ξ) : False := by
  have hΞx : Ξ⊆missing c x := fun _ h => (mem_inter.mp (hΞ h)).1
  have hroleF (F : Finset (Fin G.maxDegree)) (hF : F.card≤Ξ.card+1) :
      c.IsFree y α ∨ α∈paletteA c ((1-ε)*(G.maxDegree:ℝ)) x y ∧
        ∃w,c.col y w=some α ∧ F.card<(missing c w∩(missing c x∪missing c y)).card := by
    rcases hrole with hα|⟨w,hyw,hwlow,hwlarge⟩
    · exact Or.inl hα
    · right
      have hαA : α∈paletteA c ((1-ε)*(G.maxDegree:ℝ)) x y :=
        (mem_paletteA c _ x y α).mpr
          ⟨(presentColours_iff_coloured c x α).mpr ⟨z,hxz⟩,w,hyw,hwlow⟩
      refine ⟨hαA,w,hyw,?_⟩
      have hsub : missing c w∩missing c x⊆missing c w∩(missing c x∪missing c y) :=
        fun _ h => mem_inter.mpr ⟨(mem_inter.mp h).1,mem_union_left _ (mem_inter.mp h).2⟩
      exact (hF.trans_lt hwlarge).trans_le (card_le_card hsub)
  rcases halt with hβ|⟨t,δ,hzt,hδx,hδt,hδΞ⟩
  · exact no_certificate_with_flexible_special_spine hG hcm hxz hxu hβα ε hε hx Ξ Ξ
      hΞ hsize subset_rfl hΞx (hroleF Ξ (by omega)) (Or.inl hβ)
  · have hFx : insert δ Ξ⊆missing c x := by
      intro γ hγ
      rcases mem_insert.mp hγ with rfl|hγ
      · exact mem_missing.mpr hδx
      · exact hΞx hγ
    exact no_certificate_with_flexible_special_spine hG hcm hxz hxu hβα ε hε hx Ξ (insert δ Ξ)
      hΞ hsize (subset_insert _ _) hFx (hroleF _ (card_insert_le _ _))
      (Or.inr ⟨t,δ,hzt,hδx,hδt,mem_insert_self _ _,hδΞ⟩)

end OverfullWork.CaoChenTerminalAssembly
