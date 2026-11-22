module

public import OverfullWork.CaoChenLemma7

@[expose] public section


/-! # Rerooting the common-palette configuration in Cao--Chen Lemma 8

A selected colour missing at y permits an actual shift of the deleted
edge. All common-palette colours are different from that colour, so their
entire edge classes survive. The common palette is then inside the NEW S
palette, and the already proved full Lemma 7 rules out the configuration.
-/
namespace OverfullWork.CaoChenLemma8Rerooting
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- One actual shifted colouring exports all of the required reroot data. -/
theorem exists_shift_with_reroot_data
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {η : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some η) (hη : c.IsFree y η) :
    ∃ψ : PEC G (Fin G.maxDegree),IsColMinus ψ x u ∧ ψ.col x y=some η ∧ ψ.IsFree u η ∧
      (∀γ,ψ.IsFree x γ↔c.IsFree x γ) ∧
      ∀a b γ,γ≠η → (ψ.col a b=some γ↔c.col a b=some γ) := by
  have hyu : y≠u := by
    intro he
    subst u
    rw [hcm.uncol] at hxu
    contradiction
  obtain ⟨ψ,hψ,hyx,hoff,hfx,hηu,_⟩:=exists_shift hcm.symm hxu hη hyu
  refine ⟨ψ,hψ.symm,by rw [ψ.col_symm];exact hyx,hηu,hfx,?_⟩
  intro a b γ hγη
  by_cases hxy : (a=y ∧ b=x) ∨ (a=x ∧ b=y)
  · have hold : c.col a b=none := by
      rcases hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · rw [c.col_symm,hcm.uncol]
      · exact hcm.uncol
    have hnew : ψ.col a b=some η := by
      rcases hxy with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact hyx
      · rw [ψ.col_symm];exact hyx
    rw [hold,hnew]
    simp [Ne.symm hγη]
  · by_cases hxu' : (a=x ∧ b=u) ∨ (a=u ∧ b=x)
    · have hold : c.col a b=some η := by
        rcases hxu' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact hxu
        · rw [c.col_symm];exact hxu
      have hnew : ψ.col a b=none := by
        rcases hxu' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · rw [ψ.col_symm];exact hψ.uncol
        · exact hψ.uncol
      rw [hold,hnew]
      simp [Ne.symm hγη]
    · rw [hoff a b hxy hxu']

/-- The final rerooting implication in Lemma 8. Common colours and
constant 3k-subsets are constructed from the actual supplied palette. -/
theorem no_large_common_palette_with_missing_right (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y : V} (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (S : Finset (Fin G.maxDegree)) (U : Fin G.maxDegree → V) (F : Finset (Fin G.maxDegree))
    (hScard : S.card=k+2) (hU : ∀η∈S,c.col x (U η)=some η)
    (hS : S⊆paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y∩presentColours c x)
    (hFcard : 3*k≤F.card)
    (hCommon : ∀η∈S,F⊆badColours c ((1-ε)*(G.maxDegree:ℝ)) (U η)\{η})
    (hMissing : ∃η∈S,c.IsFree y η) : False := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  obtain ⟨η,hηS,hηy⟩:=hMissing
  obtain ⟨ψ,hψ,hxy,hηu,_hrootFree,hclasses⟩:=exists_shift_with_reroot_data hcm (hU η hηS) hηy
  have hFη : η∉F := by
    intro hηF
    exact (mem_sdiff.mp (hCommon η hηS hηF)).2 (mem_singleton_self η)
  have hFne : ∀γ∈F,γ≠η:=fun γ hγ he => hFη (he ▸ hγ)
  have hbad : ∀v γ,γ≠η → (γ∈badColours ψ q v↔γ∈badColours c q v) := by
    intro v γ hγη
    simp only [mem_badColours,IsFree,ne_eq]
    simp_rw [hclasses _ _ γ hγη]
  let B:=S.erase η
  have hBcard : B.card=k+1 := by
    have he:=card_erase_add_one hηS
    change B.card+1=S.card at he
    omega
  have hBsub : B⊆S:=erase_subset η S
  have hBne : ∀β∈B,β≠η:=fun β hβ => (mem_erase.mp hβ).1
  have hBbad : ∀β∈B,β∈badColours ψ q y := by
    intro β hβ
    have hβS : β∈paletteS c q x y:=(mem_inter.mp (hS (hBsub hβ))).1
    have hβP : β∈presentColours c x:=(mem_inter.mp (hS (hBsub hβ))).2
    have hbad₀ : β∈badColours c q y :=
      ((mem_paletteS_iff_free_or_bad c q x y β).mp hβS).resolve_left
        ((mem_presentColours c x β).mp hβP)
    exact (hbad y β (hBne β hβ)).mpr hbad₀
  obtain ⟨D,hDF,hDcard⟩:=exists_subset_card_eq hFcard
  have hDS : D⊆paletteS ψ q x (U η) := by
    intro γ hγ
    have hbad₀ : γ∈badColours c q (U η):=(mem_sdiff.mp (hCommon η hηS (hDF hγ))).1
    exact (mem_paletteS_iff_free_or_bad ψ q x (U η) γ).mpr
      (Or.inr ((hbad (U η) γ (hFne γ (hDF hγ))).mpr hbad₀))
  apply CaoChenLemma7.no_configuration hG ψ hψ hxy hηu ε hε hεone k hk hx hscale hlarge
    B U (fun _ => D) hBcard hBbad hBne
  · intro β hβ
    exact (hclasses x (U β) β (hBne β hβ)).mpr (hU β (hBsub hβ))
  · intro β hβ
    refine ⟨hDcard,?_,?_⟩
    · intro hβD
      exact (mem_sdiff.mp (hCommon β (hBsub hβ) (hDF hβD))).2 (mem_singleton_self β)
    · intro γ hγ
      have hbad₀ : γ∈badColours c q (U β):=(mem_sdiff.mp (hCommon β (hBsub hβ) (hDF hγ))).1
      exact mem_inter.mpr ⟨(hbad (U β) γ (hFne γ (hDF hγ))).mpr hbad₀,hDS hγ⟩

end OverfullWork.CaoChenLemma8Rerooting
