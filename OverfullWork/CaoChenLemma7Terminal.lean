module

public import OverfullWork.CaoChenPaletteCounting
public import OverfullWork.CaoChenProtectedPaletteSwitching

@[expose] public section


/-! # The actual terminal contradiction in Cao--Chen Lemma 7

Move the uncoloured root edge to a spine whose colour is missing at its
opposite endpoint. Every root-missing bad colour then becomes a direct
low multifan leaf, so the already proved elementary fan count applies.
The alternative in (5.1) is converted by an actual protected switching.
No general broom theorem or charge estimate is assumed.
-/
namespace OverfullWork.CaoChenLemma7Terminal
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteCounting CaoChenDischarging
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

/-- The low-fan count after an actual shift of the uncoloured edge. -/
theorem missing_bad_spine_bound (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some β) (hβ : c.IsFree y β)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ)) :
    ε*(((missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u).card:ℝ)+1)<1 := by
  let q := (1-ε)*(G.maxDegree:ℝ)
  have hux : u≠x := (c.col_adj hxu).ne.symm
  have hyu : y≠u := by
    intro he
    subst u
    rw [hcm.uncol] at hxu
    contradiction
  have hfan := (fan_bau hG hcm.symm hxu hβ hyu).2
  obtain ⟨ψ,hψ,_,hoff,hfreeX,_,_⟩ := exists_shift hcm.symm hxu hβ hyu
  have hsub : missing c x∩badColours c q u⊆lowColours ψ q u∩missing ψ x := by
    intro γ hγ
    obtain ⟨hγx,hγbad⟩:=mem_inter.mp hγ
    have hfree := mem_missing.mp hγx
    have hγnot : ¬c.IsFree u γ:=hfan γ hfree
    obtain ⟨t,hut,ht⟩ := ((mem_badColours c q u γ).mp hγbad).resolve_left hγnot
    have htx : t≠x := by
      intro he
      subst t
      exact hfree u (by rw [c.col_symm];exact hut)
    have hψut : ψ.col u t=some γ := by
      rw [hoff u t (by tauto) (by tauto)]
      exact hut
    exact mem_inter.mpr ⟨(mem_lowColours ψ q u γ).mpr ⟨t,hψut,ht⟩,
      mem_missing.mpr ((hfreeX γ).mpr hfree)⟩
  have hc:=card_le_card hsub
  have he := lowStarLeaves_card_eq_low_inter_missing (c:=ψ) (x:=x) (y:=u) q
  rw [←he] at hc
  have hbound := lowStarLeaves_count hG hψ.symm ε hε hx
  have hcR : ((missing c x∩badColours c q u).card:ℝ)≤
      ((lowStarLeaves ψ x u q).card:ℝ) := by exact_mod_cast hc
  change ε*(((missing c x∩badColours c q u).card:ℝ)+1)<1
  change ε*(((lowStarLeaves ψ x u q).card:ℝ)+1)<1 at hbound
  nlinarith only [hcR,hbound,hε]

/-- A concrete integer cap, with the exact reciprocal condition displayed. -/
theorem missing_bad_spine_card_lt (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some β) (hβ : c.IsFree y β)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (k : ℕ) (hk : 1≤ε*((k:ℝ)+1)) :
    (missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u).card<k := by
  have hb:=missing_bad_spine_bound hG hcm hxu hβ ε hε hx
  by_contra hn
  have he : (k:ℝ)≤((missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u).card:ℝ) := by
    exact_mod_cast (show k≤(missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u).card by omega)
  nlinarith only [he,hb,hk,hε]

/-- The terminal palette can be a chosen subset, as in equation (5.1). -/
theorem no_terminal_palette_of_missing_spine (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some β) (hβ : c.IsFree y β)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (Ξ : Finset (Fin G.maxDegree))
    (hΞ : Ξ⊆missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u)
    (hsize : 1≤ε*((Ξ.card:ℝ)+1)) : False := by
  have hb:=missing_bad_spine_card_lt hG hcm hxu hβ ε hε hx Ξ.card hsize
  exact (not_lt_of_ge (card_le_card hΞ)) hb

/-- The complete terminal alternative of (5.1): either beta is already
missing opposite the root, or a supplied common missing colour outside
Xi permits the actual protected switching that makes it missing there. -/
theorem no_terminal_palette_certificate (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V} {β : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxu : c.col x u=some β)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (Ξ : Finset (Fin G.maxDegree))
    (hΞ : Ξ⊆missing c x∩badColours c ((1-ε)*(G.maxDegree:ℝ)) u)
    (hsize : 1≤ε*((Ξ.card:ℝ)+1))
    (halt : c.IsFree y β ∨ ∃t : V,∃δ : Fin G.maxDegree,
      c.col y t=some β ∧ c.IsFree x δ ∧ c.IsFree t δ ∧ δ∉Ξ) : False := by
  rcases halt with hβ|⟨t,δ,hyt,hδx,hδt,hδΞ⟩
  · exact no_terminal_palette_of_missing_spine hG hcm hxu hβ ε hε hx Ξ hΞ hsize
  · obtain ⟨θ,hθ⟩:=hcm.exists_free_right
    obtain ⟨c',hsw⟩:=exists_protected_palette_switching hG hcm β θ δ hyt hθ hδx hδt
    have hxu' : c'.col x u=some β := by rw [hsw.leftRow];exact hxu
    have hΞ' : Ξ⊆missing c' x∩badColours c' ((1-ε)*(G.maxDegree:ℝ)) u := by
      intro γ hγ
      obtain ⟨hγx,hγbad⟩:=mem_inter.mp (hΞ hγ)
      have hfree := mem_missing.mp hγx
      have hγβ : γ≠β:=by intro he;exact hfree u (he ▸ hxu)
      have hγθ : γ≠θ:=by intro he;exact (hcm.ab_facts hG).1 γ hfree (he ▸ hθ)
      have hγδ : γ≠δ:=by intro he;exact hδΞ (he ▸ hγ)
      have hcol := hsw.otherEdges γ hγβ hγθ hγδ
      have hfree' : c'.IsFree x γ := by
        intro w hw
        exact hfree w (by rw [←hsw.leftRow w];exact hw)
      refine mem_inter.mpr ⟨mem_missing.mpr hfree',?_⟩
      apply (mem_badColours c' ((1-ε)*(G.maxDegree:ℝ)) u γ).mpr
      rcases (mem_badColours c ((1-ε)*(G.maxDegree:ℝ)) u γ).mp hγbad with hf|⟨w,hw,hd⟩
      · left
        intro w hw
        exact hf w ((hcol u w).mp hw)
      · exact Or.inr ⟨w,(hcol u w).mpr hw,hd⟩
    exact no_terminal_palette_of_missing_spine hG hsw.cm hxu' hsw.etaMissing ε hε hx Ξ hΞ' hsize

end OverfullWork.CaoChenLemma7Terminal
