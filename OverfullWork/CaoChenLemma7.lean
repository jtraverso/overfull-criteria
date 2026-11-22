module

public import OverfullWork.CaoChenLemma7Configuration
public import OverfullWork.CaoChenInitialFiniteState
public import OverfullWork.CaoChenIterationTerminal

@[expose] public section


/-! # Cao--Chen Lemma 7 from actual finite palette iteration

The finite configuration constructs Claim 5.2's prepared spine. Root-only
normalization constructs the initial finite state, the proved effective
steps reach a terminal state, and the fan certificate is contradictory.
All numerical requirements are paid by epsilon^2*Delta >= 1000*(k+1)^4.
-/
namespace OverfullWork.CaoChenLemma7
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenUniformPaletteBudgets
open scoped Classical
universe u
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 6000000

/-- The full selected-family form of Lemma 7. No prepared spine,
normalized palette, progress step or terminal certificate is assumed. -/
theorem no_configuration (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y z : V} {α : Fin G.maxDegree}
    (hcm₀ : IsColMinus c₀ x y) (hxz : c₀.col x z=some α) (hα : c₀.IsFree y α)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (B : Finset (Fin G.maxDegree)) (U : Fin G.maxDegree → V)
    (D : Fin G.maxDegree → Finset (Fin G.maxDegree))
    (hBcard : B.card=k+1)
    (hB : ∀β∈B,β∈badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) z)
    (hBne : ∀β∈B,β≠α) (hU : ∀β∈B,c₀.col x (U β)=some β)
    (hD : ∀β∈B,(D β).card=3*k ∧ β∉D β ∧
      D β⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) (U β)∩
        paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y) : False := by
  obtain ⟨β,hβ,c₁,δ,hp⟩:=CaoChenLemma7Configuration.exists_prepared_spine
    hG c₀ hcm₀ hxz hα ε hε hεone k hx hscale hlarge B U D hBcard hB hBne hU hD
  obtain ⟨c₂,I,F,hi⟩:=CaoChenInitialFiniteState.exists_initial_finite_state
    hG c₁ hp.cm hp.specialEdge hp.specialMissing hp.spine hp.beta_ne (D β) k hk
    ε hε hεone hx hp.selected hp.card hp.betaNotSelected hp.auxiliaryRoot
    hp.auxiliaryNotSelected hp.alternative hscale hlarge
  have hIF : I⊆F := by rw [hi.protectedFamily];exact subset_union_left
  have hβF : β∈F := by rw [hi.protectedFamily];simp
  obtain ⟨d,T,hs⟩:=CaoChenFiniteIteration.exists_terminal_state hG ε hε hεone hi.state
    hIF hi.protectedCard hi.protectedOverlapCard hi.familyPresent hβF hi.betaNotSelected
    hi.betaSpine hi.specialSpine hx hscale hlarge
  exact CaoChenIterationTerminal.no_terminal_finite_state hG ε hε hx hscale
    (hBne β hβ) hi hs

/-- The offending colours are defined from actual root edges and actual
bad/S palettes. The definition does not choose an endpoint function. -/
noncomputable def offendingColours (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y z : V) (α : Fin G.maxDegree) (k : ℕ) : Finset (Fin G.maxDegree) :=
  (((badColours c q z∩presentColours c x)\{α}).filter fun β =>
    ∃u,c.col x u=some β ∧ 3*k≤((badColours c q u∩paletteS c q x y)\{β}).card)

/-- Cao--Chen Lemma 7 as a reusable cardinal bound, with an explicit
uniform cutoff. The selected 3k-colour subsets are constructed in the proof. -/
theorem offendingColours_card_le (hG : IsClassTwo G)
    (c : PEC G (Fin G.maxDegree)) {x y z : V} {α : Fin G.maxDegree}
    (hcm : IsColMinus c x y) (hxz : c.col x z=some α) (hα : c.IsFree y α)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ) (hk : 1≤k)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ)) :
    (offendingColours c ((1-ε)*(G.maxDegree:ℝ)) x y z α k).card≤k := by
  by_contra hn
  let q:=(1-ε)*(G.maxDegree:ℝ)
  change ¬(offendingColours c q x y z α k).card≤k at hn
  obtain ⟨B,hBsub,hBcard⟩:=exists_subset_card_eq
    (show k+1≤(offendingColours c q x y z α k).card by omega)
  have hspec (β : Fin G.maxDegree) (hβ : β∈B) :
      β∈badColours c q z ∧ β≠α ∧ ∃u,c.col x u=some β ∧
        3*k≤((badColours c q u∩paletteS c q x y)\{β}).card := by
    obtain ⟨hbase,hu⟩:=mem_filter.mp (hBsub hβ)
    obtain ⟨hbad,hne⟩:=mem_sdiff.mp hbase
    exact ⟨(mem_inter.mp hbad).1,by simpa only [mem_singleton] using hne,hu⟩
  let U : Fin G.maxDegree → V:=fun β => if hβ : β∈B then Classical.choose (hspec β hβ).2.2 else x
  have hUspec (β : Fin G.maxDegree) (hβ : β∈B) : c.col x (U β)=some β ∧
      3*k≤((badColours c q (U β)∩paletteS c q x y)\{β}).card := by
    simpa only [U,dif_pos hβ] using Classical.choose_spec (hspec β hβ).2.2
  have hDexists (β : Fin G.maxDegree) (hβ : β∈B) :
      ∃D : Finset (Fin G.maxDegree),D⊆(badColours c q (U β)∩paletteS c q x y)\{β} ∧ D.card=3*k :=
    exists_subset_card_eq (hUspec β hβ).2
  let D : Fin G.maxDegree → Finset (Fin G.maxDegree):=
    fun β => if hβ : β∈B then Classical.choose (hDexists β hβ) else ∅
  have hDspec (β : Fin G.maxDegree) (hβ : β∈B) :
      D β⊆(badColours c q (U β)∩paletteS c q x y)\{β} ∧ (D β).card=3*k := by
    simpa only [D,dif_pos hβ] using Classical.choose_spec (hDexists β hβ)
  apply no_configuration hG c hcm hxz hα ε hε hεone k hk hx hscale hlarge
    B U D hBcard (fun β hβ => (hspec β hβ).1) (fun β hβ => (hspec β hβ).2.1)
    (fun β hβ => (hUspec β hβ).1)
  intro β hβ
  have hd:=hDspec β hβ
  refine ⟨hd.2,?_,?_⟩
  · intro h
    exact (mem_sdiff.mp (hd.1 h)).2 (mem_singleton_self _)
  · exact fun _ h => (mem_sdiff.mp (hd.1 h)).1

/-- The reciprocal integer and the maximum-degree threshold are chosen
before the vertex type and graph. This is an unconditional eventual
Lemma-7 bound, not an assumed normalization or iteration interface. -/
theorem eventual_offending_bound (ε : ℝ) (hε : 0<ε) (hεone : ε<1) :
    ∃k : ℕ,1≤k ∧ ∃N : ℕ,
      ∀{W : Type u} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj],
        N≤G.maxDegree → IsClassTwo G →
        ∀(c : PEC G (Fin G.maxDegree)) (x y z : W) (α : Fin G.maxDegree),
          IsColMinus c x y → c.col x z=some α → c.IsFree y α →
          (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ) →
          (offendingColours c ((1-ε)*(G.maxDegree:ℝ)) x y z α k).card≤k := by
  obtain ⟨k,hk⟩:=exists_nat_gt (max 1 (1/ε))
  have hkR : (1:ℝ)<(k:ℝ):=lt_of_le_of_lt (le_max_left _ _) hk
  have hkNat : 1≤k := by exact_mod_cast hkR.le
  have hscale : 1≤ε*((k+1:ℕ):ℝ) := by
    have hh : 1/ε<(k:ℝ):=lt_of_le_of_lt (le_max_right _ _) hk
    have hm:=(div_lt_iff₀ hε).mp hh
    push_cast
    nlinarith only [hm,hε]
  have heps : 0<ε^2:=sq_pos_of_pos hε
  obtain ⟨N,hN⟩:=exists_nat_ge ((cutoff k:ℝ)/ε^2)
  refine ⟨k,hkNat,N,?_⟩
  intro W _ _ G _ hdegree hG c x y z α hcm hxz hα hx
  have hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    have hb:=(div_le_iff₀ heps).mp hN
    have hd : (N:ℝ)≤(G.maxDegree:ℝ):=by exact_mod_cast hdegree
    have hm:=mul_le_mul_of_nonneg_left hd heps.le
    nlinarith only [hb,hm]
  exact offendingColours_card_le hG c hcm hxz hα ε hε hεone k hkNat hx hscale hlarge

end OverfullWork.CaoChenLemma7
