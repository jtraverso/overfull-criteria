module

public import OverfullWork.CaoChenUniformPaletteBudgets
public import OverfullWork.CaoChenFinitePaletteProgress

@[expose] public section


/-! # Preparing an actual selected spine from Lemma 7's finite configuration

Claim 5.2 is applied before root-only normalization. Its protected palette
is the union of the selected Ti, so the chosen auxiliary is outside the
chosen Ti. In the already-missing branch the auxiliary is chosen directly
from the root palette. No prepared colouring is assumed.
-/
namespace OverfullWork.CaoChenLemma7Configuration
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

structure Prepared (c₀ c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y z u : V) (α β δ : Fin G.maxDegree)
    (T : Finset (Fin G.maxDegree)) (k : ℕ) : Prop where
  cm : IsColMinus c x y
  rootRow : ∀v,c.col x v=c₀.col x v
  specialEdge : c.col x z=some α
  specialMissing : c.IsFree y α
  spine : c.col x u=some β
  beta_ne : β≠α
  selected : T⊆badColours c q u∩paletteS c q x y
  card : T.card=3*k
  betaNotSelected : β∉T
  auxiliaryRoot : c.IsFree x δ
  auxiliaryNotSelected : δ∉T
  alternative : c.IsFree z β ∨ ∃t,c.col z t=some β ∧ c.IsFree t δ

/-- A family of k+1 actual bad colours and selected 3k-colour palettes
constructs a prepared spine. The only size hypothesis is the uniform
maximum-degree cutoff, in addition to the finite input configuration. -/
theorem exists_prepared_spine (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y z : V} {α : Fin G.maxDegree}
    (hcm₀ : IsColMinus c₀ x y) (hxz : c₀.col x z=some α) (hα : c₀.IsFree y α)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (k : ℕ)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hk : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ))
    (B : Finset (Fin G.maxDegree)) (U : Fin G.maxDegree → V)
    (D : Fin G.maxDegree → Finset (Fin G.maxDegree))
    (hBcard : B.card=k+1)
    (hB : ∀β∈B,β∈badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) z)
    (hBne : ∀β∈B,β≠α) (hU : ∀β∈B,c₀.col x (U β)=some β)
    (hD : ∀β∈B,(D β).card=3*k ∧ β∉D β ∧
      D β⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) (U β)∩
        paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y) :
    ∃β∈B,∃c : PEC G (Fin G.maxDegree),∃δ : Fin G.maxDegree,
      Prepared c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y z (U β) α β δ (D β) k := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let C:=B.biUnion D
  have hCcard : C.card≤3*k*(k+1) := by
    calc
      C.card≤∑β∈B,(D β).card:=card_biUnion_le
      _=∑_β∈B,3*k:=sum_congr rfl (fun β hβ => (hD β hβ).1)
      _=3*k*(k+1):=by simp only [sum_const,Nat.nsmul_eq_mul,hBcard];ring
  have hbud:=claim52_budgets k C.card hCcard
  have hroot:=missing_root_gt_cutoff hcm₀ ε hε hεone k hx hlarge
  have hth : (C.card:ℝ)+((B.card-1:ℕ):ℝ)*
      ((B.card+(0+3)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    rw [hBcard,Nat.add_sub_cancel]
    have hh : ((C.card+k*(k+1+3*C.card+1):ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) :=
      (by exact_mod_cast hbud.1 : ((C.card+k*(k+1+3*C.card+1):ℕ):ℝ)≤(cutoff k:ℝ)).trans hlarge
    simpa only [Nat.cast_add,Nat.cast_mul,zero_add] using hh
  have hb : B.card+(0+3)*C.card+B.card*C.card<(missing c₀ x).card := by
    rw [hBcard]
    simpa only [zero_add] using hbud.2.trans_lt hroot
  obtain ⟨c,hs⟩:=CaoChenClaim52.exists_claim52_colouring hG c₀ hcm₀ hxz hα B C 0
    ε hε hεone hx hB (by simpa only [hBcard] using hk) hth hb
  obtain ⟨β,hβ,halt⟩:=hs.alternative
  have hTsub : D β⊆C:=fun γ hγ => mem_biUnion.mpr ⟨β,hβ,hγ⟩
  have hclasses : ∀a b γ,γ∈D β → (c.col a b=some γ↔c₀.col a b=some γ) :=
    fun a b γ hγ => hs.protectedColours a b γ (mem_union_left _ (hTsub hγ))
  have hbad (v : V) (γ : Fin G.maxDegree) (hγ : γ∈D β) :
      γ∈badColours c q v ↔ γ∈badColours c₀ q v := by
    have hf : c.IsFree v γ↔c₀.IsFree v γ := by
      constructor
      · intro hf w hw
        exact hf w ((hclasses v w γ hγ).mpr hw)
      · intro hf w hw
        exact hf w ((hclasses v w γ hγ).mp hw)
    simp only [mem_badColours,hf]
    simp_rw [hclasses _ _ γ hγ]
  have hfree : ∀γ,c.IsFree x γ↔c₀.IsFree x γ := by
    intro γ
    simp only [IsFree,hs.rootRow]
  have hS (γ : Fin G.maxDegree) (hγ : γ∈D β) :
      γ∈paletteS c q x y ↔ γ∈paletteS c₀ q x y := by
    simp only [mem_paletteS_iff_free_or_bad,hfree γ,hbad y γ hγ]
  have hselected : D β⊆badColours c q (U β)∩paletteS c q x y := by
    intro γ hγ
    obtain ⟨ha,hb⟩:=mem_inter.mp ((hD β hβ).2.2 hγ)
    exact mem_inter.mpr ⟨(hbad _ γ hγ).mpr ha,(hS γ hγ).mpr hb⟩
  have hspine : c.col x (U β)=some β := by rw [hs.rootRow];exact hU β hβ
  have hcommon (δ : Fin G.maxDegree) (hd : c.IsFree x δ) (hnot : δ∉D β)
      (halt' : c.IsFree z β ∨ ∃t,c.col z t=some β ∧ c.IsFree t δ) :
      Prepared c₀ c q x y z (U β) α β δ (D β) k :=
    ⟨hs.cm,hs.rootRow,hs.spine,hs.spineMissing,hspine,hBne β hβ,hselected,
      (hD β hβ).1,(hD β hβ).2.1,hd,hnot,halt'⟩
  refine ⟨β,hβ,c,?_⟩
  rcases halt with hfreeβ|⟨t,δ,hzt,hδx,hδt,hδC⟩
  · have hroot' := missing_root_gt_cutoff hs.cm ε hε hεone k hx hlarge
    have hsmall : 3*k≤cutoff k := by
      dsimp [cutoff]
      nlinarith only [Nat.zero_le k,Nat.zero_le (k^2),Nat.zero_le (k^3),Nat.zero_le (k^4)]
    have hbudget : (∅ : Finset (Fin G.maxDegree)).card+(D β).card<(missing c x).card := by
      simp only [card_empty,zero_add,(hD β hβ).1]
      exact hsmall.trans_lt hroot'
    obtain ⟨δ,hd,_,hnot⟩:=CaoChenFinitePaletteProgress.exists_root_auxiliary c x ∅ (D β) hbudget
    exact ⟨δ,hcommon δ hd hnot (Or.inl hfreeβ)⟩
  · exact ⟨δ,hcommon δ hδx (fun h => hδC (hTsub h)) (Or.inr ⟨t,hzt,hδt⟩)⟩

end OverfullWork.CaoChenLemma7Configuration
