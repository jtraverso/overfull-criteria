module

public import OverfullWork.CaoChenFiniteIteration
public import OverfullWork.CaoChenUniformPaletteBudgets

@[expose] public section


/-! # A constructed initial state for finite palette progress

Start from a feasible special spine and a prepared beta alternative.
Actual root-only normalization constructs the colouring, the finite
exceptional set I, and the protected family I union {beta,delta0}.
One uniform maximum-degree cutoff pays every initial finite budget.
-/
namespace OverfullWork.CaoChenInitialFiniteState
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenSecondarySpineNormalization CaoChenRootPaletteNormalization
open CaoChenUniformPaletteBudgets
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

/-- All finite initial data come from the same actual output colouring. -/
structure InitialData (c₀ c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y z u : V)
    (α β δ₀ : Fin G.maxDegree) (T I F : Finset (Fin G.maxDegree)) (k : ℕ) : Prop where
  normalized : RootNormalized c₀ c q x y (insert α T) {β,δ₀} (4*k+5) (k+1)
  exceptional : I=smallRootOverlapColours c q x y (insert α T) (4*k+5)
  protectedFamily : F=I∪{β,δ₀}
  exceptionalCard : I.card≤k
  protectedCard : F.card≤k+2
  protectedOverlap : T∩F⊆I
  protectedOverlapCard : (T∩F).card≤k
  specialNotExceptional : α∉I
  selected : T⊆badColours c q u∩paletteS c q x y
  specialSpine : c.col x z=some α
  betaSpine : c.col x u=some β
  specialMissing : c.IsFree y α
  betaPresent : β∈presentColours c y
  auxiliaryMissing : c.IsFree x δ₀
  familyPresent : ∀γ∈F,γ∈presentColours c y
  betaNotSelected : β∉T
  auxiliaryNotSelected : δ₀∉T
  alternative : c.IsFree z β ∨ ∃t,c.col z t=some β ∧ c.IsFree t δ₀
  state : CaoChenFiniteIteration.State c c q x y u α T T I F k (2*k+5) 0

/-- Root-only normalization constructs the initial state and the actual
exceptional/protected sets. The caller supplies only the prepared graph
configuration and the uniform numerical cutoff. -/
theorem exists_initial_finite_state (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y z u : V} {α β δ₀ : Fin G.maxDegree}
    (hcm₀ : IsColMinus c₀ x y) (hxz : c₀.col x z=some α) (hα : c₀.IsFree y α)
    (hxu : c₀.col x u=some β) (hβα : β≠α)
    (T : Finset (Fin G.maxDegree)) (k : ℕ) (_hk : 1≤k)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hT : T⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) u∩paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y)
    (hcard : T.card=3*k) (hβT : β∉T) (hδ₀x : c₀.IsFree x δ₀) (hδ₀T : δ₀∉T)
    (halt : c₀.IsFree z β ∨ ∃t,c₀.col z t=some β ∧ c₀.IsFree t δ₀)
    (hscale : 1≤ε*((k+1:ℕ):ℝ))
    (hlarge : (cutoff k:ℝ)≤ε^2*(G.maxDegree:ℝ)) :
    ∃c : PEC G (Fin G.maxDegree),∃I F : Finset (Fin G.maxDegree),
      InitialData c₀ c ((1-ε)*(G.maxDegree:ℝ)) x y z u α β δ₀ T I F k := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let C:=insert α T
  let E : Finset (Fin G.maxDegree):={β,δ₀}
  have hCcard : C.card≤3*k+1 := by
    have hi:=card_insert_le α T
    change C.card≤T.card+1 at hi
    omega
  have hEcard : E.card≤2:=card_le_two
  have hbud:=initial_budgets k C.card E.card hCcard hEcard
  have hmissing:=missing_root_gt_cutoff hcm₀ ε hε hεone k hx hlarge
  have hthreshold : ((4*k+5:ℕ):ℝ)+((C.card-1:ℕ):ℝ)*
      ((E.card+((4*k+5)+3)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    have hnum : 4*k+5+(C.card-1)*(E.card+((4*k+5)+3)*C.card+1)≤cutoff k := by
      convert hbud.1 using 1
    have hnumR : ((4*k+5:ℕ):ℝ)+((C.card-1:ℕ):ℝ)*
        ((E.card+((4*k+5)+3)*C.card+1:ℕ):ℝ)≤(cutoff k:ℝ) := by exact_mod_cast hnum
    exact hnumR.trans hlarge
  have hbudget : E.card+((4*k+5)+3)*C.card+C.card*(4*k+5)<(missing c₀ x).card := by
    have hnum : E.card+((4*k+5)+3)*C.card+C.card*(4*k+5)≤cutoff k := by
      convert hbud.2 using 1
    exact hnum.trans_lt hmissing
  obtain ⟨c,hnorm,hIcard⟩:=exists_root_normalized_palette_card_le hG c₀ hcm₀ q C E (4*k+5) k
    ε hε hεone rfl hx hscale hthreshold hbudget
  let I:=smallRootOverlapColours c q x y C (4*k+5)
  let F:=I∪E
  have hCprot : ∀γ∈C∪E,∀a b,(c.col a b=some γ↔c₀.col a b=some γ):=
    fun γ hγ a b => hnorm.protectedColours a b γ hγ
  have hrootFree : ∀γ,c.IsFree x γ↔c₀.IsFree x γ := by
    intro γ
    simp only [IsFree]
    simp_rw [hnorm.rootRow]
  have hbadRole : ∀γ∈C∪E,∀v,γ∈badColours c q v↔γ∈badColours c₀ q v := by
    intro γ hγ v
    simp only [mem_badColours,IsFree,ne_eq]
    simp_rw [hCprot γ hγ]
  have hSRole : ∀γ∈C∪E,γ∈paletteS c q x y↔γ∈paletteS c₀ q x y := by
    intro γ hγ
    simp only [mem_paletteS_iff_free_or_bad,hrootFree γ,hbadRole γ hγ y]
  have hselected : T⊆badColours c q u∩paletteS c q x y := by
    intro γ hγ
    have hγF : γ∈C∪E:=mem_union_left E (mem_insert_of_mem hγ)
    obtain ⟨hbad,hS⟩:=mem_inter.mp (hT hγ)
    exact mem_inter.mpr ⟨(hbadRole γ hγF u).mpr hbad,(hSRole γ hγF).mpr hS⟩
  have hxz' : c.col x z=some α:=by rw [hnorm.rootRow];exact hxz
  have hxu' : c.col x u=some β:=by rw [hnorm.rootRow];exact hxu
  have hα' : c.IsFree y α:=(hnorm.otherMissing α).mpr hα
  have hδ₀x' : c.IsFree x δ₀:=(hrootFree δ₀).mpr hδ₀x
  have hβE : β∈C∪E:=mem_union_right C (by simp [E])
  have hδE : δ₀∈C∪E:=mem_union_right C (by simp [E])
  have halt' : c.IsFree z β ∨ ∃t,c.col z t=some β ∧ c.IsFree t δ₀ := by
    rcases halt with hfree|⟨t,hzt,hδt⟩
    · left
      intro v hv
      exact hfree v ((hCprot β hβE z v).mp hv)
    · exact Or.inr ⟨t,(hCprot β hβE z t).mpr hzt,
        fun v hv => hδt v ((hCprot δ₀ hδE t v).mp hv)⟩
  have hxNat : G.degree x<G.maxDegree := by
    have hn : (0:ℝ)≤ε*(G.maxDegree:ℝ):=mul_nonneg hε.le (Nat.cast_nonneg _)
    have hh : (G.degree x:ℝ)<(G.maxDegree:ℝ):=by nlinarith only [hx,hn]
    exact_mod_cast hh
  have hβy₀ : ¬c₀.IsFree y β := by
    apply CaoChenTerminalAssembly.selected_spine_colour_present_right hG hcm₀ hxz hα hβα hxNat
    rcases halt with hfree|⟨t,hzt,hδt⟩
    · exact Or.inl hfree
    · exact Or.inr ⟨t,δ₀,hzt,hδ₀x,hδt⟩
  have hβy : β∈presentColours c y:=
    (mem_presentColours c y β).mpr (fun h => hβy₀ ((hnorm.otherMissing β).mp h))
  have hδy : δ₀∈presentColours c y:=
    (mem_presentColours c y δ₀).mpr ((hnorm.cm.ab_facts hG).1 δ₀ hδ₀x')
  have hIpresent : ∀γ∈I,γ∈presentColours c y := by
    intro γ hγ
    obtain ⟨hγCA,v,hyv,_⟩:=mem_filter.mp hγ
    exact (presentColours_iff_coloured c y γ).mpr ⟨v,hyv⟩
  have hFpresent : ∀γ∈F,γ∈presentColours c y := by
    intro γ hγ
    rcases mem_union.mp hγ with hγI|hγE
    · exact hIpresent γ hγI
    · rcases (by simpa only [E,mem_insert,mem_singleton] using hγE : γ=β ∨ γ=δ₀) with rfl|rfl
      · exact hβy
      · exact hδy
  have hαI : α∉I := by
    intro h
    exact (mem_presentColours c y α).mp (hIpresent α h) hα'
  have hFcard : F.card≤k+2 := by
    have hf:=card_union_le I E
    change F.card≤I.card+E.card at hf
    change I.card≤k at hIcard
    omega
  have hTFinI : T∩F⊆I := by
    intro γ hγ
    obtain ⟨hγT,hγF⟩:=mem_inter.mp hγ
    rcases mem_union.mp hγF with hγI|hγE
    · exact hγI
    · rcases (by simpa only [E,mem_insert,mem_singleton] using hγE : γ=β ∨ γ=δ₀) with rfl|rfl
      · exact False.elim (hβT hγT)
      · exact False.elim (hδ₀T hγT)
  have hTFcard : (T∩F).card≤k:=(card_le_card hTFinI).trans hIcard
  have hmargin : CaoChenFiniteIteration.margin (2*k+5) k 0=4*k+5 := by
    simp only [CaoChenFiniteIteration.margin,Nat.sub_zero]
    omega
  have hstate := CaoChenFiniteIteration.initial_state c hnorm.cm q α T F k (2*k+5)
    hselected hcard hα'
  have hstate' : CaoChenFiniteIteration.State c c q x y u α T T I F k (2*k+5) 0 := by
    simpa only [hmargin] using hstate
  exact ⟨c,I,F,⟨hnorm,rfl,rfl,hIcard,hFcard,hTFinI,hTFcard,hαI,hselected,hxz',hxu',hα',
    hβy,hδ₀x',hFpresent,hβT,hδ₀T,halt',hstate'⟩⟩

end OverfullWork.CaoChenInitialFiniteState
