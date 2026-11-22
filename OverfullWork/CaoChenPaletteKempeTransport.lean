module

public import OverfullWork.CaoChenPalettes
public import OverfullWork.CaoChenMissingIntersection

@[expose] public section


/-! # Exact palette transport and a strict root-palette gain

On a Kempe component every incident colour is transported by the same
transposition. This applies to actual high, low, and bad palettes, not just
their union. The final construction is the missing-colour branch of the
palette improvement in Cao--Chen Claim 5.3; it does not assume an extremal
colouring or the full Lemma 7.
-/
namespace OverfullWork.CaoChenPaletteKempeTransport
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 3000000

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every incident edge at a vertex on the component undergoes the same
colour transposition. -/
theorem col_eq_swap_iff {k : ℕ} (c : PEC G (Fin k))
    (δ η : Fin k) {r u : V}
    (hu : (c.kempeGraph δ η).Reachable r u) (w : V) (γ : Fin k) :
    (c.kempeSwap δ η r).col u w=some γ ↔
      c.col u w=some (Equiv.swap δ η γ) := by
  rw [kempeSwap_col,kempeSwapFun_of_reachable c δ η hu w]
  cases he : c.col u w with
  | none => simp
  | some τ =>
    simp only [Option.map_some,Option.some.injEq,Equiv.swap_apply_eq_iff]

/-- The actual bad palette, including both missing and low-edge colours,
is transported exactly on the component. -/
theorem mem_bad_swap_iff {k : ℕ} (c : PEC G (Fin k)) (q : ℝ)
    (δ η : Fin k) {r u : V}
    (hu : (c.kempeGraph δ η).Reachable r u) (γ : Fin k) :
    γ∈badColours (c.kempeSwap δ η r) q u ↔
      Equiv.swap δ η γ∈badColours c q u := by
  simp only [mem_badColours,isFree_kempeSwap_of_reachable c δ η hu,
    col_eq_swap_iff c δ η hu]

/-- Low colours are transported with their original low endpoint. -/
theorem mem_low_swap_iff {k : ℕ} (c : PEC G (Fin k)) (q : ℝ)
    (δ η : Fin k) {r u : V}
    (hu : (c.kempeGraph δ η).Reachable r u) (γ : Fin k) :
    γ∈lowColours (c.kempeSwap δ η r) q u ↔
      Equiv.swap δ η γ∈lowColours c q u := by
  simp only [mem_lowColours,col_eq_swap_iff c δ η hu]

/-- High colours are transported with their original high endpoint. -/
theorem mem_high_swap_iff {k : ℕ} (c : PEC G (Fin k)) (q : ℝ)
    (δ η : Fin k) {r u : V}
    (hu : (c.kempeGraph δ η).Reachable r u) (γ : Fin k) :
    γ∈highColours (c.kempeSwap δ η r) q u ↔
      Equiv.swap δ η γ∈highColours c q u := by
  simp only [mem_highColours,col_eq_swap_iff c δ η hu]

private theorem mem_image_swap {C : Type*} [DecidableEq C]
    (T : Finset C) (δ η γ : C) :
    γ∈T.image (Equiv.swap δ η) ↔ Equiv.swap δ η γ∈T := by
  constructor
  · rintro h
    obtain ⟨τ,hτ,hτγ⟩ := mem_image.mp h
    rw [←hτγ,Equiv.swap_apply_self]
    exact hτ
  · intro h
    exact mem_image.mpr ⟨Equiv.swap δ η γ,h,by simp⟩

/-- Replacing a selected non-root colour by a new root colour increases
the selected intersection by exactly one, without changing its size. -/
theorem swap_inter_card_gain {C : Type*} [DecidableEq C]
    (T X : Finset C) {δ η : C}
    (hηT : η∈T) (hδT : δ∉T) (hδX : δ∈X) (hηX : η∉X) :
    ((T.image (Equiv.swap δ η))∩X).card=(T∩X).card+1 := by
  have hne : δ≠η := by intro h;exact hδT (h ▸ hηT)
  have he : (T.image (Equiv.swap δ η))∩X=insert δ (T∩X) := by
    ext γ
    rw [mem_inter,mem_image_swap,mem_insert,mem_inter]
    by_cases hγδ : γ=δ
    · subst γ
      simp only [Equiv.swap_apply_left,hηT,hδX,and_self,true_or]
    · by_cases hγη : γ=η
      · subst γ
        simp [hne.symm,hηX]
      · rw [Equiv.swap_apply_of_ne_of_ne hγδ hγη]
        simp only [hγδ,false_or]
  rw [he,card_insert_of_notMem]
  exact fun h => hδT (mem_inter.mp h).1

/-- Fixing both endpoint rows fixes the entire S palette. -/
theorem paletteS_eq_of_endpoint_rows {k : ℕ} (c c' : PEC G (Fin k))
    (q : ℝ) (x y : V)
    (hx : ∀w,c'.col x w=c.col x w) (hy : ∀w,c'.col y w=c.col y w) :
    paletteS c' q x y=paletteS c q x y := by
  ext γ
  simp only [mem_paletteS_iff_free_or_bad,mem_badColours,IsFree]
  simp_rw [hx,hy]

omit [DecidableEq V] in
/-- The selected palette remains inside S when both swapped colours
belong to S. This is the actual transported palette of the local moves. -/
theorem image_swap_subset_paletteS {k : ℕ} (c : PEC G (Fin k))
    (q : ℝ) (x y : V) (T : Finset (Fin k)) (hT : T⊆paletteS c q x y)
    {δ η : Fin k} (hδ : δ∈paletteS c q x y) (hη : η∈paletteS c q x y) :
    T.image (Equiv.swap δ η)⊆paletteS c q x y := by
  intro γ hγ
  obtain ⟨τ,hτ,rfl⟩:=mem_image.mp hγ
  by_cases hτδ : τ=δ
  · subst τ
    simpa only [Equiv.swap_apply_left] using hη
  · by_cases hτη : τ=η
    · subst τ
      simpa only [Equiv.swap_apply_right] using hδ
    · rw [Equiv.swap_apply_of_ne_of_ne hτδ hτη]
      exact hT hτ

/-- A genuine Kempe improvement for a missing bad colour at the spine.
The root row, the other endpoint row, and all protected colour classes
are preserved, while the selected bad palette gains a root-missing colour.
This constructs the Case 1.1 move rather than postulating recolourability. -/
theorem exists_missing_spine_palette_gain (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u : V}
    (hcm : IsColMinus c x y) (hux : u≠x) (huy : u≠y)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u) {δ η : Fin G.maxDegree}
    (hδx : c.IsFree x δ) (hηy : c.IsFree y η) (hηu : c.IsFree u η)
    (hηT : η∈T) (hδT : δ∉T) (hδF : δ∉F) (hηF : η∉F) :
    ∃c' : PEC G (Fin G.maxDegree),∃T' : Finset (Fin G.maxDegree),
      IsColMinus c' x y ∧
      (∀w,c'.col x w=c.col x w) ∧
      (∀w,c'.col y w=c.col y w) ∧
      (∀a b γ,γ∈F → (c'.col a b=some γ ↔ c.col a b=some γ)) ∧
      T'⊆badColours c' q u ∧ T'=T.image (Equiv.swap δ η) ∧ T'.card=T.card ∧
      (T'∩missing c' x).card=(T∩missing c x).card+1 := by
  have hlink := (hcm.ab_facts hG).2 δ η hδx hηy
  have hoffx : ¬(c.kempeGraph δ η).Reachable u x := by
    intro h
    exact not_three_linked c hcm.adj.ne hux.symm huy.symm
      (Or.inl hδx) (Or.inr hηy) (Or.inr hηu) hlink h.symm
  have hoffy : ¬(c.kempeGraph δ η).Reachable u y :=
    fun h => hoffx (h.trans hlink.symm)
  let c' := c.kempeSwap δ η u
  let T' := T.image (Equiv.swap δ η)
  have hmiss : missing c' x=missing c x := by
    ext γ
    simp only [c',mem_missing,isFree_kempeSwap_of_not_reachable c δ η hoffx]
  have hηx : η∉missing c x := by
    intro h
    exact (hcm.ab_facts hG).1 η (mem_missing.mp h) hηy
  refine ⟨c',T',hcm.kempeSwap δ η u,?_,?_,?_,?_,rfl,?_,?_⟩
  · intro w
    exact kempeSwapFun_of_not_reachable c δ η hoffx w
  · intro w
    exact kempeSwapFun_of_not_reachable c δ η hoffy w
  · intro a b γ hγ
    have hγδ : γ≠δ := by intro he;exact hδF (he ▸ hγ)
    have hγη : γ≠η := by intro he;exact hηF (he ▸ hγ)
    by_cases hr : (c.kempeGraph δ η).Reachable u a
    · rw [col_eq_swap_iff c δ η hr]
      rw [Equiv.swap_apply_of_ne_of_ne hγδ hγη]
    · change c.kempeSwapFun δ η u a b=some γ ↔ _
      rw [kempeSwapFun_of_not_reachable c δ η hr]
  · intro γ hγ
    apply (mem_bad_swap_iff c q δ η (SimpleGraph.Reachable.refl u) γ).mpr
    exact hT ((mem_image_swap T δ η γ).mp hγ)
  · exact card_image_of_injective T (Equiv.swap δ η).injective
  · rw [hmiss]
    exact swap_inter_card_gain T (missing c x) hηT hδT (mem_missing.mpr hδx) hηx

/-- The other local improvement in Claim 5.3: the selected colour is
present on an edge to a low leaf admitting a common missing colour with
the root. The three endpoint argument proves that the swap avoids both
root endpoints; no off-root switching hypothesis is assumed. -/
theorem exists_low_leaf_spine_palette_gain (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y u z : V}
    (hcm : IsColMinus c x y) (hzx : z≠x)
    (q : ℝ) (T F : Finset (Fin G.maxDegree))
    (hT : T⊆badColours c q u) {δ η : Fin G.maxDegree}
    (hδx : c.IsFree x δ) (hηy : c.IsFree y η)
    (huz : c.col u z=some η) (hδz : c.IsFree z δ)
    (hηT : η∈T) (hδT : δ∉T) (hδF : δ∉F) (hηF : η∉F) :
    ∃c' : PEC G (Fin G.maxDegree),∃T' : Finset (Fin G.maxDegree),
      IsColMinus c' x y ∧
      (∀w,c'.col x w=c.col x w) ∧
      (∀w,c'.col y w=c.col y w) ∧
      (∀a b γ,γ∈F → (c'.col a b=some γ ↔ c.col a b=some γ)) ∧
      T'⊆badColours c' q u ∧ T'=T.image (Equiv.swap δ η) ∧ T'.card=T.card ∧
      (T'∩missing c' x).card=(T∩missing c x).card+1 := by
  have hzy : z≠y := by
    intro he
    subst z
    exact hηy u (by rw [c.col_symm];exact huz)
  have hlink := (hcm.ab_facts hG).2 δ η hδx hηy
  have hzoff : ¬(c.kempeGraph δ η).Reachable z x := by
    intro h
    exact not_three_linked c hcm.adj.ne hzx.symm hzy.symm
      (Or.inl hδx) (Or.inr hηy) (Or.inl hδz) hlink h.symm
  have hzu : (c.kempeGraph δ η).Reachable z u := by
    apply SimpleGraph.Adj.reachable
    exact ⟨(c.col_adj huz).ne.symm,Or.inr (by rw [c.col_symm];exact huz)⟩
  have hoffx : ¬(c.kempeGraph δ η).Reachable u x :=
    fun h => hzoff (hzu.trans h)
  have hoffy : ¬(c.kempeGraph δ η).Reachable u y :=
    fun h => hoffx (h.trans hlink.symm)
  let c' := c.kempeSwap δ η u
  let T' := T.image (Equiv.swap δ η)
  have hmiss : missing c' x=missing c x := by
    ext γ
    simp only [c',mem_missing,isFree_kempeSwap_of_not_reachable c δ η hoffx]
  have hηx : η∉missing c x := by
    intro h
    exact (hcm.ab_facts hG).1 η (mem_missing.mp h) hηy
  refine ⟨c',T',hcm.kempeSwap δ η u,?_,?_,?_,?_,rfl,?_,?_⟩
  · intro w
    exact kempeSwapFun_of_not_reachable c δ η hoffx w
  · intro w
    exact kempeSwapFun_of_not_reachable c δ η hoffy w
  · intro a b γ hγ
    have hγδ : γ≠δ := by intro he;exact hδF (he ▸ hγ)
    have hγη : γ≠η := by intro he;exact hηF (he ▸ hγ)
    by_cases hr : (c.kempeGraph δ η).Reachable u a
    · rw [col_eq_swap_iff c δ η hr,Equiv.swap_apply_of_ne_of_ne hγδ hγη]
    · change c.kempeSwapFun δ η u a b=some γ ↔ _
      rw [kempeSwapFun_of_not_reachable c δ η hr]
  · intro γ hγ
    apply (mem_bad_swap_iff c q δ η (SimpleGraph.Reachable.refl u) γ).mpr
    exact hT ((mem_image_swap T δ η γ).mp hγ)
  · exact card_image_of_injective T (Equiv.swap δ η).injective
  · rw [hmiss]
    exact swap_inter_card_gain T (missing c x) hηT hδT (mem_missing.mpr hδx) hηx

end OverfullWork.CaoChenPaletteKempeTransport
