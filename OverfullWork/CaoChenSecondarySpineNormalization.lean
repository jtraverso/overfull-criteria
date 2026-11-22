module

public import OverfullWork.CaoChenSecondaryNormalization
public import OverfullWork.CaoChenPaletteOverlapNormalization

@[expose] public section


/-! # Secondary normalization on the actual low spokes of a fixed spine

The target vertices are constructed from protected spoke colours. Their
small root-only overlaps are normalized while the primary A-role profile
can only shrink. The selected bad/S palette and the large-overlap spine
role are retained by the same actual output colouring.
-/
namespace OverfullWork.CaoChenSecondarySpineNormalization
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenOverlapNormalization CaoChenSecondaryNormalization
open CaoChenPaletteOverlapNormalization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 5000000

noncomputable def spokeLeaves (c : PEC G (Fin G.maxDegree)) (u : V)
    (Tau : Finset (Fin G.maxDegree)) : Finset V :=
  univ.filter fun v => ∃τ∈Tau,c.col u v=some τ

noncomputable def smallSpokeColours (c : PEC G (Fin G.maxDegree)) (x u : V)
    (Tau : Finset (Fin G.maxDegree)) (m : ℕ) : Finset (Fin G.maxDegree) :=
  Tau.filter fun τ => ∃v,c.col u v=some τ ∧ (missing c v∩missing c x).card≤m

noncomputable def smallRootOverlapColours (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) (M : ℕ) : Finset (Fin G.maxDegree) :=
  (C∩paletteA c q x y).filter fun η => ∃v,c.col y v=some η ∧
    (missing c v∩missing c x).card≤M

/-- The B1 role, expressed directly by its actual low leaf and ROOT overlap. -/
def SpineRole (c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y : V)
    (α : Fin G.maxDegree) (M : ℕ) : Prop :=
  c.IsFree y α ∨ ∃v,c.col y v=some α ∧ (G.degree v:ℝ)<q ∧
    M<(missing c v∩(missing c x)).card

theorem bad_role_iff {c₀ c : PEC G (Fin G.maxDegree)} {x y : V}
    {F X : Finset (Fin G.maxDegree)} {A : Finset V} {M : ℕ}
    (hs : State c₀ c x y F X A M) (q : ℝ) (u : V) (γ : Fin G.maxDegree) (hγ : γ∈F) :
    γ∈badColours c q u ↔ γ∈badColours c₀ q u := by
  simp only [mem_badColours,IsFree,ne_eq]
  simp_rw [hs.protectedColours _ _ γ hγ]

theorem A_role_iff {c₀ c : PEC G (Fin G.maxDegree)} {x y : V}
    {F X : Finset (Fin G.maxDegree)} {A : Finset V} {M : ℕ}
    (hs : State c₀ c x y F X A M) (q : ℝ) (γ : Fin G.maxDegree) (hγ : γ∈F) :
    γ∈paletteA c q x y ↔ γ∈paletteA c₀ q x y := by
  have hp : γ∈presentColours c x ↔ γ∈presentColours c₀ x := by
    simp only [mem_presentColours,IsFree]
    simp_rw [hs.rootRow]
  simp only [mem_paletteA,hp]
  simp_rw [hs.protectedColours _ _ γ hγ]

theorem S_role_iff {c₀ c : PEC G (Fin G.maxDegree)} {x y : V}
    {F X : Finset (Fin G.maxDegree)} {A : Finset V} {M : ℕ}
    (hs : State c₀ c x y F X A M) (q : ℝ) (γ : Fin G.maxDegree) (hγ : γ∈F) :
    γ∈paletteS c q x y ↔ γ∈paletteS c₀ q x y := by
  have hx : c.IsFree x γ↔c₀.IsFree x γ := by
    simp only [IsFree]
    simp_rw [hs.rootRow]
  simp only [mem_paletteS_iff_free_or_bad,hx,bad_role_iff hs q y γ hγ]

theorem primary_colours_subset {c₀ c : PEC G (Fin G.maxDegree)} {x y : V}
    {F C : Finset (Fin G.maxDegree)} {M : ℕ} (q : ℝ)
    (hs : State c₀ c x y F (missing c₀ x) (paletteLeaves c₀ q x y C) M) (hCF : C⊆F) :
    smallRootOverlapColours c q x y C M⊆smallRootOverlapColours c₀ q x y C M := by
  intro γ hγ
  obtain ⟨hγCA,v,hyv,hvsmall⟩:=mem_filter.mp hγ
  obtain ⟨hγC,hγA⟩:=mem_inter.mp hγCA
  have hγA₀ : γ∈paletteA c₀ q x y:=(A_role_iff hs q γ (hCF hγC)).mp hγA
  have hyv₀ : c₀.col y v=some γ:=(hs.protectedColours y v γ (hCF hγC)).mp hyv
  have hvT : v∈paletteLeaves c₀ q x y C:=mem_filter.mpr
    ⟨mem_univ v,γ,mem_inter.mpr ⟨hγC,hγA₀⟩,hyv₀⟩
  have hxmissing : missing c x=missing c₀ x := by
    ext η
    simp only [mem_missing,IsFree]
    simp_rw [hs.rootRow]
  have hvlow : v∈lowOverlapVertices c (missing c₀ x)
      (paletteLeaves c₀ q x y C) M:=mem_filter.mpr ⟨hvT,by simpa only [hxmissing] using hvsmall⟩
  exact mem_filter.mpr ⟨mem_inter.mpr ⟨hγC,hγA₀⟩,v,hyv₀,(mem_filter.mp (hs.primarySubset hvlow)).2⟩

theorem spineRole_preserved {c₀ c : PEC G (Fin G.maxDegree)} {x y z : V}
    {F C : Finset (Fin G.maxDegree)} {M : ℕ} {α : Fin G.maxDegree}
    (q : ℝ) (hs : State c₀ c x y F (missing c₀ x) (paletteLeaves c₀ q x y C) M)
    (hCF : C⊆F) (hαC : α∈C) (hxz : c₀.col x z=some α)
    (hrole : SpineRole c₀ q x y α M) : SpineRole c q x y α M := by
  rcases hrole with hfree|⟨v,hyv,hvlow,hvlarge⟩
  · exact Or.inl ((hs.otherMissing α).mpr hfree)
  · right
    refine ⟨v,(hs.protectedColours y v α (hCF hαC)).mpr hyv,hvlow,?_⟩
    by_contra hn
    have hvT : v∈paletteLeaves c₀ q x y C := by
      apply mem_filter.mpr
      refine ⟨mem_univ v,α,mem_inter.mpr ⟨hαC,?_⟩,hyv⟩
      exact (mem_paletteA c₀ q x y α).mpr
        ⟨(presentColours_iff_coloured c₀ x α).mpr ⟨z,hxz⟩,v,hyv,hvlow⟩
    have hxmissing : missing c x=missing c₀ x := by
      ext η
      simp only [mem_missing,IsFree]
      simp_rw [hs.rootRow]
    have hv : v∈lowOverlapVertices c (missing c₀ x)
        (paletteLeaves c₀ q x y C) M:=mem_filter.mpr ⟨hvT,by simpa only [hxmissing] using (show (missing c v∩missing c x).card≤M by omega)⟩
    have hh:=(mem_filter.mp (hs.primarySubset hv)).2
    omega

/-- Actual secondary normalization of the low-spoke colour family Tau.
The finite budgets are stated on colour-family sizes, before any endpoint
choice. D remains a bad/S palette and the B1 spine role is preserved. -/
theorem exists_secondary_spine_normalization (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y z u : V} {α : Fin G.maxDegree}
    (hcm₀ : IsColMinus c₀ x y) (hxz : c₀.col x z=some α)
    (D Tau C F : Finset (Fin G.maxDegree)) (m M L : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hD : D⊆badColours c₀ ((1-ε)*(G.maxDegree:ℝ)) u∩paletteS c₀ ((1-ε)*(G.maxDegree:ℝ)) x y)
    (hTau : Tau⊆lowColours c₀ ((1-ε)*(G.maxDegree:ℝ)) u)
    (hTauF : Tau⊆F) (hDF : D⊆F) (hCF : C⊆F) (hαC : α∈C)
    (hrole : SpineRole c₀ ((1-ε)*(G.maxDegree:ℝ)) x y α M)
    (hL : 1≤ε*(L:ℝ))
    (hthreshold : (m:ℝ)+((Tau.card-1:ℕ):ℝ)*
      ((F.card+(m+2)*Tau.card+(M+2)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : F.card+(m+2)*Tau.card+(M+2)*C.card+Tau.card*m<(missing c₀ x).card) :
    ∃c : PEC G (Fin G.maxDegree),
      State c₀ c x y F (missing c₀ x) (paletteLeaves c₀ ((1-ε)*(G.maxDegree:ℝ)) x y C) M ∧
      c.col x z=some α ∧
      D⊆badColours c ((1-ε)*(G.maxDegree:ℝ)) u∩paletteS c ((1-ε)*(G.maxDegree:ℝ)) x y ∧
      (smallSpokeColours c x u Tau m).card<L ∧
      smallRootOverlapColours c ((1-ε)*(G.maxDegree:ℝ)) x y C M⊆
        smallRootOverlapColours c₀ ((1-ε)*(G.maxDegree:ℝ)) x y C M ∧
      SpineRole c ((1-ε)*(G.maxDegree:ℝ)) x y α M := by
  let q:=(1-ε)*(G.maxDegree:ℝ)
  let T:=spokeLeaves c₀ u Tau
  let A:=paletteLeaves c₀ q x y C
  have hTcard : T.card=Tau.card := by
    apply CaoChenPaletteCounting.card_leaves_eq_card_colours u T Tau
    · intro v hv
      exact (mem_filter.mp hv).2
    · intro τ hτ
      obtain ⟨v,hyv,_⟩:=(mem_lowColours c₀ q u τ).mp (hTau hτ)
      exact ⟨v,mem_filter.mpr ⟨mem_univ v,τ,hτ,hyv⟩,hyv⟩
  have hTlow : ∀v∈T,(G.degree v:ℝ)<q := by
    intro v hv
    obtain ⟨τ,hτ,huv⟩:=(mem_filter.mp hv).2
    obtain ⟨w,huw,hwlow⟩:=(mem_lowColours c₀ q u τ).mp (hTau hτ)
    have he : v=w:=c₀.col_proper huv huw
    subst w
    exact hwlow
  have hAcard : A.card≤C.card := by
    rw [paletteLeaves_card_eq]
    exact card_le_card inter_subset_left
  have hthreshold' : (m:ℝ)+((T.card-1:ℕ):ℝ)*
      ((F.card+(m+2)*T.card+(M+2)*A.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    rw [hTcard]
    have hF : F.card+(m+2)*Tau.card+(M+2)*A.card+1≤
        F.card+(m+2)*Tau.card+(M+2)*C.card+1 := by
      nlinarith only [Nat.mul_le_mul_left (M+2) hAcard]
    have hFR : ((F.card+(m+2)*Tau.card+(M+2)*A.card+1:ℕ):ℝ)≤
        ((F.card+(m+2)*Tau.card+(M+2)*C.card+1:ℕ):ℝ) := by exact_mod_cast hF
    have hm:=mul_le_mul_of_nonneg_left hFR (Nat.cast_nonneg (Tau.card-1): (0:ℝ)≤_)
    linarith only [hm,hthreshold]
  have hbudget' : F.card+(m+2)*T.card+(M+2)*A.card+T.card*m<(missing c₀ x).card := by
    rw [hTcard]
    have hm:=Nat.mul_le_mul_left (M+2) hAcard
    omega
  obtain ⟨c,hs,hsmall⟩:=exists_root_overlap_normalization_preserving_primary hG c₀ hcm₀
    T A F (missing c₀ x) m M L ε hε hεone hx hTlow hL hthreshold' hbudget'
  have hD' : D⊆badColours c q u∩paletteS c q x y := by
    intro γ hγ
    obtain ⟨hbad,hS⟩:=mem_inter.mp (hD hγ)
    exact mem_inter.mpr ⟨(bad_role_iff hs q u γ (hDF hγ)).mpr hbad,
      (S_role_iff hs q γ (hDF hγ)).mpr hS⟩
  have hsmallcard : (smallSpokeColours c x u Tau m).card=
      (lowOverlapVertices c (missing c x) T m).card := by
    symm
    apply CaoChenPaletteCounting.card_leaves_eq_card_colours u
      (lowOverlapVertices c (missing c x) T m) (smallSpokeColours c x u Tau m)
    · intro v hv
      obtain ⟨hvT,hvsmall⟩:=mem_filter.mp hv
      obtain ⟨τ,hτ,huv₀⟩:=(mem_filter.mp hvT).2
      have huv : c.col u v=some τ:=(hs.protectedColours u v τ (hTauF hτ)).mpr huv₀
      exact ⟨τ,mem_filter.mpr ⟨hτ,v,huv,hvsmall⟩,huv⟩
    · intro τ hτ
      obtain ⟨hτTau,v,huv,hvsmall⟩:=mem_filter.mp hτ
      have huv₀ : c₀.col u v=some τ:=(hs.protectedColours u v τ (hTauF hτTau)).mp huv
      have hvT : v∈T:=mem_filter.mpr ⟨mem_univ v,τ,hτTau,huv₀⟩
      exact ⟨v,mem_filter.mpr ⟨hvT,hvsmall⟩,huv⟩
  refine ⟨c,hs,?_,hD',?_,primary_colours_subset q hs hCF,
    spineRole_preserved q hs hCF hαC hxz hrole⟩
  · rw [hs.rootRow]
    exact hxz
  · rw [hsmallcard]
    exact hsmall

end OverfullWork.CaoChenSecondarySpineNormalization
