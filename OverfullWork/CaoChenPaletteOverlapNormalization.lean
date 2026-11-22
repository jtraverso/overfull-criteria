module

public import OverfullWork.CaoChenOverlapNormalization
public import OverfullWork.CaoChenPaletteCounting

@[expose] public section


/-! # Normalizing the actual A-colour leaves of a protected palette

The selected vertices are the actual low neighbours of y reached by colours
in C intersect A. No endpoint selector is postulated. Properness bounds their
number by |C| and identifies the small-overlap colour count with a vertex count.
The constructed colouring fixes all selected roles and makes that count < L.
-/
namespace OverfullWork.CaoChenPaletteOverlapNormalization
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenOverlapNormalization
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 4000000

noncomputable def paletteLeaves (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) : Finset V :=
  univ.filter fun v => ∃η∈C∩paletteA c q x y,c.col y v=some η

noncomputable def smallOverlapColours (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) (M : ℕ) : Finset (Fin G.maxDegree) :=
  (C∩paletteA c q x y).filter fun η => ∃v,c.col y v=some η ∧
    (missing c v∩(missing c x∪missing c y)).card≤M

/-- The actual A-leaves are in bijection with their protected colours. -/
theorem paletteLeaves_card_eq (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) :
    (paletteLeaves c q x y C).card=(C∩paletteA c q x y).card := by
  apply CaoChenPaletteCounting.card_leaves_eq_card_colours
  · intro v hv
    exact (mem_filter.mp hv).2
  · intro η hη
    obtain ⟨_,v,hyv,_⟩:=(mem_paletteA c q x y η).mp (mem_inter.mp hη).2
    exact ⟨v,mem_filter.mpr ⟨mem_univ v,η,hη,hyv⟩,hyv⟩

omit [DecidableEq V] in
/-- The overlap bound is a bound on actual colours as well as vertices. -/
theorem smallOverlapColours_card_eq (c : PEC G (Fin G.maxDegree)) (q : ℝ)
    (x y : V) (C : Finset (Fin G.maxDegree)) (M : ℕ) :
    (smallOverlapColours c q x y C M).card=
      (lowOverlapVertices c (missing c x∪missing c y) (paletteLeaves c q x y C) M).card := by
  symm
  apply CaoChenPaletteCounting.card_leaves_eq_card_colours
  · intro v hv
    obtain ⟨hvT,hvlow⟩:=mem_filter.mp hv
    obtain ⟨η,hη,hyv⟩:=(mem_filter.mp hvT).2
    exact ⟨η,mem_filter.mpr ⟨hη,v,hyv,hvlow⟩,hyv⟩
  · intro η hη
    obtain ⟨hηCA,v,hyv,hvlow⟩:=mem_filter.mp hη
    exact ⟨v,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ v,η,hηCA,hyv⟩,hvlow⟩,hyv⟩

/-- A concrete Claim-5.1/5.4 normalization for a fixed protected colour
family C. All budgets depend on |C|, rather than the order of the graph.
The constructed colouring preserves the y-roles of every protected colour. -/
theorem exists_normalized_palette_overlap (hG : IsClassTwo G)
    (c₀ : PEC G (Fin G.maxDegree)) {x y : V} (hcm₀ : IsColMinus c₀ x y)
    (q : ℝ) (C : Finset (Fin G.maxDegree)) (M L : ℕ)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1)
    (hq : q=(1-ε)*(G.maxDegree:ℝ)) (hx : (G.degree x:ℝ)<q)
    (hL : 1≤ε*(L:ℝ))
    (hthreshold : (M:ℝ)+((C.card-1:ℕ):ℝ)*(((M+3)*C.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ))
    (hbudget : (M+3)*C.card+C.card*M<(missing c₀ x).card) :
    ∃ c : PEC G (Fin G.maxDegree),IsColMinus c x y ∧
      (∀w,c.col x w=c₀.col x w) ∧
      (∀γ,c.IsFree y γ↔c₀.IsFree y γ) ∧
      (∀a b γ,γ∈C → (c.col a b=some γ↔c₀.col a b=some γ)) ∧
      (∀η∈C,∀v,c.col y v=some η↔c₀.col y v=some η) ∧
      (∀η∈C,η∈paletteA c q x y↔η∈paletteA c₀ q x y) ∧
      paletteLeaves c q x y C=paletteLeaves c₀ q x y C ∧
      (smallOverlapColours c q x y C M).card<L := by
  let T:=paletteLeaves c₀ q x y C
  have hTcard : T.card≤C.card := by
    rw [paletteLeaves_card_eq]
    exact card_le_card inter_subset_left
  have hTlow : ∀v∈T,(G.degree v:ℝ)<(1-ε)*(G.maxDegree:ℝ) := by
    intro v hv
    obtain ⟨η,hη,hyv⟩:=(mem_filter.mp hv).2
    obtain ⟨_,w,hyw,hw⟩:=(mem_paletteA c₀ q x y η).mp (mem_inter.mp hη).2
    have hvw : v=w:=c₀.col_proper hyv hyw
    subst w
    rwa [←hq]
  have hFmax : C.card+(M+2)*T.card≤(M+3)*C.card := by nlinarith
  have hth : (M:ℝ)+((T.card-1:ℕ):ℝ)*
      ((C.card+(M+2)*T.card+1:ℕ):ℝ)≤ε^2*(G.maxDegree:ℝ) := by
    have hN : T.card-1≤C.card-1:=by omega
    have hNR : ((T.card-1:ℕ):ℝ)≤((C.card-1:ℕ):ℝ):=by exact_mod_cast hN
    have hFR : ((C.card+(M+2)*T.card+1:ℕ):ℝ)≤(((M+3)*C.card+1:ℕ):ℝ):=by
      exact_mod_cast (by omega : C.card+(M+2)*T.card+1≤(M+3)*C.card+1)
    have hh:=mul_le_mul hNR hFR (by positivity) (by positivity)
    nlinarith only [hh,hthreshold]
  have hbud : C.card+(M+2)*T.card+T.card*M<(missing c₀ x).card := by
    have hh:=Nat.mul_le_mul_right M hTcard
    omega
  obtain ⟨c,hcm,hrow,hfree,hfixed,hsmall⟩:=exists_normalized_overlap_colouring hG c₀ hcm₀
    T C M L ε hε hεone (by rwa [←hq]) hTlow hL hth hbud
  have hyroles : ∀η∈C,∀v,c.col y v=some η↔c₀.col y v=some η := by
    intro η hη v
    exact hfixed y v η hη
  have hxpresent : ∀η,η∈presentColours c x↔η∈presentColours c₀ x := by
    intro η
    simp only [mem_presentColours,IsFree]
    simp_rw [hrow]
  have hAroles : ∀η∈C,η∈paletteA c q x y↔η∈paletteA c₀ q x y := by
    intro η hη
    simp only [mem_paletteA,hxpresent η,hyroles η hη]
  have hleaves : paletteLeaves c q x y C=paletteLeaves c₀ q x y C := by
    ext v
    simp only [paletteLeaves,mem_filter,mem_univ,true_and,mem_inter]
    constructor
    · rintro ⟨η,⟨hηC,hηA⟩,hyv⟩
      exact ⟨η,⟨hηC,(hAroles η hηC).mp hηA⟩,(hyroles η hηC v).mp hyv⟩
    · rintro ⟨η,⟨hηC,hηA⟩,hyv⟩
      exact ⟨η,⟨hηC,(hAroles η hηC).mpr hηA⟩,(hyroles η hηC v).mpr hyv⟩
  refine ⟨c,hcm,hrow,hfree,hfixed,hyroles,hAroles,hleaves,?_⟩
  rw [smallOverlapColours_card_eq,hleaves]
  exact hsmall

end OverfullWork.CaoChenPaletteOverlapNormalization
