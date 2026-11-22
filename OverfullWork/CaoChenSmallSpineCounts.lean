module

public import OverfullWork.CaoChenGeneralPaletteSpine
public import OverfullWork.CaoChenMinimalPalette

@[expose] public section


/-! # Exact source counts and degree bounds on small-root S-spines

Properness identifies S-coloured neighbours with present S-colours.
The palette partition then gives an exact source count. The genuine
palette-presence theorem bounds every source degree, including the
previously exceptional double-maximum configuration.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset Overfull LeanPool.Vizing LeanPool.Vizing.PEC
open CaoChenPalettes CaoChenPaletteCounting CaoChenR1Continuation CaoChenMinimalPalette
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
set_option maxHeartbeats 2000000

/-- No class or degree assumption is needed for this proper-colouring bijection. -/
theorem neighboursS_card_eq_paletteS_inter_present
    (c : PEC G (Fin G.maxDegree)) (q : ℝ) (x y : V) :
    (neighboursS c q x y).card=(paletteS c q x y∩presentColours c x).card := by
  apply card_leaves_eq_card_colours x (neighboursS c q x y)
    (paletteS c q x y∩presentColours c x)
  · intro u hu
    obtain ⟨_,η,hη,hcol⟩:=mem_filter.mp hu
    exact ⟨η,mem_inter.mpr ⟨hη,(presentColours_iff_coloured c x η).mpr ⟨u,hcol⟩⟩,hcol⟩
  · intro η hη
    obtain ⟨hηS,hηP⟩:=mem_inter.mp hη
    obtain ⟨u,hcol⟩:=(presentColours_iff_coloured c x η).mp hηP
    exact ⟨u,mem_filter.mpr ⟨(mem_neighborFinset G x u).mpr (c.col_adj hcol),η,hηS,hcol⟩,hcol⟩

/-- The root's single uncoloured edge accounts for the final `+1`. -/
theorem neighboursS_card_add_paletteB_add_one (_hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y) (q : ℝ) :
    (neighboursS c q x y).card+(paletteB c q x y).card+1=G.degree x := by
  have hBsub : paletteB c q x y⊆presentColours c x := by
    intro η hη
    exact ((mem_paletteB c q x y η).mp hη).1
  have hunion : (paletteS c q x y∩presentColours c x)∪paletteB c q x y=
      presentColours c x := by
    ext η
    have hp:=congrArg (fun P : Finset (Fin G.maxDegree) => η∈P)
      (paletteS_union_paletteB c q x y)
    simp only [mem_union,mem_univ] at hp
    constructor
    · intro hη
      rcases mem_union.mp hη with hS|hB
      · exact (mem_inter.mp hS).2
      · exact hBsub hB
    · intro hη
      rcases hp.mpr trivial with hS|hB
      · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hS,hη⟩))
      · exact mem_union.mpr (Or.inr hB)
  have hd : Disjoint (paletteS c q x y∩presentColours c x) (paletteB c q x y) :=
    (disjoint_paletteS_paletteB c q x y).mono_left inter_subset_left
  have hc:=congrArg Finset.card hunion
  rw [card_union_of_disjoint hd,←neighboursS_card_eq_paletteS_inter_present] at hc
  have hp : (presentColours c x).card=(colNbrs c x).card :=
    CommonMissingColour.present_colour_card G.maxDegree c x
  have hx:=hcm.card_colNbrs x
  simp only [true_or,if_true] at hx
  omega

/-- Every S-neighbour sees all S-colours, so its degree plus the
complementary B-palette pays the entire maximum-degree palette. -/
theorem neighboursS_degree_add_paletteB_ge (hcrit : IsDeltaCritical G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y)
    (q : ℝ) (hq : 0<q) (hsmall : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ))
    (u : V) (hu : u∈neighboursS c q x y) :
    G.maxDegree≤G.degree u+(paletteB c q x y).card := by
  obtain ⟨_,α,hα,hxu⟩:=mem_filter.mp hu
  have hpres:=paletteS_subset_present_at_spine_of_paletteS hcrit hcm hxu q hq hsmall hα
  have hc:=card_le_card hpres
  have hdegree : (presentColours c u).card≤G.degree u := by
    have hp : (presentColours c u).card=(colNbrs c u).card :=
      CommonMissingColour.present_colour_card G.maxDegree c u
    rw [hp]
    exact (card_le_card (filter_subset _ _)).trans_eq (card_neighborFinset_eq_degree G u)
  have hpartition:=paletteS_card_add_paletteB_card c q x y
  omega

omit [DecidableEq V] in
/-- The source set consists of actual neighbours, without any hidden dummy edge. -/
theorem neighboursS_subset_neighbourFinset (c : PEC G (Fin G.maxDegree))
    (q : ℝ) (x y : V) : neighboursS c q x y⊆G.neighborFinset x :=
  filter_subset _ _

/-- The B-palette misses at least two root incidences, leaving an S-source. -/
theorem neighboursS_card_pos (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y) (q : ℝ) :
    0<(neighboursS c q x y).card := by
  have hc:=neighboursS_card_add_paletteB_add_one hG hcm q
  have hB:=paletteB_card_add_two_le_degree hG hcm q
  omega

theorem neighboursS_nonempty (hG : IsClassTwo G)
    {c : PEC G (Fin G.maxDegree)} {x y : V} (hcm : IsColMinus c x y) (q : ℝ) :
    (neighboursS c q x y).Nonempty :=
  card_pos.mp (neighboursS_card_pos hG hcm q)

end OverfullWork.CaoChenDischarging
