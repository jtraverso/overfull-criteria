module

public import OverfullWork.CaoChenPaletteCounting
public import OverfullWork.CaoChenDistanceFour

@[expose] public section


/-! # The actual minimum-palette choice in Cao--Chen Claim 3.2

The minimum ranges over all neighbours and all proper colourings of
the corresponding edge-deleted graph.  Nat.find constructs this minimum
without an assumption that the type of partial colourings is finite.
-/
namespace OverfullWork.CaoChenMinimalPalette
open SimpleGraph Finset LeanPool.Vizing LeanPool.Vizing.PEC Overfull
open CaoChenPalettes CaoChenPaletteCounting CaoChenDischarging
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : PEC G (Fin G.maxDegree)} {x y : V}
set_option maxHeartbeats 3000000

theorem highColours_card_le_excluding_root (hcm : IsColMinus c x y) (q : ℝ) :
    (highColours c q y).card≤
      ((G.neighborFinset y).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card := by
  let L := (G.neighborFinset y).filter fun z => z≠x ∧ q≤(G.degree z:ℝ) ∧
    ∃η,c.col y z=some η
  have hcard : L.card=(highColours c q y).card := by
    apply card_leaves_eq_card_colours y L (highColours c q y)
    · intro z hz
      obtain ⟨_,_,hzq,η,hcol⟩ := mem_filter.mp hz
      exact ⟨η,(mem_highColours c q y η).mpr ⟨z,hcol,hzq⟩,hcol⟩
    · intro η hη
      obtain ⟨z,hcol,hzq⟩ := (mem_highColours c q y η).mp hη
      have hzx : z≠x := by
        intro he
        subst z
        rw [c.col_symm,hcm.uncol] at hcol
        cases hcol
      exact ⟨z,mem_filter.mpr ⟨(mem_neighborFinset G y z).mpr (c.col_adj hcol),
        hzx,hzq,η,hcol⟩,hcol⟩
  rw [←hcard]
  apply card_le_card
  intro z hz
  obtain ⟨hzN,hzx,hzq,_⟩ := mem_filter.mp hz
  exact mem_filter.mpr ⟨hzN,hzx,hzq⟩

theorem missing_root_subset_highColours (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (q : ℝ) (hroom : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    missing c x⊆highColours c q y := by
  intro η hη
  have hfree := mem_missing.mp hη
  have hn : ¬c.IsFree y η := fun hy => (hcm.ab_facts hG).1 η hfree hy
  obtain ⟨z,hcol⟩ : ∃z,c.col y z=some η := by
    simpa only [IsFree,not_forall,not_not] using hn
  have hd := CaoChenDistanceFour.spine_degree_sum_lower hG hcm hcol hfree
  have hdR : (G.maxDegree:ℝ)+2≤(G.degree x:ℝ)+(G.degree z:ℝ) := by exact_mod_cast hd
  exact (mem_highColours c q y η).mpr ⟨z,hcol,by linarith⟩

/-- This is stronger than the highCount version: the initial vertex x
is excluded, exactly as in sigma_q(x,y) in the paper. -/
theorem sigma_ge_missing_add_paletteB (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (q : ℝ) (hroom : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    (missing c x).card+(paletteB c q x y).card≤
      ((G.neighborFinset y).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card := by
  have hd : Disjoint (missing c x) (paletteB c q x y) := by
    apply Finset.disjoint_left.mpr
    intro η hm hb
    have hp := ((mem_paletteB c q x y η).mp hb).1
    exact (mem_presentColours c x η).mp hp (mem_missing.mp hm)
  have hsub : missing c x ∪ paletteB c q x y⊆highColours c q y := by
    intro η hη
    rcases mem_union.mp hη with hm|hb
    · exact missing_root_subset_highColours hG hcm q hroom hm
    · exact (mem_highColours c q y η).mpr ((mem_paletteB c q x y η).mp hb).2
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hd] at hc
  exact hc.trans (highColours_card_le_excluding_root hcm q)

theorem highCount_ge_missing_add_paletteB (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (q : ℝ) (hroom : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    (missing c x).card+(paletteB c q x y).card≤highCount G q y := by
  apply (sigma_ge_missing_add_paletteB hG hcm q hroom).trans
  apply card_le_card
  intro z hz
  obtain ⟨hzN,_,hzq⟩ := mem_filter.mp hz
  exact mem_filter.mpr ⟨hzN,hzq⟩

theorem paletteB_card_add_two_le_degree (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (q : ℝ) : (paletteB c q x y).card+2≤G.degree x := by
  have hd : Disjoint (paletteB c q x y) (missing c y) := by
    apply Finset.disjoint_left.mpr
    intro η hb hm
    obtain ⟨_,z,hcol,_⟩ := (mem_paletteB c q x y η).mp hb
    exact mem_missing.mp hm z hcol
  have hsub : paletteB c q x y ∪ missing c y⊆presentColours c x := by
    intro η hη
    rcases mem_union.mp hη with hb|hm
    · exact ((mem_paletteB c q x y η).mp hb).1
    · apply (mem_presentColours c x η).mpr
      intro hx
      exact (hcm.ab_facts hG).1 η hx (mem_missing.mp hm)
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hd] at hc
  have hp : (presentColours c x).card=(colNbrs c x).card :=
    CommonMissingColour.present_colour_card G.maxDegree c x
  have hx := hcm.card_colNbrs x
  simp only [true_or,if_true] at hx
  have hy := hcm.card_missing_end (Or.inr rfl : y=x ∨ y=y)
  have hyD := G.degree_le_maxDegree y
  omega

/-- A genuine minimizer over every neighbour and every edge-deleted
colouring, with no finite-PEC premise. -/
theorem exists_minimal_paletteB (hcrit : IsDeltaCritical G) (x : V) (q : ℝ)
    (hx : 0<G.degree x) :
    ∃ y : V,∃ c : PEC G (Fin G.maxDegree),IsColMinus c x y ∧
      ∀ (v : V) (d : PEC G (Fin G.maxDegree)),IsColMinus d x v →
        (paletteB c q x y).card≤(paletteB d q x v).card := by
  obtain ⟨y,hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hx
  obtain ⟨c,hcm⟩ := exists_colMinus_of_colorable hxy
    (hcrit.2.2 s(x,y) ((mem_edgeSet G).mpr hxy))
  let P : ℕ → Prop := fun p => ∃ y : V,∃ c : PEC G (Fin G.maxDegree),
    IsColMinus c x y ∧ (paletteB c q x y).card=p
  have hp : ∃p,P p := ⟨(paletteB c q x y).card,y,c,hcm,rfl⟩
  obtain ⟨y,c,hcm,heq⟩ := Nat.find_spec hp
  refine ⟨y,c,hcm,?_⟩
  intro v d hd
  by_contra hn
  have hlt : (paletteB d q x v).card<Nat.find hp := by omega
  exact Nat.find_min hp hlt ⟨v,d,hd,rfl⟩

/-- The real minimum-palette construction proves Claim 3.2 property (2)
uniformly at every neighbour.  Sigma is the concrete high-neighbour
count excluding x.  The same witness also satisfies p≤d(x)-2. -/
theorem exists_minimal_paletteB_uniform_sigma (hcrit : IsDeltaCritical G)
    (x : V) (q : ℝ) (hx : 0<G.degree x)
    (hroom : (G.degree x:ℝ)+q≤(G.maxDegree:ℝ)) :
    ∃ y : V,∃ c : PEC G (Fin G.maxDegree),IsColMinus c x y ∧
      (paletteB c q x y).card≤G.degree x-2 ∧
      (∀ (v : V) (d : PEC G (Fin G.maxDegree)),IsColMinus d x v →
        (paletteB c q x y).card≤(paletteB d q x v).card) ∧
      ∀ v : V,G.Adj x v →
        G.maxDegree-G.degree x+1+(paletteB c q x y).card≤
          ((G.neighborFinset v).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card ∧
        q<(((G.neighborFinset v).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card:ℝ) := by
  obtain ⟨y,c,hcm,hmin⟩ := exists_minimal_paletteB hcrit x q hx
  have hsmall := paletteB_card_add_two_le_degree hcrit.2.1 hcm q
  refine ⟨y,c,hcm,by omega,hmin,?_⟩
  intro v hxv
  obtain ⟨d,hd⟩ := exists_colMinus_of_colorable hxv
    (hcrit.2.2 s(x,v) ((mem_edgeSet G).mpr hxv))
  have hlocal := sigma_ge_missing_add_paletteB hcrit.2.1 hd q hroom
  have hmissing := hd.card_missing_end (Or.inl rfl : x=x ∨ x=v)
  have hmax := G.degree_le_maxDegree x
  have hmissing_eq : (missing d x).card=G.maxDegree-G.degree x+1 := by omega
  have hp := hmin v d hd
  rw [hmissing_eq] at hlocal
  have hbound : G.maxDegree-G.degree x+1+(paletteB c q x y).card≤
      ((G.neighborFinset v).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card := by omega
  refine ⟨hbound,?_⟩
  have hbase : G.maxDegree-G.degree x+1≤
      ((G.neighborFinset v).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card := by omega
  have hbaseR : ((G.maxDegree-G.degree x+1:ℕ):ℝ)≤
      (((G.neighborFinset v).filter fun z => z≠x ∧ q≤(G.degree z:ℝ)).card:ℝ) := by
    exact_mod_cast hbase
  have he : ((G.maxDegree-G.degree x+1:ℕ):ℝ)+(G.degree x:ℝ)=(G.maxDegree:ℝ)+1 := by
    exact_mod_cast (show G.maxDegree-G.degree x+1+G.degree x=G.maxDegree+1 by omega)
  linarith

end OverfullWork.CaoChenMinimalPalette
