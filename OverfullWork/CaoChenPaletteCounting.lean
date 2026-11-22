module

public import OverfullWork.CaoChenR1FanCount
public import OverfullWork.CaoChenPalettes

@[expose] public section


/-! # Concrete palette counts for Cao--Chen Claim 3.1

All counts concern an actual proper partial edge colouring.  They do
not assume any lower bound for the final discharged charge.
-/
namespace OverfullWork.CaoChenPaletteCounting
open SimpleGraph Finset LeanPool.Vizing LeanPool.Vizing.PEC Overfull
open CaoChenDischarging CaoChenPalettes
open scoped Classical
variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : PEC G (Fin G.maxDegree)} {x y : V}
set_option maxHeartbeats 3000000

/-- Properness gives a bijection between any chosen family of coloured
incident edges and its actual palette of colours. -/
theorem card_leaves_eq_card_colours (v : V) (L : Finset V)
    (P : Finset (Fin G.maxDegree))
    (hL : ∀u∈L,∃η∈P,c.col v u=some η)
    (hP : ∀η∈P,∃u∈L,c.col v u=some η) : L.card=P.card := by
  have himage : L.image (c.col v)=P.image some := by
    apply subset_antisymm
    · intro o ho
      obtain ⟨u,hu,rfl⟩ := mem_image.mp ho
      obtain ⟨η,hη,hcol⟩ := hL u hu
      exact mem_image.mpr ⟨η,hη,hcol.symm⟩
    · intro o ho
      obtain ⟨η,hη,rfl⟩ := mem_image.mp ho
      obtain ⟨u,hu,hcol⟩ := hP η hη
      exact mem_image.mpr ⟨u,hu,hcol⟩
  have hinj : Set.InjOn (c.col v) (L : Set V) := by
    intro u hu w _ he
    obtain ⟨η,_,hcol⟩ := hL u hu
    exact c.col_proper hcol (he.symm.trans hcol)
  have hc := congrArg Finset.card himage
  rw [card_image_of_injOn hinj,card_image_of_injective _ (Option.some_injective _)] at hc
  exact hc

/-- At every vertex other than x, the deleted edge xy cannot remove an
edge to a high vertex when x itself lies below the threshold. -/
theorem high_neighbour_coloured (hcm : IsColMinus c x y) (q : ℝ)
    (hx : (G.degree x:ℝ)<q) {z w : V} (hz : z≠x)
    (hzw : G.Adj z w) (hw : q≤(G.degree w:ℝ)) :
    ∃η,c.col z w=some η := by
  have hne : s(z,w)≠s(x,y) := by
    intro he
    rcases Sym2.eq_iff.mp he with ⟨hzx,_⟩|⟨_,hwx⟩
    · exact hz hzx
    · subst w
      linarith
  exact Option.ne_none_iff_exists'.mp (hcm.total z w hzw hne)

/-- When x is low, excluding x from the high-neighbour count changes
nothing.  The right side is the paper's sigma_q(x,z). -/
theorem highCount_eq_excluding_low_vertex (q : ℝ) (hx : (G.degree x:ℝ)<q) (z : V) :
    highCount G q z=
      ((G.neighborFinset z).filter fun w => w≠x ∧ q≤(G.degree w:ℝ)).card := by
  unfold highCount
  congr 1
  ext w
  simp only [mem_filter]
  constructor
  · intro h
    refine ⟨h.1,?_,h.2⟩
    intro he
    subst w
    linarith
  · intro h
    exact ⟨h.1,h.2.2⟩

/-- The concrete R1 donation is bounded below from a high-neighbour
count.  The denominator is positive because the donor has a low neighbour. -/
theorem donation_ge_of_high_count_bound (q B : ℝ) (hB : 0<B)
    (hroom : q+B<(G.maxDegree:ℝ)) {z : V} (hxz : G.Adj x z)
    (hx : (G.degree x:ℝ)<q)
    (hhigh : (G.maxDegree:ℝ)-B≤(highCount G q z:ℝ)) :
    ((G.maxDegree:ℝ)-B-q)/B≤donation G q z := by
  have hsum := lowCount_add_highCount G q z
  have hsumR : (lowCount G q z:ℝ)+(highCount G q z:ℝ)=(G.degree z:ℝ) := by
    exact_mod_cast hsum
  have hdeg : (G.degree z:ℝ)≤(G.maxDegree:ℝ) := by
    exact_mod_cast G.degree_le_maxDegree z
  have hlow : (lowCount G q z:ℝ)≤B := by linarith
  have hsource : (G.maxDegree:ℝ)-B≤(G.degree z:ℝ) := by
    have hn : (0:ℝ)≤(lowCount G q z:ℝ) := Nat.cast_nonneg _
    linarith
  have hpos : (0:ℝ)<(lowCount G q z:ℝ) := by
    exact_mod_cast lowCount_positive_of_low_neighbour G q hxz hx
  have hz : q<(G.degree z:ℝ) := by linarith
  rw [donation,if_pos hz]
  apply (div_le_div_iff₀ hB hpos).mpr
  have hm := mul_le_mul_of_nonneg_left hlow
    (show 0≤(G.maxDegree:ℝ)-B-q by linarith)
  nlinarith only [hm,hsource,hB]

theorem highColours_card_eq_highCount (hcm : IsColMinus c x y) (q : ℝ)
    (hx : (G.degree x:ℝ)<q) {z : V} (hz : z≠x) :
    (highColours c q z).card=highCount G q z := by
  symm
  apply card_leaves_eq_card_colours z
    ((G.neighborFinset z).filter fun w => q≤(G.degree w:ℝ)) (highColours c q z)
  · intro w hw
    obtain ⟨hwN,hwq⟩ := mem_filter.mp hw
    obtain ⟨η,hη⟩ := high_neighbour_coloured hcm q hx hz
      ((mem_neighborFinset G z w).mp hwN) hwq
    exact ⟨η,(mem_highColours c q z η).mpr ⟨w,hη,hwq⟩,hη⟩
  · intro η hη
    obtain ⟨w,hw,hwq⟩ := (mem_highColours c q z η).mp hη
    exact ⟨w,mem_filter.mpr ⟨(mem_neighborFinset G z w).mpr (c.col_adj hw),hwq⟩,hw⟩

theorem badColours_card_add_highCount (hcm : IsColMinus c x y) (q : ℝ)
    (hx : (G.degree x:ℝ)<q) {z : V} (hz : z≠x) :
    (badColours c q z).card+highCount G q z=G.maxDegree := by
  have h := bad_card_add_high_card c q z
  rw [highColours_card_eq_highCount hcm q hx hz] at h
  exact h

theorem badColours_card_eq_deficit (hcm : IsColMinus c x y) (q : ℝ)
    (hx : (G.degree x:ℝ)<q) {z : V} (hz : z≠x) :
    (badColours c q z).card=G.maxDegree-highCount G q z := by
  have h := badColours_card_add_highCount hcm q hx hz
  omega

/-- The bad-palette identity with sigma written as its concrete finite
neighbour count, rather than introduced as a new definition. -/
theorem badColours_card_eq_sigma_deficit (hcm : IsColMinus c x y) (q : ℝ)
    (hx : (G.degree x:ℝ)<q) {z : V} (hxz : G.Adj x z) :
    (badColours c q z).card=G.maxDegree-
      ((G.neighborFinset z).filter fun w => w≠x ∧ q≤(G.degree w:ℝ)).card := by
  rw [badColours_card_eq_deficit hcm q hx hxz.ne.symm,
    highCount_eq_excluding_low_vertex q hx z]

/-- A small actual bad palette supplies the R1 donation quota. -/
theorem donation_ge_of_badColours_card_bound (hcm : IsColMinus c x y) (q B : ℝ)
    (hB : 0<B) (hroom : q+B<(G.maxDegree:ℝ)) {z : V} (hxz : G.Adj x z)
    (hx : (G.degree x:ℝ)<q) (hbad : ((badColours c q z).card:ℝ)≤B) :
    ((G.maxDegree:ℝ)-B-q)/B≤donation G q z := by
  apply donation_ge_of_high_count_bound q B hB hroom hxz hx
  have h := badColours_card_add_highCount hcm q hx hxz.ne.symm
  have hr : ((badColours c q z).card:ℝ)+(highCount G q z:ℝ)=(G.maxDegree:ℝ) := by
    exact_mod_cast h
  linarith

theorem neighboursS_card_eq_bad_inter_present (q : ℝ) :
    (neighboursS c q x y).card=(badColours c q y ∩ presentColours c x).card := by
  apply card_leaves_eq_card_colours x (neighboursS c q x y)
    (badColours c q y ∩ presentColours c x)
  · intro z hz
    obtain ⟨_,η,hη,hcol⟩ := mem_filter.mp hz
    have hs := (mem_paletteS_iff_free_or_bad c q x y η).mp hη
    have hn : ¬c.IsFree x η := fun h => h z hcol
    exact ⟨η,mem_inter.mpr ⟨hs.resolve_left hn,
      (presentColours_iff_coloured c x η).mpr ⟨z,hcol⟩⟩,hcol⟩
  · intro η hη
    obtain ⟨hbad,hpresent⟩ := mem_inter.mp hη
    obtain ⟨z,hcol⟩ := (presentColours_iff_coloured c x η).mp hpresent
    exact ⟨z,mem_filter.mpr ⟨(mem_neighborFinset G x z).mpr (c.col_adj hcol),
      η,(mem_paletteS_iff_free_or_bad c q x y η).mpr (Or.inr hbad),hcol⟩,hcol⟩

theorem lowStarLeaves_card_eq_low_inter_missing (q : ℝ) :
    (lowStarLeaves c x y q).card=(lowColours c q y ∩ missing c x).card := by
  apply card_leaves_eq_card_colours y (lowStarLeaves c x y q)
    (lowColours c q y ∩ missing c x)
  · intro z hz
    obtain ⟨_,hzq,η,hcol,hfree⟩ := mem_filter.mp hz
    exact ⟨η,mem_inter.mpr ⟨(mem_lowColours c q y η).mpr ⟨z,hcol,hzq⟩,
      mem_missing.mpr hfree⟩,hcol⟩
  · intro η hη
    obtain ⟨hlow,hmissing⟩ := mem_inter.mp hη
    obtain ⟨z,hcol,hzq⟩ := (mem_lowColours c q y η).mp hlow
    exact ⟨z,mem_filter.mpr ⟨(mem_neighborFinset G y z).mpr (c.col_adj hcol),
      hzq,η,hcol,mem_missing.mp hmissing⟩,hcol⟩

theorem lowStarLeaves_card_eq_bad_inter_missing (hG : IsClassTwo G)
    (hcm : IsColMinus c x y) (q : ℝ) :
    (lowStarLeaves c x y q).card=(badColours c q y ∩ missing c x).card := by
  rw [lowStarLeaves_card_eq_low_inter_missing]
  congr 1
  ext η
  simp only [badColours,mem_inter,mem_union,mem_missing]
  have hd := (hcm.ab_facts hG).1
  exact ⟨fun h => ⟨Or.inr h.1,h.2⟩,
    fun h => ⟨h.1.resolve_left (fun hy => hd η h.2 hy),h.2⟩⟩

/-- Exact property (2) behind Claim 3.1: no constant or inequality is
postulated, and low leaves use the already constructed direct fan. -/
theorem neighboursS_card_add_lowStarLeaves_card (hG : IsClassTwo G)
    (hcm : IsColMinus c x y) (q : ℝ) (hx : (G.degree x:ℝ)<q) :
    (neighboursS c q x y).card+(lowStarLeaves c x y q).card=
      G.maxDegree-highCount G q y := by
  rw [neighboursS_card_eq_bad_inter_present,
    lowStarLeaves_card_eq_bad_inter_missing hG hcm]
  have heq : badColours c q y ∩ presentColours c x=badColours c q y\missing c x := by
    ext η
    simp [presentColours]
  rw [heq,card_sdiff_add_card_inter]
  exact badColours_card_eq_deficit hcm q hx hcm.adj.ne.symm

/-- Property (2) follows from its exact identity and the proved direct
multifan bound, with the real ratio retained instead of rounded. -/
theorem neighboursS_card_gt_deficit_sub_ratio (hG : IsClassTwo G)
    (hcm : IsColMinus c x y) (ε : ℝ) (hε : 0<ε)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ)) :
    ((G.maxDegree-highCount G ((1-ε)*(G.maxDegree:ℝ)) y:ℕ):ℝ)-(1-ε)/ε<
      ((neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y).card:ℝ) := by
  have hi := neighboursS_card_add_lowStarLeaves_card hG hcm
    ((1-ε)*(G.maxDegree:ℝ)) hx
  have hiR : ((neighboursS c ((1-ε)*(G.maxDegree:ℝ)) x y).card:ℝ)+
      ((lowStarLeaves c x y ((1-ε)*(G.maxDegree:ℝ))).card:ℝ)=
      ((G.maxDegree-highCount G ((1-ε)*(G.maxDegree:ℝ)) y:ℕ):ℝ) := by
    exact_mod_cast hi
  have hlow := lowStarLeaves_card_lt_ratio hG hcm ε hε hx
  linarith

/-- The donation quota in Case 2 follows from a small bad palette,
without a hypothesis about the final charge. -/
theorem donation_ge_of_badColours_card_fraction (hcm : IsColMinus c x y)
    (ε ρ : ℝ) (hρ : 0<ρ) (hρε : ρ<ε) {z : V} (hxz : G.Adj x z)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hbad : ((badColours c ((1-ε)*(G.maxDegree:ℝ)) z).card:ℝ)≤ρ*(G.maxDegree:ℝ)) :
    (ε-ρ)/ρ≤donation G ((1-ε)*(G.maxDegree:ℝ)) z := by
  have hD : (0:ℝ)<(G.maxDegree:ℝ) := by
    have hd : 0<G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨z,hxz⟩
    exact_mod_cast hd.trans_le (G.degree_le_maxDegree x)
  have hroom : (1-ε)*(G.maxDegree:ℝ)+ρ*(G.maxDegree:ℝ)<(G.maxDegree:ℝ) := by
    have hm := mul_pos (sub_pos.mpr hρε) hD
    nlinarith only [hm]
  have h := donation_ge_of_badColours_card_bound hcm ((1-ε)*(G.maxDegree:ℝ))
    (ρ*(G.maxDegree:ℝ)) (mul_pos hρ hD) hroom hxz hx hbad
  have he : ((G.maxDegree:ℝ)-ρ*(G.maxDegree:ℝ)-(1-ε)*(G.maxDegree:ℝ))/
      (ρ*(G.maxDegree:ℝ))=(ε-ρ)/ρ := by
    field_simp
    ring
  rwa [he] at h

end OverfullWork.CaoChenPaletteCounting
