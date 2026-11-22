module

public import OverfullWork.CaoChenSecondDischarge

@[expose] public section


/-! # Distinct second-discharge donors indexed by missing colours

The structural conclusion of Cao--Chen Theorem 2 is needed only to
certify eligibility of the neighbours carrying a missing colour. Their
existence, distinctness, radius-two incidence and required cardinality
are proved here from the actual partial colouring and critical edge.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset LeanPool.Vizing LeanPool.Vizing.PEC Overfull
open scoped Classical
variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : PEC G (Fin G.maxDegree)} {x y : V}
set_option maxHeartbeats 2000000

/-- Each missing colour produces a different eligible donor; adjacency
between the donor and the receiver causes no difficulty for our R2. -/
theorem missing_colours_le_eligibleDonors (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (d C : ℕ)
    (hstruct : ∀α,c.IsFree x α → ∀v,c.col y v=some α → EligibleDonor G d C v) :
    (missing c x).card≤(eligibleDonors G d C x).card := by
  have hex : ∀α : ↥(missing c x),∃v : V,c.col y v=some α.val := by
    intro α
    have hfree := mem_missing.mp α.property
    have hnot := (hcm.ab_facts hG).1 α.val hfree
    simpa only [IsFree,not_forall,not_not] using hnot
  choose f hf using hex
  have hmem : ∀α : ↥(missing c x),f α∈eligibleDonors G d C x := by
    intro α
    apply mem_filter.mpr
    refine ⟨mem_univ _,hstruct α.val (mem_missing.mp α.property) (f α) (hf α),?_⟩
    have hne : x≠f α := by
      intro he
      have hh := hf α
      rw [←he,c.col_symm,hcm.uncol] at hh
      cases hh
    exact mem_radiusTwo_of_two_step G (c.col_adj (hf α)).symm hcm.adj.symm hne
  let g : ↥(missing c x) → ↥(eligibleDonors G d C x) := fun α => ⟨f α,hmem α⟩
  have hinj : Function.Injective g := by
    intro α β he
    have hv : f α=f β := congrArg Subtype.val he
    apply Subtype.ext
    apply Option.some.inj
    exact (hf α).symm.trans (by rw [hv];exact hf β)
  have hc := Fintype.card_le_of_injective g hinj
  simpa only [Fintype.card_coe] using hc

/-- The required count for a low vertex, obtained from its actual
missing palette rather than postulated as a separate counting input. -/
theorem required_eligibleDonors_of_coloured_neighbours
    (hG : IsClassTwo G) (hcm : IsColMinus c x y) (d C : ℕ) (hx : G.degree x<d)
    (hstruct : ∀α,c.IsFree x α → ∀v,c.col y v=some α → EligibleDonor G d C v) :
    G.maxDegree-d+1≤(eligibleDonors G d C x).card := by
  have hc := missing_colours_le_eligibleDonors hG hcm d C hstruct
  have hm := hcm.card_missing_end (Or.inl rfl)
  have hd := G.degree_le_maxDegree x
  omega

theorem R2_low_charge_of_coloured_neighbours
    (hG : IsClassTwo G) (hcm : IsColMinus c x y) (q : ℝ) (hq : 0≤q)
    (d C : ℕ) (hx : G.degree x<d)
    (hstruct : ∀α,c.IsFree x α → ∀v,c.col y v=some α → EligibleDonor G d C v) :
    (G.maxDegree:ℝ)-(d:ℝ)+1≤R2Charge G q d C x :=
  R2_low_charge_ge_required G q hq d C hx
    (required_eligibleDonors_of_coloured_neighbours hG hcm d C hx hstruct)

/-- Global assembly in a critical graph, with actual deleted-edge
colourings constructed from criticality. The remaining structural input
is exactly eligibility of their missing-colour neighbours, not an assumed
donor count or an assumed average-degree bound. -/
theorem critical_average_from_R1_and_coloured_neighbours
    (hcrit : IsDeltaCritical G) (hactive : ∀x,0<G.degree x)
    (ε : ℝ) (hε : 0<ε) (hεone : ε<1) (d C : ℕ) (hd : 1≤d)
    (hcap : (C:ℝ)≤ε*(G.maxDegree:ℝ)/2)
    (hsmall : ((d-1:ℕ):ℝ)≤ε*(G.maxDegree:ℝ))
    (hR1 : ∀v,d≤G.degree v → (1-ε/2)*(G.maxDegree:ℝ)≤
      R1Charge G ((1-ε/2)*(G.maxDegree:ℝ)) v)
    (hstruct : ∀x y : V,∀φ : PEC G (Fin G.maxDegree),G.degree x<d → G.Adj x y →
      IsColMinus φ x y → ∀α,φ.IsFree x α → ∀v,φ.col y v=some α → EligibleDonor G d C v) :
    (1-ε)*(G.maxDegree:ℝ)*(Fintype.card V:ℝ)≤∑v : V,(G.degree v:ℝ) := by
  apply average_degree_from_R1_and_R2_donors G ε hε hεone d C hd hcap hsmall hR1
  intro v hv
  obtain ⟨w,hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (hactive v)
  obtain ⟨φ,hφ⟩ := exists_colMinus_of_colorable hvw
    (hcrit.2.2 s(v,w) ((mem_edgeSet G).mpr hvw))
  exact required_eligibleDonors_of_coloured_neighbours hcrit.2.1 hφ d C hv
    (hstruct v w φ hv hvw hφ)

end OverfullWork.CaoChenDischarging
