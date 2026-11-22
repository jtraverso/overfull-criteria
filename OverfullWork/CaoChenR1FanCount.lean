module

public import OverfullWork.CaoChenDischarging

@[expose] public section


/-! # The low multifan count in Cao--Chen Claim 3.1

For a colouring of G-xy, edges at y whose colours are missing at x form
a direct multifan. Its missing-colour sets are disjoint. Counting those
sets proves property (1) in Case 2 of Claim 3.1 of Cao--Chen (2018).
This is an actual adjacency/counting input for R1, not an assumption on
the final discharged charge.
-/
namespace OverfullWork.CaoChenDischarging
open SimpleGraph Finset LeanPool.Vizing LeanPool.Vizing.PEC Overfull
open scoped Classical
variable {V : Type*} [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : PEC G (Fin G.maxDegree)} {x y : V}
set_option maxHeartbeats 3000000

private theorem leaf_ne_initial (hcm : IsColMinus c x y) {u : V} {γ : Fin G.maxDegree}
    (hu : c.col y u=some γ) : u≠x := by
  intro he
  subst u
  rw [c.col_symm,hcm.uncol] at hu
  cases hu

/-- Two direct multifan leaves have disjoint missing-colour sets. -/
theorem direct_fan_leaves_disjoint (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    {u v : V} (hne : u≠v)
    (hu : ∃α,c.col y u=some α ∧ c.IsFree x α)
    (hv : ∃β,c.col y v=some β ∧ c.IsFree x β) :
    Disjoint (missing c u) (missing c v) := by
  obtain ⟨α,hα,hαfree⟩ := hu
  obtain ⟨β,hβ,hβfree⟩ := hv
  have hux := leaf_ne_initial hcm hα
  have hvx := leaf_ne_initial hcm hβ
  let f : ℕ → V := fun i => if i=0 then x else if i=1 then u else v
  have hF : IsMultifan c y 3 f := by
    refine ⟨by omega,?_,?_,?_,?_⟩
    · simpa only [f,if_pos rfl] using hcm.symm.uncol
    · intro i hi
      rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl|rfl|rfl
      · simpa [f] using hcm.adj.symm
      · simpa [f] using c.col_adj hα
      · simpa [f] using c.col_adj hβ
    · intro i hi j hj hij
      rcases (by omega : i=0 ∨ i=1 ∨ i=2) with rfl|rfl|rfl <;>
        rcases (by omega : j=0 ∨ j=1 ∨ j=2) with rfl|rfl|rfl <;>
        simp_all [f]
    · intro i hi hi3
      rcases (by omega : i=1 ∨ i=2) with rfl|rfl
      · exact ⟨0,by omega,α,by simpa [f] using hα,by simpa [f] using hαfree⟩
      · exact ⟨0,by omega,β,by simpa [f] using hβ,by simpa [f] using hβfree⟩
  have hcm' : IsColMinus c y (f 0) := by simpa [f] using hcm.symm
  have he := (multifan_elementary hG 3 c y f hcm' hF).2.1
    1 (by omega) 2 (by omega) (by omega)
  apply Finset.disjoint_left.mpr
  intro γ huγ hvγ
  apply he γ
  · simpa [f] using (mem_missing.mp huγ)
  · simpa [f] using (mem_missing.mp hvγ)

/-- Counting the missing palettes of the initial vertex and all direct
fan leaves consumes at most the whole Delta-colour palette. -/
theorem direct_fan_missing_sum_le (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (Z : Finset V)
    (hZ : ∀z∈Z,∃α,c.col y z=some α ∧ c.IsFree x α) :
    (missing c x).card+(∑z∈Z,(missing c z).card)≤G.maxDegree := by
  have hx : x∉Z := by
    intro hxZ
    obtain ⟨α,hα,_⟩ := hZ x hxZ
    exact leaf_ne_initial hcm hα rfl
  have hp : Set.PairwiseDisjoint (↑(insert x Z):Set V) (fun z => missing c z) := by
    intro u hu v hv hne
    rcases mem_insert.mp hu with rfl|huZ
    · obtain ⟨β,hβ,hβfree⟩ := hZ v ((mem_insert.mp hv).resolve_left hne.symm)
      have he := (fan_bau hG hcm hβ hβfree hne).1
      apply Finset.disjoint_left.mpr
      intro γ hxγ hvγ
      exact he γ (mem_missing.mp hxγ) (mem_missing.mp hvγ)
    · rcases mem_insert.mp hv with rfl|hvZ
      · obtain ⟨α,hα,hαfree⟩ := hZ u huZ
        have he := (fan_bau hG hcm hα hαfree hne.symm).1
        apply Finset.disjoint_left.mpr
        intro γ huγ hxγ
        exact he γ (mem_missing.mp hxγ) (mem_missing.mp huγ)
      · exact direct_fan_leaves_disjoint hG hcm hne (hZ u huZ) (hZ v hvZ)
  have hb : ((insert x Z).biUnion fun z => missing c z).card≤G.maxDegree := by
    simpa only [card_univ,Fintype.card_fin] using
      card_le_card (subset_univ ((insert x Z).biUnion fun z => missing c z))
  rw [card_biUnion hp,sum_insert hx] at hb
  exact hb

/-- Integer threshold form of the low-leaf count, including the extra
missing colour at the initial endpoint of the deleted edge. -/
theorem direct_low_fan_count (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (Z : Finset V) (t : ℕ) (ht : t≤G.maxDegree) (hx : G.degree x≤t)
    (hZ : ∀z∈Z,(∃α,c.col y z=some α ∧ c.IsFree x α) ∧ G.degree z≤t) :
    (Z.card+1)*(G.maxDegree-t)+1≤G.maxDegree := by
  have hb := direct_fan_missing_sum_le hG hcm Z (fun z hz => (hZ z hz).1)
  have hxc := hcm.card_missing_end (Or.inl rfl)
  have hxlow : G.maxDegree-t+1≤(missing c x).card := by omega
  have hzlow : ∀z∈Z,G.maxDegree-t≤(missing c z).card := by
    intro z hz
    obtain ⟨⟨α,hα,_⟩,hzt⟩ := hZ z hz
    have hzx := leaf_ne_initial hcm hα
    have hzy : z≠y := (c.col_adj hα).ne.symm
    have hzc := hcm.card_missing_other hzx hzy
    omega
  have hs := sum_le_sum hzlow
  rw [sum_const,Nat.nsmul_eq_mul] at hs
  nlinarith only [hb,hxlow,hs]

/-- Property (1) of Claim 3.1, in its precise real-threshold form. -/
theorem direct_low_fan_real_count (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (Z : Finset V) (ε : ℝ) (_hε : 0<ε)
    (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ))
    (hZ : ∀z∈Z,(∃α,c.col y z=some α ∧ c.IsFree x α) ∧
      (G.degree z:ℝ)<(1-ε)*(G.maxDegree:ℝ)) :
    ε*((Z.card:ℝ)+1)<1 := by
  have hb := direct_fan_missing_sum_le hG hcm Z (fun z hz => (hZ z hz).1)
  have hbR : ((missing c x).card:ℝ)+(∑z∈Z,((missing c z).card:ℝ))≤(G.maxDegree:ℝ) := by
    exact_mod_cast hb
  have hxc := hcm.card_missing_end (Or.inl rfl)
  have hxcR : ((missing c x).card:ℝ)+(G.degree x:ℝ)=(G.maxDegree:ℝ)+1 := by exact_mod_cast hxc
  have hxmissing : ε*(G.maxDegree:ℝ)<((missing c x).card:ℝ) := by nlinarith only [hxcR,hx]
  have hzmissing : ∀z∈Z,ε*(G.maxDegree:ℝ)≤((missing c z).card:ℝ) := by
    intro z hz
    obtain ⟨⟨α,hα,_⟩,hzt⟩ := hZ z hz
    have hzx := leaf_ne_initial hcm hα
    have hzy : z≠y := (c.col_adj hα).ne.symm
    have hzc := hcm.card_missing_other hzx hzy
    have hzcR : ((missing c z).card:ℝ)+(G.degree z:ℝ)=(G.maxDegree:ℝ) := by exact_mod_cast hzc
    nlinarith only [hzcR,hzt]
  have hs := sum_le_sum hzmissing
  rw [sum_const,nsmul_eq_mul] at hs
  have hD : (0:ℝ)<(G.maxDegree:ℝ) := by
    have hd : 0<G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨y,hcm.adj⟩
    have hpos : 0<G.maxDegree := hd.trans_le (G.degree_le_maxDegree x)
    exact_mod_cast hpos
  nlinarith only [hbR,hxmissing,hs,hD]

/-- The low leaves whose incident colour at y is missing at x, as used
in the set C_y(phi) in Claim 3.1. Properness identifies leaves and colours. -/
noncomputable def lowStarLeaves (c : PEC G (Fin G.maxDegree)) (x y : V) (q : ℝ) : Finset V :=
  (G.neighborFinset y).filter fun z => (G.degree z:ℝ)<q ∧
    ∃α,c.col y z=some α ∧ c.IsFree x α

theorem lowStarLeaves_count (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ)) :
    ε*((lowStarLeaves c x y ((1-ε)*(G.maxDegree:ℝ))).card+1)<1 := by
  apply direct_low_fan_real_count hG hcm _ ε hε hx
  intro z hz
  obtain ⟨_,hzlow,hzstar⟩ := mem_filter.mp hz
  exact ⟨hzstar,hzlow⟩

theorem lowStarLeaves_card_lt_ratio (hG : IsClassTwo G) (hcm : IsColMinus c x y)
    (ε : ℝ) (hε : 0<ε) (hx : (G.degree x:ℝ)<(1-ε)*(G.maxDegree:ℝ)) :
    ((lowStarLeaves c x y ((1-ε)*(G.maxDegree:ℝ))).card:ℝ)<(1-ε)/ε := by
  have hh := lowStarLeaves_count hG hcm ε hε hx
  apply (lt_div_iff₀ hε).mpr
  nlinarith only [hh]

end OverfullWork.CaoChenDischarging
