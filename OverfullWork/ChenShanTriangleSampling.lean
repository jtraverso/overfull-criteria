module

public import OverfullWork.ChenShanTriangleSamplingMass
public import OverfullWork.IndependentBernoulliSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real Filter IndependentBernoulliSampling
open scoped Classical Topology

variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {E : A → B → Prop} {L : A → W → Prop} {R : B → W → Prop}

/-- The sampling step in (4.15), with the explicit union-bound hypothesis. -/
theorem exists_triangle_sample_of_union_bound
    (h : BoundedFractionalTriangleDecomposition E L R)
    (hd : 1 ≤ (Fintype.card W : ℝ) / 3)
    (hUnion : ((tripartiteArcs E L R).card : ℝ) *
      (2 * exp (-(((Fintype.card W : ℝ) / 3) ^ (1 / 3 : ℝ) / 4))) < 1) :
    ∃ T ⊆ supportedTriangles E L R, ∀ e ∈ tripartiteArcs E L R,
      |(((triangleHypergraph T).filter (fun t => e ∈ t)).card : ℝ) -
        (Fintype.card W : ℝ) / 3| ≤ ((Fintype.card W : ℝ) / 3) ^ (2 / 3 : ℝ) := by
  obtain ⟨ω,hω,hMargins,hBound⟩ := h
  let d : ℝ := (Fintype.card W : ℝ) / 3
  let C := supportedTriangles E L R
  let G := tripartiteArcs E L R
  let p : C → ℝ := fun t => d * ω t.val.1 t.val.2.1 t.val.2.2
  let S : G → Finset C := fun e => univ.filter (fun t => e.val ∈ triangleEdges t.val)
  have hd0 : 0 < d := lt_of_lt_of_le zero_lt_one hd
  have hk : 0 < (Fintype.card W : ℝ) := by
    dsimp only [d] at hd0
    linarith only [hd0]
  have hp (t : C) : 1 / 6 ≤ p t ∧ p t ≤ 1 / 2 := by
    have ht := (mem_filter.mp t.property).2
    exact triangle_retention_probability_bounds hk (hBound _ _ _ ht.1 ht.2.1 ht.2.2)
  have hMean (e : G) : mean p (S e) = d := by
    let U := C.filter (fun t => e.val ∈ triangleEdges t)
    let incl : U ↪ C := ⟨fun t => ⟨t.val,(mem_filter.mp t.property).1⟩,
      fun _ _ hEq => Subtype.ext (congrArg (fun t : C => t.val) hEq)⟩
    have hS : S e = U.attach.map incl := by
      ext t
      constructor
      · intro ht
        have ht' : t.val ∈ U := mem_filter.mpr ⟨t.property,(mem_filter.mp ht).2⟩
        exact mem_map.mpr ⟨⟨t.val,ht'⟩,mem_attach _ _,Subtype.ext rfl⟩
      · intro ht
        obtain ⟨u,_,rfl⟩ := mem_map.mp ht
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp u.property).2⟩
    rw [mean,hS,sum_map]
    change (∑ t ∈ U.attach, d * ω t.val.1 t.val.2.1 t.val.2.2) = d
    rw [sum_attach U (fun t => d * ω t.1 t.2.1 t.2.2)]
    exact triangle_retention_mass_eq ω hω hMargins e.val e.property
  let ε := d ^ (-(1 / 3) : ℝ)
  have hε : 0 ≤ ε := rpow_nonneg hd0.le _
  have hε' : ε ≤ 2 := (rpow_le_one_of_one_le_of_nonpos hd (by norm_num)).trans (by norm_num)
  have hPower₁ : ε ^ 2 * d = d ^ (1 / 3 : ℝ) := by
    change (d ^ (-(1 / 3) : ℝ)) ^ 2 * d = _
    rw [pow_two,← rpow_add hd0]
    conv_lhs => rhs; rw [← rpow_one d]
    rw [← rpow_add hd0]
    congr 1
    norm_num
  have hPower₂ : ε * d = d ^ (2 / 3 : ℝ) := by
    change d ^ (-(1 / 3) : ℝ) * d = _
    conv_lhs => rhs; rw [← rpow_one d]
    rw [← rpow_add hd0]
    congr 1
    norm_num
  obtain ⟨s,hs⟩ := exists_simultaneous_count p
    (fun t => (by norm_num : 0 ≤ (1 / 6 : ℝ)).trans (hp t).1)
    (fun t => (hp t).2.trans (by norm_num)) S d hMean hε hε' (by
      rw [hPower₁,Fintype.card_coe]
      exact hUnion)
  let T := (univ.filter fun t : C => s t).map ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨T,?_,?_⟩
  · intro t ht
    obtain ⟨u,_,rfl⟩ := mem_map.mp ht
    exact u.property
  · intro e he
    have hCount : ((T.filter (fun t => e ∈ triangleEdges t)).card : ℝ) =
        count (S ⟨e,he⟩) s := by
      simp only [T,count,filter_map,card_map,S,filter_filter]
      congr 2
      ext t
      simp [and_comm]
    rw [triangleHypergraph_degree_eq,hCount,← hPower₂]
    exact hs ⟨e,he⟩

/-- The polynomial number of edge tests is dominated by the Chernoff bound. -/
private theorem eventually_triangle_union_bound :
    ∀ᶠ d : ℝ in atTop, 216 * d ^ 2 * exp (-(d ^ (1 / 3 : ℝ) / 4)) < 1 := by
  have hLimit := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 6 (1/4) (by norm_num)).comp
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 3 : ℝ)))
  have hSmall := hLimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/216))
  filter_upwards [hSmall,eventually_ge_atTop (0 : ℝ)] with d hSmall hd
  change (d ^ (1 / 3 : ℝ)) ^ (6 : ℝ) *
    exp (-(1/4) * d ^ (1 / 3 : ℝ)) < 1/216 at hSmall
  rw [← rpow_mul hd, show (1/3 : ℝ) * 6 = 2 by norm_num,
    show d ^ (2 : ℝ) = d ^ 2 by norm_cast] at hSmall
  rw [show -(d ^ (1 / 3 : ℝ) / 4) = -(1/4) * d ^ (1 / 3 : ℝ) by ring]
  linarith only [hSmall]

/-- Chen–Shan (4.15). One threshold works for all balanced tripartite
graphs of the given sizes and all decompositions satisfying (4.10). -/
theorem exists_triangle_sample_threshold :
    ∃ m₀ : ℕ, ∀ (m : ℕ), m₀ ≤ m →
    ∀ (A B W : Type*) [Fintype A] [Fintype B] [Fintype W]
      (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop),
    Fintype.card A = m → Fintype.card B = m → m ≤ 2 * Fintype.card W →
    TripartiteLocallyBalanced E L R → BoundedFractionalTriangleDecomposition E L R →
    ∃ T ⊆ supportedTriangles E L R, ∀ e ∈ tripartiteArcs E L R,
      |(((triangleHypergraph T).filter (fun t => e ∈ t)).card : ℝ) -
        (Fintype.card W : ℝ) / 3| ≤ ((Fintype.card W : ℝ) / 3) ^ (2 / 3 : ℝ) := by
  obtain ⟨D,hD⟩ := eventually_atTop.mp eventually_triangle_union_bound
  obtain ⟨m₀,hm₀⟩ := exists_nat_gt (6 * max (1 : ℝ) D)
  refine ⟨m₀,?_⟩
  intro m hm A B W _ _ _ E L R hA hB hW hb hω
  let d : ℝ := (Fintype.card W : ℝ) / 3
  have hmd : (m : ℝ) ≤ 6 * d := by
    have hk : (m : ℝ) ≤ 2 * (Fintype.card W : ℝ) := by exact_mod_cast hW
    dsimp only [d]
    linarith only [hk]
  have hm' : (m₀ : ℝ) ≤ m := by exact_mod_cast hm
  have hmax : max (1 : ℝ) D ≤ d := by linarith only [hm₀,hm',hmd]
  have hd : 1 ≤ d := (le_max_left _ _).trans hmax
  have hD' := hD d ((le_max_right _ _).trans hmax)
  apply exists_triangle_sample_of_union_bound hω hd
  have hCard : ((tripartiteArcs E L R).card : ℝ) ≤ 3 * (m : ℝ) * m := by
    exact_mod_cast tripartite_arc_count_le_three_sq hA hB hb
  have hSquare : (m : ℝ) ^ 2 ≤ (6 * d) ^ 2 := by gcongr
  have hCard' : ((tripartiteArcs E L R).card : ℝ) ≤ 108 * d ^ 2 := by
    nlinarith only [hCard,hSquare]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCard' (by positivity)) ?_
  convert hD' using 1
  ring

end OverfullWork.ChenShan
