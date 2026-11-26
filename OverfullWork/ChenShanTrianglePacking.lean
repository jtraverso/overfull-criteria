module

public import OverfullWork.ChenShanTrianglePackingLeave
public import OverfullWork.ChenShanTriangleSampling
public import OverfullWork.ChenShanEGJTransport

@[expose] public section

namespace OverfullWork.ChenShan

open Finset Real Pseudorandom
open scoped Classical

universe uA uB uW

/-- Apply Ehard–Glock–Joos to a retained triangle family. The real upper
degree bound d + d^(2/3) is permitted by Theorem 1.2. -/
theorem exists_triangle_packing_from_sample :
    ∃ Δ₀ : ℝ, ∀ (A : Type uA) (B : Type uB) (W : Type uW)
      [Fintype A] [Fintype B] [Fintype W]
      (E : A → B → Prop) (L : A → W → Prop) (R : B → W → Prop)
      (T : Finset (A × B × W)) (d : ℝ),
      let G := tripartiteArcs E L R
      let u := d ^ (2/3 : ℝ)
      let Δ := d + u
      1 ≤ d → Δ₀ ≤ Δ →
      T ⊆ supportedTriangles E L R → TripartiteLocallyBalanced E L R →
      (∀ e ∈ G, |(((triangleHypergraph T).filter (fun S => e ∈ S)).card : ℝ) - d| ≤ u) →
      (T.card : ℝ) ≤ exp (Δ ^ ((1/900 : ℝ) ^ 2)) →
      (Fintype.card (A ⊕ B ⊕ W) : ℝ) ≤ exp (Δ ^ ((1/900 : ℝ) ^ 2)) →
      (∀ v, 2 * Δ ^ (3/2 : ℝ) ≤ (d-u) * incidentDegree G v) →
      ∃ M ⊆ T,
        IsMatching (triangleHypergraph M) ∧
        ArcBalanced (packingLeave G (triangleHypergraph M)) ∧
        ∀ v, (incidentDegree (packingLeave G (triangleHypergraph M)) v : ℝ) ≤
          (Δ ^ (-(1/900) : ℝ) + 2 * d ^ (-(1/3) : ℝ)) * incidentDegree G v := by
  obtain ⟨Δ₀,hEGJ⟩ := egj_triangle_matching.{max uA uB uW,max uA uB uW}
  refine ⟨Δ₀,?_⟩
  intro A B W _ _ _ E L R T d G u Δ hd hΔ hT hb hSample hSize hTests hHeavy
  let H := triangleHypergraph T
  let w (v : A ⊕ B ⊕ W) (S : Finset (OrientedTripartiteEdge A B W)) : ℝ :=
    incidentDegree S v
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hu : 0 ≤ u := rpow_nonneg hd0.le _
  have hΔ1 : 1 ≤ Δ := by dsimp only [Δ]; linarith only [hd,hu]
  have hΔ0 : 0 < Δ := zero_lt_one.trans_le hΔ1
  have hSub (S) (hS : S ∈ H) : S ⊆ G := by
    obtain ⟨t,ht,rfl⟩ := mem_map.mp hS
    exact triangleEdges_subset_tripartiteArcs (mem_filter.mp (hT ht)).2
  have hDegree (e : OrientedTripartiteEdge A B W) : (degree H e : ℝ) ≤ Δ := by
    by_cases he : e ∈ G
    · have h := (abs_le.mp (hSample e he)).2
      change (degree H e : ℝ) - d ≤ u at h
      dsimp only [Δ]
      linarith only [h]
    · have hEmpty : H.filter (fun S => e ∈ S) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro S hS
        exact he (hSub S (mem_filter.mp hS).1 (mem_filter.mp hS).2)
      change ((H.filter (fun S => e ∈ S)).card : ℝ) ≤ Δ
      rw [hEmpty,card_empty,Nat.cast_zero]
      exact hΔ0.le
  have hCodegree (e f : OrientedTripartiteEdge A B W) (hef : e ≠ f) :
      (codegree H e f : ℝ) ≤ Δ ^ (1/2 : ℝ) := by
    have h : (codegree H e f : ℝ) ≤ 1 := by
      exact_mod_cast triangleHypergraph_codegree_le_one T e f hef
    exact h.trans (one_le_rpow hΔ1 (by norm_num))
  have hNonneg (v) (S : Finset (OrientedTripartiteEdge A B W)) : 0 ≤ w v S := by
    dsimp only [w]
    positivity
  have hWeight (v) : (d-u) * incidentDegree G v ≤ weight (w v) H := by
    apply mul_incidentDegree_le_sum_incidentDegree G H v (d-u) hSub
    intro e he
    have h := (abs_le.mp (hSample e he)).1
    have hh : d - u ≤ (((triangleHypergraph T).filter (fun S => e ∈ S)).card : ℝ) := by
      linarith only [h]
    dsimp only [H]
    convert hh using 3
    ext S
    simp
  have hLocalHeavy (v) (S) (hS : S ∈ H) :
      w v S * Δ ^ (3/2 : ℝ) ≤ weight (w v) H := by
    have hTwo : w v S ≤ 2 := by
      obtain ⟨t,_,rfl⟩ := mem_map.mp hS
      change (incidentDegree (triangleEdges t) v : ℝ) ≤ 2
      exact_mod_cast triangleEdges_incidentDegree_le_two t v
    exact (mul_le_mul_of_nonneg_right hTwo (rpow_nonneg hΔ0.le _)).trans
      ((hHeavy v).trans (hWeight v))
  obtain ⟨K,hK,hMatch,hApprox⟩ := hEGJ Δ hΔ _ H
    (triangleHypergraph_uniform T) hDegree hCodegree
    (by simpa [H,triangleHypergraph_card] using hSize) _ w
    (fun v S _ => hNonneg v S) hTests
  let M := T.filter (fun t => triangleEdges t ∈ K)
  have hM : triangleHypergraph M = K := by
    ext S
    constructor
    · intro hS
      obtain ⟨t,ht,rfl⟩ := mem_map.mp hS
      exact (mem_filter.mp ht).2
    · intro hS
      obtain ⟨t,ht,rfl⟩ := mem_map.mp (hK hS)
      exact mem_map.mpr ⟨t,mem_filter.mpr ⟨ht,hS⟩,rfl⟩
  have hPair : (↑K : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id :=
    fun a ha b hb' hab => hMatch a ha b hb' hab
  refine ⟨M,filter_subset _ _,hM ▸ hMatch,?_,?_⟩
  · apply trianglePacking_leave_balanced hb
      (fun t ht => (mem_filter.mp (hT ((filter_subset _ _) ht))).2)
    rwa [hM]
  intro v
  rw [hM]
  have hCover : coveredEdges K ⊆ G := coveredEdges_subset (fun S hS => hSub S (hK hS))
  have hCoverDegree : incidentDegree (coveredEdges K) v ≤ incidentDegree G v :=
    incidentDegree_mono hCover v
  have hDiff : (incidentDegree (packingLeave G K) v : ℝ) =
      incidentDegree G v - incidentDegree (coveredEdges K) v := by
    rw [packingLeave,incidentDegree_sdiff hCover,Nat.cast_sub hCoverDegree]
  have hBijection : weight (w v) K = incidentDegree (coveredEdges K) v := by
    rw [incidentDegree_coveredEdges_eq K hPair v,weight,Nat.cast_sum]
  let q := Δ ^ (-(1/900) : ℝ)
  let r := d ^ (-(1/3) : ℝ)
  have hq : 0 ≤ q := rpow_nonneg hΔ0.le _
  have hq1 : q ≤ 1 := rpow_le_one_of_one_le_of_nonpos hΔ1 (by norm_num)
  have hr : 0 ≤ r := rpow_nonneg hd0.le _
  have hrd : r * d = u := by
    change d ^ (-(1/3) : ℝ) * d = d ^ (2/3 : ℝ)
    conv_lhs => rhs; rw [← rpow_one d]
    rw [← rpow_add hd0]
    congr 1
    norm_num
  have hSlack : (1-2*r)*Δ ≤ d-u := by
    dsimp only [Δ]
    nlinarith only [hrd,mul_nonneg hr hu]
  have hQuotient : (1-2*r)*incidentDegree G v ≤ weight (w v) H / Δ := by
    apply (le_div_iff₀ hΔ0).mpr
    calc
      _ = ((1-2*r)*Δ)*incidentDegree G v := by ring
      _ ≤ (d-u)*incidentDegree G v := mul_le_mul_of_nonneg_right hSlack (by positivity)
      _ ≤ _ := hWeight v
  have hApprox' := (abs_le.mp (hApprox v (hLocalHeavy v))).1
  change -(q * (weight (w v) H / Δ)) ≤ weight (w v) K - weight (w v) H / Δ at hApprox'
  have hCovLower : (1-q)*(1-2*r)*incidentDegree G v ≤ weight (w v) K := by
    have hMultiply := mul_le_mul_of_nonneg_left hQuotient (sub_nonneg.mpr hq1)
    calc
      _ = (1-q)*((1-2*r)*incidentDegree G v) := by ring
      _ ≤ _ := hMultiply
      _ ≤ _ := by linarith only [hApprox']
  rw [hDiff,← hBijection]
  change (incidentDegree G v : ℝ) - weight (w v) K ≤ (q+2*r)*incidentDegree G v
  have hCross : 0 ≤ q * r * (incidentDegree G v : ℝ) :=
    mul_nonneg (mul_nonneg hq hr) (by positivity)
  nlinarith only [hCovLower,hCross]

end OverfullWork.ChenShan
