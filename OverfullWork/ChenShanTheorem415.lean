module

public import OverfullWork.ChenShanCoverDownParameterChoice
public import OverfullWork.ChenShanNestedAbsorptionStep
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type*} [Fintype A] [Fintype B] [Fintype W]
variable {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}

private theorem tripartite_triangle_of_certificate
    {t : Finset (OrientedTripartiteEdge A B W)} (ht : IsCoverDownTriangle t)
    (hSupport : t ⊆ tripartiteArcs E P Q) :
    ∃ z : A × B × W, t = triangleEdges z := by
  obtain ⟨a,b,c,_,_,_,rfl⟩ := ht
  have hab := hSupport (by simp [exteriorTriangle] :
    (a,b) ∈ exteriorTriangle (a,b) c)
  have hbc := hSupport (by simp [exteriorTriangle,exteriorReserveArcs] :
    (b,c) ∈ exteriorTriangle (a,b) c)
  have hca := hSupport (by simp [exteriorTriangle,exteriorReserveArcs] :
    (c,a) ∈ exteriorTriangle (a,b) c)
  rcases a with a | (a | a) <;>
    rcases b with b | (b | b) <;>
    rcases c with c | (c | c) <;>
    simp only [mem_tripartiteArcs,tripartiteArc] at hab hbc hca
  · refine ⟨(a,b,c),?_⟩
    ext e
    simp only [exteriorTriangle,exteriorReserveArcs,triangleEdges,mem_insert,mem_singleton]
  · refine ⟨(c,a,b),?_⟩
    ext e
    simp only [exteriorTriangle,exteriorReserveArcs,triangleEdges,mem_insert,mem_singleton]
    tauto
  · refine ⟨(b,c,a),?_⟩
    ext e
    simp only [exteriorTriangle,exteriorReserveArcs,triangleEdges,mem_insert,mem_singleton]
    tauto

/-- A certified exact cover by oriented triangles gives the decomposition
with one triangle through every edge on each of the three sides. -/
theorem tripartite_decomposition_of_cover_down_packing
    (T : Finset (Finset (OrientedTripartiteEdge A B W)))
    (hT : (↑T : Set (Finset (OrientedTripartiteEdge A B W))).PairwiseDisjoint id)
    (hCert : ∀ t ∈ T, IsCoverDownTriangle t)
    (hCov : coveredEdges T = tripartiteArcs E P Q) :
    Nonempty (TripartiteTriangleDecomposition E P Q) := by
  have hSupport {t} (ht : t ∈ T) : t ⊆ tripartiteArcs E P Q := by
    intro e he
    rw [← hCov]
    exact mem_coveredEdges.mpr ⟨t,ht,he⟩
  have hFind {e} (he : e ∈ tripartiteArcs E P Q) :
      ∃ z : A × B × W, triangleEdges z ∈ T ∧ e ∈ triangleEdges z := by
    rw [← hCov] at he
    obtain ⟨t,ht,he⟩ := mem_coveredEdges.mp he
    obtain ⟨z,rfl⟩ := tripartite_triangle_of_certificate (hCert t ht) (hSupport ht)
    exact ⟨z,ht,he⟩
  have hUnique {z z' : A × B × W} {e : OrientedTripartiteEdge A B W}
      (hz : triangleEdges z ∈ T) (hz' : triangleEdges z' ∈ T)
      (he : e ∈ triangleEdges z) (he' : e ∈ triangleEdges z') : z = z' := by
    apply triangleEdges_injective
    by_contra hne
    exact disjoint_left.mp (hT (show triangleEdges z ∈ (↑T : Set _) from hz)
      (show triangleEdges z' ∈ (↑T : Set _) from hz') hne) he he'
  refine ⟨⟨fun a b w => triangleEdges (a,b,w) ∈ T,?_,?_,?_,?_⟩⟩
  · intro a b w ht
    exact ⟨mem_tripartiteArcs.mp (hSupport ht (by simp [triangleEdges] :
      (.inl a,.inr (.inl b)) ∈ triangleEdges (a,b,w))),
      mem_tripartiteArcs.mp (hSupport ht (by simp [triangleEdges] :
      (.inr (.inr w),.inl a) ∈ triangleEdges (a,b,w))),
      mem_tripartiteArcs.mp (hSupport ht (by simp [triangleEdges] :
      (.inr (.inl b),.inr (.inr w)) ∈ triangleEdges (a,b,w)))⟩
  · intro a b hab
    let e : OrientedTripartiteEdge A B W := (.inl a,.inr (.inl b))
    obtain ⟨⟨a',b',w⟩,ht,he⟩ := hFind (e := e) (mem_tripartiteArcs.mpr hab)
    obtain ⟨rfl,rfl⟩ : a = a' ∧ b = b' := by
      simpa [e,triangleEdges,Prod.mk.injEq] using he
    refine ⟨w,ht,fun w' hw' => ?_⟩
    exact congrArg (fun t => t.2.2) (hUnique hw' ht (by simp [e,triangleEdges]) he)
  · intro a w haw
    let e : OrientedTripartiteEdge A B W := (.inr (.inr w),.inl a)
    obtain ⟨⟨a',b,w'⟩,ht,he⟩ := hFind (e := e) (mem_tripartiteArcs.mpr haw)
    obtain ⟨rfl,rfl⟩ : w = w' ∧ a = a' := by
      simpa [e,triangleEdges,Prod.mk.injEq] using he
    refine ⟨b,ht,fun b' hb' => ?_⟩
    exact congrArg (fun t => t.2.1) (hUnique hb' ht (by simp [e,triangleEdges]) he)
  · intro b w hbw
    let e : OrientedTripartiteEdge A B W := (.inr (.inl b),.inr (.inr w))
    obtain ⟨⟨a,b',w'⟩,ht,he⟩ := hFind (e := e) (mem_tripartiteArcs.mpr hbw)
    obtain ⟨rfl,rfl⟩ : b = b' ∧ w = w' := by
      simpa [e,triangleEdges,Prod.mk.injEq] using he
    refine ⟨a,ht,fun a' ha' => ?_⟩
    exact congrArg Prod.fst (hUnique ha' ht (by simp [e,triangleEdges]) he)

private theorem DenseTripartite.color_ratio_upper {m : ℕ} {η ε : ℝ}
    (G : DenseTripartite E P Q m η ε) (hm : 0 < m) (hε : ε ≤ 1/2) :
    (Fintype.card W : ℝ)/m ≤ 3/2 := by
  have hNonempty : Nonempty A := Fintype.card_pos_iff.mp (by rwa [G.sizeA])
  let a := hNonempty.some
  have hEq := G.balanced.1 a
  rw [Fintype.card_subtype,Fintype.card_subtype] at hEq
  have hCard : (univ.filter (P a)).card ≤ m := by
    rw [← hEq, ← G.sizeB]
    exact card_le_univ _
  have hSum :
      ((univ.filter (P a)).card : ℝ) + ((univ.filter (fun w => ¬ P a w)).card : ℝ) =
        Fintype.card W := by
    exact_mod_cast (by simpa only [card_univ] using
      card_filter_add_card_filter_not (s := (univ : Finset W)) (P a))
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  apply (div_le_iff₀ hmR).mpr
  have hCardR : ((univ.filter (P a)).card : ℝ) ≤ m := by exact_mod_cast hCard
  have hMissing := (G.missingAW a).trans (mul_le_mul_of_nonneg_right hε hmR.le)
  linarith only [hCardR,hSum,hMissing]

set_option maxHeartbeats 800000 in
/-- Chen–Shan, Theorem 4.15. The margin determines both thresholds
before the graph and its three vertex classes are chosen. -/
theorem exists_triangle_decomposition_of_dense_tripartite
    (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, ∃ m₀ : ℕ, 0 < ε₀ ∧
      ∀ (m : ℕ), m₀ ≤ m → ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
      ∀ (A B W : Type u) [Fintype A] [Fintype B] [Fintype W]
        (E : A → B → Prop) (P : A → W → Prop) (Q : B → W → Prop),
      DenseTripartite E P Q m η ε →
        Nonempty (TripartiteTriangleDecomposition E P Q) := by
  let η' := min η (1/8)
  have hη' : 0 < η' := lt_min hη (by norm_num)
  have hηhalf : η' < 1/2 := (min_le_right η (1/8)).trans_lt (by norm_num)
  let cap := coverDownPackingCap (η'/2/2)
  have hcap : 0 < cap := by
    unfold cap coverDownPackingCap
    exact lt_min (by positivity) (by positivity)
  obtain ⟨η₀,ρ,μ,ζ,ξ,hη₀,hη₀small,hEta,hρ,hρsmall,hρabs,hμ,hμsmall,hζ,hξ,hξ₁,hScalar⟩ :=
    exists_cover_down_scalar_parameters hη' hηhalf.le hcap
  obtain ⟨cap',n₀,N₀,hCapEq,_,hLevels⟩ := exists_all_levels_cover_down_packing.{u}
    hρ hρsmall hη₀ hη₀small hEta hηhalf.le hμ hμsmall hζ hξ
  have hδmin : 0 < 20*μ/ρ := by positivity
  obtain ⟨cutoff,hNumeric⟩ := cover_down_levels_of_scalar_bounds_uniform.{u}
    (η₀ := η₀) (ζ := ζ) (cap := cap') n₀ N₀ hρ hρsmall hη' hμ.le hδmin hξ
  obtain ⟨h,εAbs,m₀,hCut,hFour,hεAbs,hm₀,hNested⟩ :=
    exists_nested_prefixes_and_absorber.{u,u,u} η' ρ μ ξ
      hη' hηhalf hρ hρabs hμ hξ hξ₁ cutoff
  refine ⟨min εAbs (min ξ (1/2)),m₀,lt_min hεAbs (lt_min hξ (by norm_num)),?_⟩
  intro m hm₀' ε hε hεsmall A B W _ _ _ E P Q hG
  have hm : 0 < m := by omega
  have hεξ : ε ≤ ξ := hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεhalf : ε ≤ 1/2 := hεsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηle : 1/2 + η' ≤ 1/2 + η :=
    add_le_add_right (min_le_left η (1/8)) _
  have hG' : DenseTripartite E P Q m η' ε :=
    ⟨hG.sizeA,hG.sizeB,hG.balanced,
      fun a => (mul_le_mul_of_nonneg_right hηle (Nat.cast_nonneg m)).trans (hG.degreeA a),
      fun b => (mul_le_mul_of_nonneg_right hηle (Nat.cast_nonneg m)).trans (hG.degreeB b),
      hG.missingAW,hG.missingBW,hG.missingWA,hG.missingWB⟩
  let k := Fintype.card W
  have hLower : 1/2+η' ≤ (k:ℝ)/m := hG'.color_ratio_lower hm
  have hUpper : (k:ℝ)/m ≤ 3/2 := DenseTripartite.color_ratio_upper hG' hm hεhalf
  have hk : 0 < k := by
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have h := (le_div_iff₀ hmR).mp hLower
    exact_mod_cast (show (0:ℝ) < k from (by positivity : 0 < (1/2+η')*m).trans_le h)
  obtain ⟨l,hSizes,_,_,S,hSample,_,EA,PA,QA,hAbs,hDisj,hDeg,hAbsDec,hAbsorb⟩ :=
    hNested m hm₀' ε hε (hεsmall.trans (min_le_left _ _)) A B W E P Q hG'
  let δ := 4*ε+10*ξ+20*μ/ρ
  have hδle : 20*μ/ρ ≤ δ := by
    dsimp [δ]
    linarith only [hε,hξ]
  have hSc : CoverDownScalarBounds ρ η' η₀ μ ζ δ ξ cap' := by
    rw [hCapEq]
    exact (hScalar ε hε hεξ).2
  have hBounds := hNumeric δ hδle hSc A B W m k l S
    (fun i hi => hCut.trans (hSizes i hi)) (by linarith only [hLower,hη']) hUpper
  have hAbsBal := arcBalanced_of_tripartiteLocallyBalanced
    (Classical.choice hAbsDec).locallyBalanced
  obtain ⟨L,T,hL,hInside,hBal,hT,hCert,hCov⟩ :=
    hLevels A B W m k l S E P Q ε (tripartiteArcs EA PA QA)
      hm hk rfl hε hG' hLower hUpper hSample hBounds hAbs hDisj hAbsBal hDeg
  obtain ⟨U,hU,hCertU,hCovU⟩ := finish_all_levels_with_absorber EA PA QA (S.vertices l)
    hAbs hAbsorb L T hL (hInside.trans inter_subset_right) hBal hT hCert hCov
  exact tripartite_decomposition_of_cover_down_packing U hU hCertU hCovU

end OverfullWork.ChenShan
