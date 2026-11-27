module

public import OverfullWork.ChenShanCoverDownPerturbation
public import OverfullWork.ChenShanLemma414
import OverfullWork.ChenShanAbsorberCatalogue
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

universe u
variable {A B W : Type u} [Fintype A] [Fintype B] [Fintype W]
variable {ρ : ℝ} {m k l : ℕ}

/-- The updated reserve still consists of crossing arcs after the
exterior leave is covered. -/
theorem cover_down_updated_reserve_crosses
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (R C L : TripartiteArcSet A B W)
    (hR : ∀ e ∈ R, CrossesNestedPrefix S i e.1 e.2)
    (hL : L ⊆ S.vertices i ×ˢ S.vertices i)
    (hNoInner : Disjoint L (S.vertices (i+1) ×ˢ S.vertices (i+1))) :
    let X := S.vertices i \ S.vertices (i+1)
    let D := L ∩ (X ×ˢ X)
    ∀ e ∈ (R \ C) ∪ (L \ D), CrossesNestedPrefix S i e.1 e.2 := by
  intro X D e he
  rcases mem_union.mp he with he | he
  · exact hR e (mem_sdiff.mp he).1
  · have hL' := (mem_sdiff.mp he).1
    obtain ⟨h₁,h₂⟩ := mem_product.mp (hL hL')
    by_cases hU₁ : e.1 ∈ S.vertices (i+1) <;> by_cases hU₂ : e.2 ∈ S.vertices (i+1)
    · exact False.elim (disjoint_left.mp hNoInner hL' (mem_product.mpr ⟨hU₁,hU₂⟩))
    · exact Or.inl ⟨hU₁,mem_sdiff.mpr ⟨h₂,hU₂⟩⟩
    · exact Or.inr ⟨mem_sdiff.mpr ⟨h₁,hU₁⟩,hU₂⟩
    · exact False.elim ((mem_sdiff.mp he).2 (mem_inter.mpr
        ⟨hL',mem_product.mpr ⟨mem_sdiff.mpr ⟨h₁,hU₁⟩,mem_sdiff.mpr ⟨h₂,hU₂⟩⟩⟩))

omit [Fintype A] [Fintype B] [Fintype W] in
theorem crossingPartTag_eq_succ_of_arc {E : A → B → Prop} {P : A → W → Prop}
    {Q : B → W → Prop} {v w : TripartiteVertex A B W} (he : tripartiteArc E P Q v w) :
    crossingPartTag w = crossingPartTag v + 1 := by
  rcases v with a | (b | z) <;> rcases w with a' | (b' | z') <;>
    first | rfl | exact False.elim he

/-- The two classes of the modified exterior neighborhood coincide
with the out- and in-neighborhoods, in cyclic order. -/
theorem cover_down_exterior_neighbor_shores
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ) (R : TripartiteArcSet A B W)
    (hR : R ⊆ tripartiteArcs E P Q)
    (hCross : ∀ e ∈ R, CrossesNestedPrefix S i e.1 e.2)
    (v : TripartiteVertex A B W) (hv : v ∉ S.vertices (i+1)) :
    arcOutNeighbors R v =
      arcNeighborsIn (prefixPartVertices S (i+1) (crossingPartTag v + 1)) R v ∧
    arcInNeighbors R v =
      arcNeighborsIn (prefixPartVertices S (i+1) (crossingPartTag v + 2)) R v := by
  have hNext (u w : TripartiteVertex A B W) (he : (u,w) ∈ R) :
      crossingPartTag w = crossingPartTag u+1 :=
    crossingPartTag_eq_succ_of_arc (mem_tripartiteArcs.mp (hR he))
  have hPrev (u w : TripartiteVertex A B W) (he : (w,u) ∈ R) :
      crossingPartTag w = crossingPartTag u+2 :=
    (show ∀ a b : Fin 3, b = a+1 → a = b+2 by decide) _ _ (hNext w u he)
  have hNe : (1:Fin 3) ≠ 2 := by decide
  constructor
  · ext w
    rw [mem_arcOutNeighbors,mem_arcNeighborsIn]
    constructor
    · intro he
      have hc := hCross (v,w) he
      have hU := (hc.resolve_left (fun h => hv h.1)).2
      exact ⟨mem_filter.mpr ⟨hU,hNext v w he⟩,Or.inl he⟩
    · rintro ⟨hZ,h⟩
      refine h.resolve_right ?_
      intro he
      have hw := (mem_filter.mp hZ).2
      exact hNe (add_left_cancel (hw.symm.trans (hPrev v w he)))
  · ext w
    rw [mem_arcInNeighbors,mem_arcNeighborsIn]
    constructor
    · intro he
      have hc := hCross (w,v) he
      have hU := (hc.resolve_right (fun h => hv h.2)).1
      exact ⟨mem_filter.mpr ⟨hU,hPrev v w he⟩,Or.inr he⟩
    · rintro ⟨hZ,h⟩
      refine h.resolve_left ?_
      intro he
      have hw := (mem_filter.mp hZ).2
      exact hNe (add_left_cancel ((hNext v w he).symm.trans hw))

/-- The two matching shores partition the modified neighborhood, and
local balance makes their sizes equal. -/
theorem cover_down_exterior_neighbor_partition
    {E : A → B → Prop} {P : A → W → Prop} {Q : B → W → Prop}
    (S : NestedTripartitePrefixes A B W ρ m k l) (i : ℕ)
    (GU R : TripartiteArcSet A B W) (hR : R ⊆ tripartiteArcs E P Q)
    (hCross : ∀ e ∈ R, CrossesNestedPrefix S i e.1 e.2)
    (hGU : GU ⊆ S.vertices (i+1) ×ˢ S.vertices (i+1))
    (hBal : ArcBalanced (GU ∪ R))
    (v : TripartiteVertex A B W) (hv : v ∉ S.vertices (i+1)) :
    let F := arcOutNeighbors R v
    let G := arcInNeighbors R v
    F ∪ G = arcNeighborsIn (S.vertices (i+1)) R v ∧ Disjoint F G ∧ F.card = G.card := by
  intro F G
  obtain ⟨hF,hG⟩ := cover_down_exterior_neighbor_shores S i R hR hCross v hv
  refine ⟨?_,?_,?_⟩
  · ext w
    simp only [F,G,mem_union,mem_arcOutNeighbors,mem_arcInNeighbors,mem_arcNeighborsIn]
    constructor
    · intro h
      refine ⟨?_,h⟩
      rcases h with h | h
      · exact ((hCross (v,w) h).resolve_left (fun he => hv he.1)).2
      · exact ((hCross (w,v) h).resolve_right (fun he => hv he.2)).1
    · exact And.right
  · change Disjoint (arcOutNeighbors R v) (arcInNeighbors R v)
    rw [hF,hG]
    apply disjoint_left.mpr
    intro w hw hw'
    have h₁ := (mem_filter.mp ((mem_arcNeighborsIn _ _ _ _).mp hw).1).2
    have h₂ := (mem_filter.mp ((mem_arcNeighborsIn _ _ _ _).mp hw').1).2
    exact (by decide : (1:Fin 3) ≠ 2) (add_left_cancel (h₁.symm.trans h₂))
  · exact cover_down_exterior_out_in_card (S.vertices (i+1)) GU R (by
      intro e he
      exact mem_product.mpr (mem_product.mp (hGU he)))
      (by convert hBal using 1; ext e; simp only [mem_union]) v hv

/-- The constants in Step 2 meet the overlap, load and degree
budgets of Lemma 4.14. -/
theorem cover_down_matching_budgets {ρ μ n N η : ℝ} (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hμ : 0 ≤ μ) (hn : 0 ≤ n) (hN : ρ*n ≤ N) (hN' : N ≤ 4*ρ*n)
    (hMargin : 120000*μ^(3/2:ℝ)*n ≤ η*μ*(ρ*n)/8) :
    let b : ℝ := (⌈10/ρ⌉₊ : ℕ)
    let d := 10*μ
    4*n ≤ 3*b*N ∧ 100*μ^2*ρ*n ≤ 6*d^2*N ∧
    20*μ*n ≤ 2*b*d*N ∧ 81*b*d^(3/2:ℝ)*N ≤ η*μ*(ρ*n)/8 := by
  let b : ℝ := (⌈10/ρ⌉₊ : ℕ)
  have hb₀ : 0 ≤ b := by positivity
  have hN₀ : 0 ≤ N := (mul_nonneg hρ.le hn).trans hN
  have hLo : 10/ρ ≤ b := Nat.le_ceil _
  have hHi : b < 10/ρ+1 := Nat.ceil_lt_add_one (by positivity : 0 ≤ (10:ℝ)/ρ)
  have hbLo : 10 ≤ b*ρ := (div_le_iff₀ hρ).mp hLo
  have hbHi : b*ρ ≤ 11 := by
    have h := (lt_div_iff₀ hρ).mp (show b < (10+ρ)/ρ by
      rwa [add_div,div_self hρ.ne'])
    linarith only [h,hρone]
  have hProdLo : 10*n ≤ b*N := by
    have h₁ := mul_le_mul_of_nonneg_right hbLo hn
    have h₂ := mul_le_mul_of_nonneg_left hN hb₀
    linarith only [h₁,h₂]
  have hProdHi : b*N ≤ 44*n := by
    have h₁ := mul_le_mul_of_nonneg_right hbHi hn
    have h₂ := mul_le_mul_of_nonneg_left hN' hb₀
    linarith only [h₁,h₂]
  have hOverlap := mul_le_mul_of_nonneg_left hN (show 0 ≤ 100*μ^2 by positivity)
  have hLoad := mul_le_mul_of_nonneg_left hProdLo hμ
  have h10 : (10:ℝ)^(3/2:ℝ) ≤ 32 := by
    rw [show (3/2:ℝ) = 1+1/2 by norm_num,Real.rpow_add (by norm_num : (0:ℝ) < 10),
      Real.rpow_one,← Real.sqrt_eq_rpow]
    have hs : Real.sqrt 10 ≤ 16/5 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith only [hs]
  have hPower : (10*μ)^(3/2:ℝ) ≤ 32*μ^(3/2:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hμ]
    exact mul_le_mul_of_nonneg_right h10 (Real.rpow_nonneg hμ _)
  have hM₁ := mul_le_mul_of_nonneg_right hPower (show 0 ≤ b*N from mul_nonneg hb₀ hN₀)
  have hM₂ := mul_le_mul_of_nonneg_right hProdHi (show 0 ≤ μ^(3/2:ℝ) from Real.rpow_nonneg hμ _)
  have hM₃ := mul_nonneg (Real.rpow_nonneg hμ (3/2:ℝ)) hn
  change 4*n ≤ 3*b*N ∧ 100*μ^2*ρ*n ≤ 6*(10*μ)^2*N ∧
    20*μ*n ≤ 2*b*(10*μ)*N ∧ 81*b*(10*μ)^(3/2:ℝ)*N ≤ η*μ*(ρ*n)/8
  refine ⟨by linarith only [hProdLo,hn],?_,by linarith only [hLoad,mul_nonneg hμ hn],?_⟩
  · linarith only [hOverlap,mul_nonneg (sq_nonneg μ) hN₀]
  · linarith only [hM₁,hM₂,hM₃,hMargin]

/-- Apply Lemma 4.14 directly to a finite family of shores with the
relative minimum degree of (4.26). -/
theorem exists_cover_down_shore_matchings
    (b : ℕ) (hb : 0 < b) (density η : ℝ) (hdensity : 0 < density) (hdensityone : density ≤ 1) :
    ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
    ∀ (V J : Type u) [Fintype V] [Fintype J] (E : V → V → Prop) (F G : J → Finset V),
    Fintype.card V ≤ 3*n → Fintype.card J ≤ 3*b*n →
    (∀ j, (F j).card = (G j).card) → (∀ j, Disjoint (F j) (G j)) →
    (∀ j, 81*b*density^(3/2:ℝ)*n ≤ η*(F j).card) →
    (∀ j, ∀ x ∈ F j, (1/2+η)*((G j).card : ℝ) ≤ ((G j).filter (E x)).card) →
    (∀ j, ∀ y ∈ G j, (1/2+η)*((F j).card : ℝ) ≤ ((F j).filter (fun x => E x y)).card) →
    (∀ i j, i ≠ j → (((F i ∪ G i) ∩ (F j ∪ G j)).card : ℝ) ≤ 6*density^2*n) →
    (∀ v, ((univ.filter (fun j => v ∈ F j ∪ G j)).card : ℝ) ≤ 2*b*density*n) →
    ∃ M : J → Finset (V × V),
      (∀ j, ∃ f : ↥(F j) ≃ ↥(G j), M j = matchingArcs f ∧ ∀ a : F j, E a (f a)) ∧
      ∀ i j, i ≠ j → Disjoint (M i) (M j) := by
  obtain ⟨n₀,hPack⟩ := exists_bklot_bipartite_matching_packing b hb density hdensity hdensityone
  refine ⟨n₀,?_⟩
  intro n hn V J _ _ E F G hV hJ hSize hDisj hMargin hLeft hRight hOverlap hLoad
  let q := Fintype.card J
  let e : J ≃ Fin q := Fintype.equivFin J
  let idx (i : ℕ) (h : i < q) := e.symm ⟨i,h⟩
  let X (i : ℕ) := if h : i < q then F (idx i h) else ∅
  let Y (i : ℕ) := if h : i < q then G (idx i h) else ∅
  have hX (i) (hi : i < q) : X i = F (idx i hi) := dite_eq_left hi
  have hY (i) (hi : i < q) : Y i = G (idx i hi) := dite_eq_left hi
  have hIndex (j : J) : idx (e j).val (e j).isLt = j := e.symm_apply_apply j
  have hIdxNe (i j) (hi : i < q) (hj : j < q) (hne : i ≠ j) :
      idx i hi ≠ idx j hj := fun h => hne (congrArg Fin.val (e.symm.injective h))
  have hLoad' (v : V) : (((range q).filter (fun j => v ∈ X j ∪ Y j)).card : ℝ) ≤ 2*b*density*n := by
    let f : J ↪ ℕ := e.toEmbedding.trans Fin.valEmbedding
    have hEq : (range q).filter (fun j => v ∈ X j ∪ Y j) =
        (univ.filter (fun j => v ∈ F j ∪ G j)).map f := by
      ext i
      simp only [mem_filter,mem_range,mem_map,mem_univ,true_and]
      constructor
      · rintro ⟨hi,h⟩
        rw [hX i hi,hY i hi] at h
        exact ⟨idx i hi,h,congrArg Fin.val (e.apply_symm_apply ⟨i,hi⟩)⟩
      · rintro ⟨j,h,rfl⟩
        have hj : f j < q := (e j).isLt
        refine ⟨hj,?_⟩
        rw [hX _ hj,hY _ hj]
        change v ∈ F (idx (e j).val (e j).isLt) ∪ G (idx (e j).val (e j).isLt)
        rwa [hIndex]
    rw [hEq,card_map]
    exact hLoad v
  have hXSize (i) (hi : i < q) : (X i).card = (Y i).card := by
    rw [hX i hi,hY i hi]
    exact hSize _
  obtain ⟨M,hM,hPair⟩ := hPack n q hn hJ V E X Y hV hXSize
    (by intro i hi; rw [hX i hi,hY i hi]; exact hDisj _)
    (by
      intro i hi x hx
      rw [hX i hi] at hx
      rw [hY i hi]
      have h := hMargin (idx i hi)
      rw [hSize (idx i hi)] at h
      linarith only [h,hLeft _ x hx])
    (by
      intro i hi y hy
      rw [hY i hi] at hy
      rw [hX i hi]
      linarith only [hMargin (idx i hi),hRight _ y hy])
    (by
      intro i hi j hj hne
      rw [hX i hi,hY i hi,hX j hj,hY j hj]
      exact hOverlap _ _ (hIdxNe i j hi hj hne))
    hLoad'
  refine ⟨fun j => M (e j).val,?_,?_⟩
  · intro j
    have h := hM (e j).val (e j).isLt
    rwa [hX _ (e j).isLt,hY _ (e j).isLt,hIndex] at h
  · intro i j hne
    exact hPair (e i).val (e i).isLt (e j).val (e j).isLt
      (fun h => hne (e.injective (Fin.ext h)))

end OverfullWork.ChenShan
