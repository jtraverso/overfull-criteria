module

public import OverfullWork.ChenShanMultigraphCompletion
public import OverfullWork.KLOSPartitionRestriction
public import OverfullWork.Critical
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open SimpleGraph Finset KLOS PrunedCore RobustExpansion
open scoped Classical
universe u

/-- The ordinary robust cores and the exceptional set of Theorem 2.2.
The ambient density and the internal robustness use their respective
normalizations. -/
structure OrdinaryCorePartition {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k a : ℕ) (α ν τ : ℝ)
    (U : I → Finset V) (Z : Finset V) : Prop where
  separated : Pairwise fun i j => Disjoint (U i) (U j)
  exceptional : ∀ i, Disjoint (U i) Z
  covers : ∀ v, v ∈ Z ∨ ∃ i, v ∈ U i
  size : ∀ i, α * (Fintype.card V : ℝ) ≤ (U i).card
  minDegree : ∀ i, ∀ v ∈ U i, k - a ≤ neighboursIn G (U i) v
  robust : ∀ i, ExpandsInside G ν τ (U i)

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

private theorem expandsInside_mono_margin (G : SimpleGraph V) [DecidableRel G.Adj]
    {ν ν' τ : ℝ} (hν : ν' ≤ ν) {U : Finset V} (h : ExpandsInside G ν τ U) :
    ExpandsInside G ν' τ U := by
  intro S hS hLo hHi
  have hScale := mul_le_mul_of_nonneg_right hν (Nat.cast_nonneg (α := ℝ) U.card)
  have hMono : robustNeighbourhoodIn G ν U S ⊆ robustNeighbourhoodIn G ν' U S := by
    intro v hv
    have hv' := mem_filter.mp hv
    exact mem_filter.mpr ⟨hv'.1,hScale.trans hv'.2⟩
  calc
    _ ≤ (S.card : ℝ) + ν * U.card := add_le_add_right hScale _
    _ ≤ _ := (h S hS hLo hHi).trans (by exact_mod_cast card_le_card hMono)

private theorem expandsInside_induced_image
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : V ↪ W) (he : ∀ x y, H.Adj (e x) (e y) ↔ G.Adj x y)
    {ν τ : ℝ} {U : Finset V} (h : ExpandsInside G ν τ U) :
    ExpandsInside H ν τ (U.map e) := by
  intro S hS hLo hHi
  let T := U.filter (fun v => e v ∈ S)
  have hT : T.map e = S := by
    ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      exact (mem_filter.mp hv).2
    · intro hx
      obtain ⟨v,hv,rfl⟩ := mem_map.mp (hS hx)
      exact mem_map.mpr ⟨v,mem_filter.mpr ⟨hv,hx⟩,rfl⟩
  rw [← hT,card_map,card_map] at hLo hHi
  have hc := h T (filter_subset _ _) hLo hHi
  simpa only [← hT,card_map,robustNeighbourhoodIn_map_induced G H e he] using hc

private theorem deficit_le_exceptional {I : Type*}
    {G : SimpleGraph V} [DecidableRel G.Adj] {k a : ℕ} {α ν τ : ℝ}
    {U : I → Finset V} {Z : Finset V} (P : OrdinaryCorePartition G k a α ν τ U Z) :
    ∑ v, (k - G.degree v) ≤ Fintype.card V * a + k * Z.card := by
  calc
    _ ≤ ∑ v, (a + if v ∈ Z then k else 0) := by
      apply sum_le_sum
      intro v _
      by_cases hz : v ∈ Z
      · simp only [ite_eq_left hz]
        omega
      · obtain ⟨i,hi⟩ := (P.covers v).resolve_left hz
        have hmin := P.minDegree i v hi
        have hle : neighboursIn G (U i) v ≤ G.degree v := by
          rw [neighboursIn_eq_filter_card, ← card_neighborFinset_eq_degree]
          apply card_le_card
          intro x hx
          simpa only [mem_neighborFinset] using (mem_filter.mp hx).2
        simp only [ite_eq_right hz,add_zero]
        omega
    _ = _ := by
      rw [sum_add_distrib,← sum_filter]
      simp [Nat.mul_comm]

set_option maxHeartbeats 1400000 in
/-- The auxiliary-core step in §5.5. It keeps the old graph induced,
doubles the order, adds one robust core, and retains all exceptional
vertices at the error budget used in the paper. -/
theorem exists_regular_completion_add_ordinary_core
    (α ν τ : ℝ) (hα : 0 < α) (hα₁ : α < 1) (hν : 0 < ν)
    (hτ : 0 < τ) (hRange : τ < α/24) :
    ∃ ν' ε : ℝ, 0 < ν' ∧ ν' ≤ ν ∧ 0 < ε ∧ ∃ N : ℕ,
    ∀ {V I : Type u} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V) (Z : Finset V)
      (k a : ℕ),
      let n := Fintype.card V
      let a' := a + Z.card + 1
      N ≤ n → α*(n:ℝ) ≤ k → k < n → (∀ v, G.degree v ≤ k) →
      ¬ (MultiGraph.ofSimpleGraph G).HasOverfullSubset k →
      OrdinaryCorePartition G k a α ν τ U Z →
      (a' : ℝ) ≤ ε*n →
      ∃ R : SimpleGraph (V ⊕ Fin n), ∃ _ : DecidableRel R.Adj,
        (∀ x, R.degree x = k) ∧
        (∀ v w : V, R.Adj (.inl v) (.inl w) ↔ G.Adj v w) ∧
        ¬ (MultiGraph.ofSimpleGraph R).HasOverfullSubset k ∧
        let left : V ↪ V ⊕ Fin n := ⟨Sum.inl,Sum.inl_injective⟩
        let right : Fin n ↪ V ⊕ Fin n := ⟨Sum.inr,Sum.inr_injective⟩
        let cores : Option I → Finset (V ⊕ Fin n) :=
          fun i => i.elim (univ.map right) (fun j => (U j).map left)
        OrdinaryCorePartition R k a' (α/2) ν' τ cores (Z.map left) ∧
        (a' : ℝ) + (Z.map left).card + 1 ≤ ε * (Fintype.card (V ⊕ Fin n) : ℝ) ∧
        (α/2) * (Fintype.card (V ⊕ Fin n) : ℝ) ≤ k := by
  obtain ⟨νaux,ε,hνaux,hε,N,hComplete⟩ := exists_simple_auxiliary_completion.{u} α τ hα hα₁ hτ hRange
  refine ⟨min ν νaux,ε,lt_min hν hνaux,min_le_left _ _,hε,N,?_⟩
  intro V I _ _ G _ U Z k a n a' hn hk hkLt hDegree hNo P hBudget
  have hs := deficit_le_exceptional P
  have hsNat : (∑ v, (k - G.degree v)) ≤ n*(a+Z.card) := by
    exact hs.trans (by rw [Nat.mul_add]; gcongr)
  have hsReal : ((∑ v, (k - G.degree v) : ℕ) : ℝ) ≤ (n:ℝ)*((a:ℝ)+Z.card) := by
    exact_mod_cast hsNat
  have hSmall : ((∑ v, (k - G.degree v) : ℕ) : ℝ) ≤ ε*(n:ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left hBudget (Nat.cast_nonneg (α := ℝ) n)
    simp only [a',Nat.cast_add,Nat.cast_one] at h
    nlinarith only [hsReal,h,Nat.cast_nonneg (α := ℝ) n]
  obtain ⟨R,H,hH,hReg,hLeft,hRight,hRNo,hMin,hExp⟩ :=
    hComplete G k hn hk hkLt hDegree hNo hSmall
  let left : V ↪ V ⊕ Fin n := ⟨Sum.inl,Sum.inl_injective⟩
  let right : Fin n ↪ V ⊕ Fin n := ⟨Sum.inr,Sum.inr_injective⟩
  let cores : Option I → Finset (V ⊕ Fin n) :=
    fun i => i.elim (univ.map right) (fun j => (U j).map left)
  have hnPos : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hb : ⌈((∑ v, (k - G.degree v) : ℕ) : ℝ)/(n:ℝ)⌉₊ ≤ a+Z.card := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hnPos).mpr
    simpa only [Nat.cast_add,mul_comm] using hsReal
  have hCard : (Fintype.card (V ⊕ Fin n) : ℝ) = 2*n := by
    simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add]
    change (n:ℝ)+n = 2*n
    ring
  refine ⟨R,Classical.decRel _,hReg,hLeft,hRNo,?_⟩
  change OrdinaryCorePartition R k a' (α/2) (min ν νaux) τ cores (Z.map left) ∧ _ ∧ _
  refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_,?_⟩
  · intro i j hij
    cases i with
    | none => cases j with
      | none => exact (hij rfl).elim
      | some j =>
        apply Finset.disjoint_left.mpr
        simp [cores,left,right]
    | some i => cases j with
      | none =>
        apply Finset.disjoint_left.mpr
        simp [cores,left,right]
      | some j =>
        exact (disjoint_map left).mpr (P.separated (fun h => hij (congrArg some h)))
  · intro i
    cases i with
    | none =>
      apply Finset.disjoint_left.mpr
      simp [cores,left,right]
    | some i => exact (disjoint_map left).mpr (P.exceptional i)
  · intro v
    cases v with
    | inl v =>
      rcases P.covers v with hv | ⟨i,hi⟩
      · exact Or.inl (mem_map.mpr ⟨v,hv,rfl⟩)
      · exact Or.inr ⟨some i,mem_map.mpr ⟨v,hi,rfl⟩⟩
    | inr w => exact Or.inr ⟨none,mem_map.mpr ⟨w,mem_univ _,rfl⟩⟩
  · intro i
    rw [hCard]
    have hScale : α/2*(2*(n:ℝ)) = α*n := by ring
    rw [hScale]
    cases i with
    | none =>
      simp only [cores,Option.elim_none,card_map,card_univ,Fintype.card_fin]
      nlinarith only [hα₁,hnPos,mul_pos (sub_pos.mpr hα₁) hnPos]
    | some i => simpa only [cores,Option.elim_some,card_map] using P.size i
  · intro i x hx
    cases i with
    | none =>
      obtain ⟨w,_,rfl⟩ := mem_map.mp hx
      change k-a' ≤ neighboursIn R (univ.map right) (right w)
      rw [neighboursIn_map_induced H R right hRight,neighboursIn_eq_filter_card]
      have hEq : univ.filter (H.Adj w) = H.neighborFinset w := by ext; simp
      rw [hEq,card_neighborFinset_eq_degree]
      have hw := hMin w
      dsimp only [n] at hb
      dsimp only [a'] at *
      omega
    | some i =>
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hx
      change k-a' ≤ neighboursIn R ((U i).map left) (left v)
      rw [neighboursIn_map_induced G R left hLeft]
      exact (show k-a' ≤ k-a by dsimp [a']; omega).trans (P.minDegree i v hv)
  · intro i
    cases i with
    | none =>
        exact expandsInside_induced_image H R right hRight
          (expandsInside_mono_margin H (min_le_right _ _) hExp)
    | some i =>
        exact expandsInside_induced_image G R left hLeft
          (expandsInside_mono_margin G (min_le_left _ _) (P.robust i))
  · rw [hCard,card_map]
    simp only [a',Nat.cast_add,Nat.cast_one] at hBudget ⊢
    linarith only [hBudget,Nat.cast_nonneg (α := ℝ) a]
  · rw [hCard,show α/2*(2*(n:ℝ)) = α*n by ring]
    exact hk


/-- Quantitative coloring conclusion for a specified number of ordinary
cores. The degree relation is equality in the regular terminal case
and inequality in the statement for the input graph. -/
def OrdinaryCoreColouringAt (D : ℕ → ℕ → Prop) (q : ℕ) (α ν τ ε : ℝ) (N : ℕ) : Prop :=
  ∀ {V I : Type u} [Fintype V] [DecidableEq V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : I → Finset V) (Z : Finset V)
    (k a : ℕ),
    Fintype.card I = q → N ≤ Fintype.card V → α * (Fintype.card V : ℝ) ≤ k →
    (∀ v, D (G.degree v) k) →
    ¬ (MultiGraph.ofSimpleGraph G).HasOverfullSubset k →
    OrdinaryCorePartition G k a α ν τ U Z →
    ((a : ℝ) + Z.card + 1 ≤ ε * (Fintype.card V : ℝ)) →
    G.EdgeColorable k

/-- Transfer a coloring rule from `q+1` cores to `q` cores. The target
rule is chosen at the common robust parameter before the input graph
is quantified. -/
theorem ordinary_core_colouring_of_completion
    (q : ℕ) {α ν τ : ℝ} (hα : 0 < α) (hα₁ : α < 1) (hν : 0 < ν) (hτ : 0 < τ)
    (hτsmall : τ < α/24) (D : ℕ → ℕ → Prop) (hD : ∀ k, D k k)
    (hTarget : ∀ ν' : ℝ, 0 < ν' → ν' ≤ ν → ∃ ε N, 0 < ε ∧
      OrdinaryCoreColouringAt.{u} D (q+1) (α/2) ν' τ ε N) :
    ∃ ε N, 0 < ε ∧ OrdinaryCoreColouringAt.{u} (· ≤ ·) q α ν τ ε N := by
  obtain ⟨ν',ε₀,hν',hν'le,hε₀,N₀,hAux⟩ :=
    exists_regular_completion_add_ordinary_core.{u} α ν τ hα hα₁ hν hτ hτsmall
  obtain ⟨ε₁,N₁,hε₁,hColour⟩ := hTarget ν' hν' hν'le
  refine ⟨min ε₀ ε₁,max (max N₀ N₁) 1,lt_min hε₀ hε₁,?_⟩
  intro V I _ _ _ G _ U Z k a hq hn hk hDegree hNo hPart hErr
  let n := Fintype.card V
  have hnN₀ : N₀ ≤ n := (le_max_left N₀ N₁).trans ((le_max_left _ 1).trans hn)
  have hnN₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans ((le_max_left _ 1).trans hn)
  have hnPos : 0 < n := (le_max_right _ 1).trans hn
  by_cases hkn : k < n
  · have hErr₀ : ((a + Z.card + 1 : ℕ) : ℝ) ≤ ε₀*n := by
      push_cast
      exact hErr.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _))
    obtain ⟨R,hR,hReg,hKeep,hRNo,P,_,hDensity⟩ :=
      hAux G U Z k a hnN₀ hk hkn hDegree hNo hPart hErr₀
    have hErr₁ : ((a + Z.card + 1 : ℕ) : ℝ) +
        ((Z.map ⟨Sum.inl,Sum.inl_injective⟩ : Finset (V ⊕ Fin n)).card : ℝ) + 1 ≤
        ε₁*(Fintype.card (V ⊕ Fin n) : ℝ) := by
      have h := hErr.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _))
      simp only [Fintype.card_sum,Fintype.card_fin,Nat.cast_add,Nat.cast_one,card_map]
      change (a:ℝ)+Z.card+1+Z.card+1 ≤ ε₁*((n:ℝ)+n)
      change (a:ℝ)+Z.card+1 ≤ ε₁*(n:ℝ) at h
      linarith only [h,Nat.cast_nonneg (α := ℝ) a]
    have hOrder : N₁ ≤ Fintype.card (V ⊕ Fin n) := by
      simp only [Fintype.card_sum,Fintype.card_fin]
      omega
    have hc := hColour R
      (fun i : Option I => i.elim (univ.map ⟨Sum.inr,Sum.inr_injective⟩)
        (fun j => (U j).map ⟨Sum.inl,Sum.inl_injective⟩))
      (Z.map ⟨Sum.inl,Sum.inl_injective⟩) k (a+Z.card+1)
      (by simp [hq]) hOrder hDensity (fun v => by rw [hReg]; exact hD k) hRNo P hErr₁
    let emb : G ↪g R :=
      { toFun := Sum.inl, inj' := Sum.inl_injective, map_rel_iff' := fun {_ _} => hKeep _ _ }
    exact Critical.colourable_of_copy emb.toCopy hc
  · let _ : Nonempty V := Fintype.card_pos_iff.mp hnPos
    exact (LeanPool.Vizing.lineGraph_colorable G).mono
      (by have := G.maxDegree_lt_card_verts; omega)

/-- The closing implication of §5.5. The regular three- and four-core
case is the precise input still needed from Theorem 5.31. -/
theorem theorem22_of_regular_core_factorization
    {α ν τ : ℝ} (hα : 0 < α) (hα₁ : α < 1) (hν : 0 < ν) (hτ : 0 < τ)
    (hτsmall : τ < α/48)
    (hTerminal : ∀ (d w : ℝ) (t : ℕ), (d = α/2 ∨ d = α/4) → 0 < w → (t = 3 ∨ t = 4) →
      ∃ ε N, 0 < ε ∧ OrdinaryCoreColouringAt.{u} (· = ·) t d w τ ε N) :
    ∃ ε N, 0 < ε ∧ ∀ q : ℕ, (q = 1 ∨ q = 2 ∨ q = 3) →
      OrdinaryCoreColouringAt.{u} (· ≤ ·) q α ν τ ε N := by
  have hRange : τ < α/24 := by linarith only [hα,hτsmall]
  have hTwoThree {d w : ℝ} (hd : 0 < d) (hd₁ : d < 1) (hw : 0 < w)
      (hr : τ < d/24) (hDensity : d = α ∨ d = α/2) (q : ℕ) (hq : q = 2 ∨ q = 3) :
      ∃ ε N, 0 < ε ∧ OrdinaryCoreColouringAt.{u} (· ≤ ·) q d w τ ε N :=
    ordinary_core_colouring_of_completion q hd hd₁ hw hτ hr (· = ·) (fun _ => rfl)
      (fun w' hw' _ => hTerminal (d/2) w' (q+1)
        (by rcases hDensity with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (by ring)) hw'
        (by rcases hq with rfl | rfl <;> decide))
  obtain ⟨ε₂,N₂,hε₂,h₂⟩ := hTwoThree hα hα₁ hν hRange (Or.inl rfl) 2 (Or.inl rfl)
  obtain ⟨ε₃,N₃,hε₃,h₃⟩ := hTwoThree hα hα₁ hν hRange (Or.inl rfl) 3 (Or.inr rfl)
  obtain ⟨ε₁,N₁,hε₁,h₁⟩ := ordinary_core_colouring_of_completion 1 hα hα₁ hν hτ hRange
    (· ≤ ·) (fun _ => le_rfl)
    (fun w hw _ => hTwoThree (show 0 < α/2 by positivity) (by linarith only [hα₁]) hw
      (by linarith only [hτsmall]) (Or.inr rfl) 2 (Or.inl rfl))
  let ε := min ε₁ (min ε₂ ε₃)
  let N := max N₁ (max N₂ N₃)
  refine ⟨ε,N,lt_min hε₁ (lt_min hε₂ hε₃),?_⟩
  intro q hq V I _ _ _ G _ U Z k a hI hn hk hd hNo hc he
  have hApply {e : ℝ} {m t : ℕ} (H : OrdinaryCoreColouringAt.{u} (· ≤ ·) t α ν τ e m)
      (ht : Fintype.card I = t) (hm : m ≤ N) (hε : ε ≤ e) : G.EdgeColorable k :=
    H G U Z k a ht (hm.trans hn) hk hd hNo hc
      (he.trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)))
  rcases hq with rfl | rfl | rfl
  · exact hApply h₁ hI (le_max_left _ _) (min_le_left _ _)
  · exact hApply h₂ hI ((le_max_left _ _).trans (le_max_right _ _))
      ((min_le_right _ _).trans (min_le_left _ _))
  · exact hApply h₃ hI ((le_max_right _ _).trans (le_max_right _ _))
      ((min_le_right _ _).trans (min_le_right _ _))

end OverfullWork.ChenShan
