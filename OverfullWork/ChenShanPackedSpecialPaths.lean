module

public import OverfullWork.ChenShanSpecialPathSystem
public import OverfullWork.ChenShanFillingPacking
import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset DirectedRobustExpansion
open scoped Classical

variable {V : Type*}

/-- The real arcs traversed at a given transition of an ordered
special path system. Auxiliary arcs are identified by their sources. -/
def specialPathFillingArcs {H : Digraph V} {A : ℕ → Finset V} {J : Type*} {t : ℕ}
    (P : OrderedClusterPaths H A J 0 t) (U : Finset V) (i : ℕ) : Digraph V :=
  ⟨fun x y => ∃ j, P.vertex i j = x ∧ P.vertex (i+1) j = y ∧ x ∉ U⟩

/-- Construct the interval paths using fixed fillings. The real arcs
at each transition are exactly the arcs of the supplied matching. -/
theorem exists_special_path_system_of_prescribed_fillings
    (G : Digraph V) (A U W : ℕ → Finset V) (t n : ℕ) (F : Fin t → Digraph V)
    (hSize : ∀ i ≤ t, (A i).card = n)
    (hDisj : ∀ i j, i ≤ t → j ≤ t → i ≠ j → Disjoint (A i) (A j))
    (hU : ∀ i < t, U i ⊆ A i) (hW : ∀ i < t, W i ⊆ A (i+1))
    (hUW : ∀ i < t, (U i).card = (W i).card)
    (hF : ∀ i : Fin t, F i ≤ G ∧
      ∃ f : ↥(A i.val \ U i.val) ≃ ↥(A (i.val+1) \ W i.val), F i = fillingMatchingDigraph f) :
    let H : Digraph V := ⟨fun x y => G.Adj x y ∨ ∃ i < t, x ∈ U i ∧ y ∈ W i⟩
    ∃ P : OrderedClusterPaths H A (Fin n) 0 t,
      (∀ i < t, ∀ j, P.vertex i j ∈ U i ↔ P.vertex (i+1) j ∈ W i) ∧
      (∀ i : Fin t, specialPathFillingArcs P (U i.val) i.val = F i) ∧
      (∀ i j : ℕ, i ≤ t → j ≤ t → ∀ a b : Fin n,
        P.vertex i a = P.vertex j b → i = j ∧ a = b) := by
  classical
  intro H
  let R (i : ℕ) (x y : V) : Prop := ∃ hi : i < t, (F ⟨i,hi⟩).Adj x y
  have hEach (i : ℕ) (hi : i < t) :
      ∃ e : A i ≃ A (i+1), (∀ x : A i, x.val ∈ U i ↔ (e x).val ∈ W i) ∧
        ∀ x : A i, x.val ∉ U i → R i x (e x) := by
    obtain ⟨f, hf⟩ := (hF ⟨i,hi⟩).2
    obtain ⟨e, _, _, hClasses, hFree⟩ :=
      exists_special_path_step_of_filling (A i) (A (i+1)) (U i) (W i)
        (hU i hi) (hW i hi) (hUW i hi) f
    refine ⟨e, hClasses, fun x hx => ⟨hi, ?_⟩⟩
    rw [hf]
    exact ⟨⟨x.val,mem_sdiff.mpr ⟨x.prop,hx⟩⟩, rfl, (hFree x hx).symm⟩
  obtain ⟨P, hStep, hCoords⟩ := exists_special_path_system_of_step_bijections R H A U W t n
    hSize hDisj (fun i _ x y ⟨hi, h⟩ => Or.inl ((hF ⟨i,hi⟩).1 h))
    (fun i hi x hx y hy => Or.inr ⟨i, hi, hx, hy⟩) hEach
  refine ⟨P, fun i hi j => (hStep i hi j).1, fun i => ?_, hCoords⟩
  ext x y
  constructor
  · rintro ⟨j, hX, hY, hFree⟩
    obtain ⟨_, h⟩ := (hStep i.val i.isLt j).2 (hX ▸ hFree)
    exact hX ▸ hY ▸ h
  · intro h
    obtain ⟨f, hf⟩ := (hF i).2
    have hxy := hf ▸ h
    obtain ⟨a, rfl, rfl⟩ := hxy
    obtain ⟨ha, hfree⟩ := mem_sdiff.mp a.prop
    obtain ⟨j, hJ⟩ := P.covers i.val (Nat.zero_le _) i.isLt.le a.val ha
    obtain ⟨_, hNext⟩ := (hStep i.val i.isLt j).2 (hJ ▸ hfree)
    rw [hf] at hNext
    obtain ⟨c, hC, hTarget⟩ := hNext
    have hc : c = a := Subtype.ext (hC.trans hJ)
    exact ⟨j, hJ, (hc ▸ hTarget).symm, hfree⟩

/-- Build the special paths for a family of blocks and rounds while
retaining the global disjointness of all real filling arcs. -/
theorem exists_packed_special_path_systems [Fintype V]
    {B : Type*} {s : ℕ} (G : Digraph V) (A : B → ℕ → Finset V)
    (U W : B → Fin s → ℕ → Finset V) (t n r : ℕ) (ε η d a : ℝ)
    (hn : 0 < n) (hSize : ∀ b i, i ≤ t → (A b i).card = n)
    (hDisj : ∀ b i j, i ≤ t → j ≤ t → i ≠ j → Disjoint (A b i) (A b j))
    (hApart : ∀ p q : B × Fin t, p ≠ q →
      Disjoint (A p.1 p.2.val) (A q.1 q.2.val) ∨
      Disjoint (A p.1 (p.2.val+1)) (A q.1 (q.2.val+1)))
    (hU : ∀ b j i, i < t → U b j i ⊆ A b i)
    (hW : ∀ b j i, i < t → W b j i ⊆ A b (i+1))
    (hUW : ∀ b j i, i < t → (U b j i).card = (W b j i).card)
    (hPair : ∀ b i, i < t → IsLowerSuperregularPair G ε d (A b i) (A b (i+1)))
    (hη : 0 < η) (hηOne : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hBudget : (s:ℝ) ≤ a*((n:ℝ)*η))
    (hGap : 2*η < d) (hr : 0 < r) (hCut : (n:ℝ)*η ≤ (r:ℝ))
    (hMargin : ∀ b j i, i < t → (r:ℝ)+((U b j i).card:ℝ) ≤ (d-η)*(n:ℝ)) :
    let H (b : B) (j : Fin s) : Digraph V :=
      ⟨fun x y => G.Adj x y ∨ ∃ i < t, x ∈ U b j i ∧ y ∈ W b j i⟩
    ∃ P : ∀ b j, OrderedClusterPaths (H b j) (A b) (Fin n) 0 t,
      (∀ b j i, i < t → ∀ k, (P b j).vertex i k ∈ U b j i ↔
        (P b j).vertex (i+1) k ∈ W b j i) ∧
      (∀ b j i l, i ≤ t → l ≤ t → ∀ k k' : Fin n,
        (P b j).vertex i k = (P b j).vertex l k' → i = l ∧ k = k') ∧
      let real (p : (B × Fin t) × Fin s) :=
        specialPathFillingArcs (P p.1.1 p.2) (U p.1.1 p.2 p.1.2.val) p.1.2.val
      (∀ p, real p ≤ G) ∧ Pairwise (fun p q => Disjoint (real p) (real q)) ∧
      ((∀ p q : B × Fin t,
        Disjoint (A p.1 p.2.val) (A q.1 (q.2.val+1)) ∨
        Disjoint (A p.1 (p.2.val+1)) (A q.1 q.2.val)) →
        ∀ p q x y u v, (real p).Adj x y → (real q).Adj u v → s(x,y) = s(u,v) → p = q) := by
  classical
  intro H
  obtain ⟨F, hF, hFresh⟩ := exists_edge_disjoint_filling_matchings_on_pairs G
    (fun p : B × Fin t => A p.1 p.2.val) (fun p => A p.1 (p.2.val+1))
    (fun p j => U p.1 j p.2.val) (fun p j => W p.1 j p.2.val)
    n r ε η d a hn (fun p => hSize _ _ p.2.isLt.le) (fun p => hSize _ _ p.2.isLt)
    hApart (fun p j => hU _ j _ p.2.isLt) (fun p j => hW _ j _ p.2.isLt)
    (fun p j => hUW _ j _ p.2.isLt) (fun p => hPair _ _ p.2.isLt)
    hη hηOne ha hd hTol hBudget hGap hr hCut (fun p j => hMargin _ j _ p.2.isLt)
  have hPaths (b : B) (j : Fin s) := exists_special_path_system_of_prescribed_fillings G
    (A b) (U b j) (W b j) t n (fun i => F (b,i) j) (hSize b) (hDisj b)
    (hU b j) (hW b j) (hUW b j) (fun i => hF (b,i) j)
  choose P hStep hExact hCoordinates using hPaths
  let real (p : (B × Fin t) × Fin s) :=
    specialPathFillingArcs (P p.1.1 p.2) (U p.1.1 p.2 p.1.2.val) p.1.2.val
  have hGraph (p : (B × Fin t) × Fin s) : real p = F p.1 p.2 := hExact _ _ _
  have hRealFresh : Pairwise (fun p q => Disjoint (real p) (real q)) := by
    intro p q hNe
    rw [hGraph p, hGraph q]
    exact hFresh hNe
  refine ⟨P, hStep, hCoordinates, fun p => ?_, hRealFresh, ?_⟩
  · change real p ≤ G
    rw [hGraph p]
    exact (hF p.1 p.2).1
  intro hReverse p q x y u v hp hq he
  change (real p).Adj x y at hp
  change (real q).Adj u v at hq
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · by_contra hNe
    exact disjoint_iff_inf_le.mp (hRealFresh hNe) ⟨hp,hq⟩
  · obtain ⟨j, rfl, rfl, _⟩ := hp
    obtain ⟨k, hk, hl, _⟩ := hq
    have hPStart := (P p.1.1 p.2).part p.1.2.val (Nat.zero_le _) p.1.2.isLt.le j
    have hPEnd := (P p.1.1 p.2).part (p.1.2.val+1) (Nat.zero_le _) p.1.2.isLt j
    have hQStart := (P q.1.1 q.2).part q.1.2.val (Nat.zero_le _) q.1.2.isLt.le k
    have hQEnd := (P q.1.1 q.2).part (q.1.2.val+1) (Nat.zero_le _) q.1.2.isLt k
    rcases hReverse p.1 q.1 with h | h
    · exact (disjoint_left.mp h hPStart (hl ▸ hQEnd)).elim
    · exact (disjoint_left.mp h hPEnd (hk ▸ hQStart)).elim

/-- The arcs of one factor carry their block and transition labels
through the construction. The digraph is their union. -/
def specialFactorDigraph {B J : Type*} {H : B → Digraph V}
    {A : B → ℕ → Finset V} {t : ℕ} (P : ∀ b, OrderedClusterPaths (H b) (A b) J 0 t) :
    Digraph V :=
  ⟨fun x y => ∃ (p : B × Fin t) (j : J),
    (P p.1).vertex p.2.val j = x ∧ (P p.1).vertex (p.2.val+1) j = y⟩

/-- The union of the interval systems of one round is one-regular
when each core vertex occurs exactly once as a transition source
and once as a transition target. This is the boundary convention
in the canonical intervals of Definition 5.10. -/
theorem specialFactorDigraph_regular_on_core
    {B J : Type*} {H : B → Digraph V} {A : B → ℕ → Finset V} {t : ℕ}
    (P : ∀ b, OrderedClusterPaths (H b) (A b) J 0 t) (core : Finset V)
    (hCore : ∀ b i, i ≤ t → A b i ⊆ core)
    (hSources : ∀ v ∈ core, ∃! p : B × Fin t, v ∈ A p.1 p.2.val)
    (hTargets : ∀ v ∈ core, ∃! p : B × Fin t, v ∈ A p.1 (p.2.val+1)) :
    (∀ x y, (specialFactorDigraph P).Adj x y → x ∈ core ∧ y ∈ core) ∧
      ∀ v ∈ core, (∃! w, (specialFactorDigraph P).Adj v w) ∧
        (∃! w, (specialFactorDigraph P).Adj w v) := by
  constructor
  · rintro _ _ ⟨p, j, rfl, rfl⟩
    exact ⟨hCore _ _ p.2.isLt.le ((P p.1).part _ (Nat.zero_le _) p.2.isLt.le j),
      hCore _ _ p.2.isLt ((P p.1).part _ (Nat.zero_le _) p.2.isLt j)⟩
  intro v hv
  constructor
  · obtain ⟨p, hp, hpUnique⟩ := hSources v hv
    obtain ⟨j, hj⟩ := (P p.1).covers p.2.val (Nat.zero_le _) p.2.isLt.le v hp
    refine ⟨(P p.1).vertex (p.2.val+1) j, ⟨p,j,hj,rfl⟩, ?_⟩
    rintro w ⟨q,k,hk,hw⟩
    have hq := hpUnique q (hk ▸ (P q.1).part q.2.val (Nat.zero_le _) q.2.isLt.le k)
    subst q
    have he := (P p.1).injective p.2.val (Nat.zero_le _) p.2.isLt.le (hk.trans hj.symm)
    exact hw.symm.trans (congrArg ((P p.1).vertex (p.2.val+1)) he)
  · obtain ⟨p, hp, hpUnique⟩ := hTargets v hv
    obtain ⟨j, hj⟩ := (P p.1).covers (p.2.val+1) (Nat.zero_le _) p.2.isLt v hp
    refine ⟨(P p.1).vertex p.2.val j, ⟨p,j,rfl,hj⟩, ?_⟩
    rintro w ⟨q,k,hw,hk⟩
    have hq := hpUnique q (hk ▸ (P q.1).part (q.2.val+1) (Nat.zero_le _) q.2.isLt k)
    subst q
    have he := (P p.1).injective (p.2.val+1) (Nat.zero_le _) p.2.isLt (hk.trans hj.symm)
    exact hw.symm.trans (congrArg ((P p.1).vertex p.2.val) he)

end OverfullWork.ChenShan
