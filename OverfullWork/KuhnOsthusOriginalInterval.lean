module

public import OverfullWork.KuhnOsthusIntervalPathTransport
public import OverfullWork.KuhnOsthusLemma81

@[expose] public section


/-! Replace the complete exceptional sequence by its original two-arc
paths. This preserves the ordinary slots and keeps the exceptional
incidences away from both boundary clusters. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V : Type*} [Fintype V]

/-- The original arcs of a complete exceptional path system in one
interval and style. The first and last cluster are allowed to be
shared with the neighbouring intervals. -/
structure OriginalInterval (G : Digraph V) (Z A S T : Finset V) where
  digraph : Digraph V
  le : digraph ≤ G
  path_system : IsDirectedPathSystem digraph
  cover : CoversExceptional digraph Z
  no_internal : ∀ {x y}, digraph.Adj x y → x ∈ Z → y ∉ Z
  slots : ∀ x, x ∉ Z →
    ((∃ y, digraph.Adj x y) ↔ x ∈ A \ T) ∧ ((∃ y, digraph.Adj y x) ↔ x ∈ A \ S)
  exceptional_inside : ∀ x, x ∉ Z → IncidentTo (exceptionalPart digraph Z) x → x ∈ A \ (S ∪ T)
  exceptional_matching : ∀ {x y z}, x ∉ Z →
    (exceptionalPart digraph Z).Adj y x → ¬ (exceptionalPart digraph Z).Adj x z
  projection : ∃ (H : Digraph V) (P : IntervalPathCover H A S T) (endpoint : Bool × Z → V),
    Function.Injective endpoint ∧ (∀ p, endpoint p ∈ A \ (S ∪ T)) ∧
    (∀ z, P.digraph.Adj (endpoint (false,z)) (endpoint (true,z))) ∧
    ∀ x y, digraph.Adj x y ↔
      (P.digraph.Adj x y ∧ ¬ ∃ z : Z, endpoint (false,z) = x ∧ endpoint (true,z) = y) ∨
      (∃ z : Z, endpoint (false,z) = x ∧ z.val = y) ∨
      (∃ z : Z, z.val = x ∧ endpoint (true,z) = y)

/-- Equal interval and boundary sets give the same original paths. -/
def OriginalInterval.castSets {G : Digraph V} {Z A S T A' S' T' : Finset V}
    (P : OriginalInterval G Z A S T) (hA : A = A') (hS : S = S') (hT : T = T') :
    OriginalInterval G Z A' S' T' := hT ▸ hS ▸ hA ▸ P

omit [Fintype V] in
@[simp] theorem OriginalInterval.castSets_digraph {G : Digraph V} {Z A S T A' S' T' : Finset V}
    (P : OriginalInterval G Z A S T) (hA : A = A') (hS : S = S') (hT : T = T') :
    (P.castSets hA hS hT).digraph = P.digraph := by
  subst A'
  subst S'
  subst T'
  rfl

/-- Each protected shortcut is replaced by the two arcs through its
specified exceptional vertex. The endpoints of the shortcuts form a
matching in the interior. -/
theorem exists_original_interval_of_path_cover (G H : Digraph V) (Z A S T : Finset V)
    (P : IntervalPathCover H A S T) (endpoint : Bool × Z → V)
    (hDis : Disjoint A Z) (hEnd : ∀ p, endpoint p ∈ A \ (S ∪ T))
    (hInj : Function.Injective endpoint)
    (hKeep : ∀ z, P.digraph.Adj (endpoint (false,z)) (endpoint (true,z)))
    (hExc : ∀ z : Z, G.Adj (endpoint (false,z)) z ∧ G.Adj z (endpoint (true,z)))
    (hOrd : ∀ x y, P.digraph.Adj x y →
      (¬ ∃ z : Z, endpoint (false,z) = x ∧ endpoint (true,z) = y) → G.Adj x y) :
    Nonempty (OriginalInterval G Z A S T) := by
  classical
  let a (z : Z) := endpoint (false,z)
  let b (z : Z) := endpoint (true,z)
  let D := P.digraph
  let F : Digraph V := ⟨fun x y =>
    (D.Adj x y ∧ ¬ ∃ z : Z, a z = x ∧ b z = y) ∨
      (∃ z : Z, a z = x ∧ z.val = y) ∨ (∃ z : Z, z.val = x ∧ b z = y)⟩
  have hA (z : Z) : a z ∉ Z := fun h =>
    disjoint_left.mp hDis (mem_sdiff.mp (hEnd (false,z))).1 h
  have hB (z : Z) : b z ∉ Z := fun h =>
    disjoint_left.mp hDis (mem_sdiff.mp (hEnd (true,z))).1 h
  have hD {x y : V} (h : D.Adj x y) : x ∉ Z ∧ y ∉ Z :=
    ⟨fun hx => disjoint_left.mp hDis (mem_sdiff.mp ((P.slots x).1.mp ⟨y,h⟩)).1 hx,
      fun hy => disjoint_left.mp hDis (mem_sdiff.mp ((P.slots y).2.mp ⟨x,h⟩)).1 hy⟩
  have ha : Function.Injective a := fun _ _ h => congrArg Prod.snd (hInj h)
  have hb : Function.Injective b := fun _ _ h => congrArg Prod.snd (hInj h)
  have hab (z w : Z) : a z ≠ b w := fun h => Bool.false_ne_true (congrArg Prod.fst (hInj h))
  have hOutZ (z : Z) (y : V) : F.Adj z y ↔ b z = y := by
    constructor
    · rintro (h | ⟨w,hw,_⟩ | ⟨w,hw,hy⟩)
      · exact ((hD h.1).1 z.prop).elim
      · exact (hA w (hw.symm ▸ z.prop)).elim
      · exact (Subtype.ext hw : w = z) ▸ hy
    · intro h
      exact Or.inr (Or.inr ⟨z,rfl,h⟩)
  have hInZ (z : Z) (x : V) : F.Adj x z ↔ a z = x := by
    constructor
    · rintro (h | ⟨w,hx,hw⟩ | ⟨w,_,hw⟩)
      · exact ((hD h.1).2 z.prop).elim
      · exact (Subtype.ext hw : w = z) ▸ hx
      · exact (hB w (hw.symm ▸ z.prop)).elim
    · intro h
      exact Or.inr (Or.inl ⟨z,h,rfl⟩)
  have hOutOrd {x y : V} (hx : x ∉ Z) (h : F.Adj x y) :
      (D.Adj x y ∧ ¬ ∃ z : Z, a z = x ∧ b z = y) ∨ (∃ z : Z, a z = x ∧ z.val = y) := by
    rcases h with h | h | ⟨z,rfl,_⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (hx z.prop).elim
  have hInOrd {x y : V} (hy : y ∉ Z) (h : F.Adj x y) :
      (D.Adj x y ∧ ¬ ∃ z : Z, a z = x ∧ b z = y) ∨ (∃ z : Z, z.val = x ∧ b z = y) := by
    rcases h with h | ⟨z,_,rfl⟩ | h
    · exact Or.inl h
    · exact (hy z.prop).elim
    · exact Or.inr h
  have hOrdOut {x : V} (hx : x ∉ Z) :
      (∃ y, F.Adj x y) ↔ ∃ y, D.Adj x y := by
    constructor
    · rintro ⟨y,hy⟩
      rcases hOutOrd hx hy with h | ⟨z,he,_⟩
      · exact ⟨y,h.1⟩
      · exact ⟨b z,he ▸ hKeep z⟩
    · rintro ⟨y,hy⟩
      by_cases h : ∃ z : Z, a z = x ∧ b z = y
      · obtain ⟨z,hz,_⟩ := h
        exact ⟨z,Or.inr (Or.inl ⟨z,hz,rfl⟩)⟩
      · exact ⟨y,Or.inl ⟨hy,h⟩⟩
  have hOrdIn {x : V} (hx : x ∉ Z) :
      (∃ y, F.Adj y x) ↔ ∃ y, D.Adj y x := by
    constructor
    · rintro ⟨y,hy⟩
      rcases hInOrd hx hy with h | ⟨z,_,he⟩
      · exact ⟨y,h.1⟩
      · exact ⟨a z,he ▸ hKeep z⟩
    · rintro ⟨y,hy⟩
      by_cases h : ∃ z : Z, a z = y ∧ b z = x
      · obtain ⟨z,_,hz⟩ := h
        exact ⟨z,Or.inr (Or.inr ⟨z,rfl,hz⟩)⟩
      · exact ⟨y,Or.inl ⟨hy,h⟩⟩
  have hUniqueOut {x y z : V} (hy : F.Adj x y) (hz : F.Adj x z) : y = z := by
    by_cases hx : x ∈ Z
    · exact ((hOutZ ⟨x,hx⟩ y).mp hy).symm.trans ((hOutZ ⟨x,hx⟩ z).mp hz)
    · rcases hOutOrd hx hy with h | ⟨u,hu,hy⟩ <;> rcases hOutOrd hx hz with h' | ⟨v,hv,hz⟩
      · exact P.is_path_system.out_unique h.1 h'.1
      · exact (h.2 ⟨v,hv,P.is_path_system.out_unique (hv ▸ hKeep v) h.1⟩).elim
      · exact (h'.2 ⟨u,hu,P.is_path_system.out_unique (hu ▸ hKeep u) h'.1⟩).elim
      · exact hy.symm.trans ((congrArg Subtype.val (ha (hu.trans hv.symm))).trans hz)
  have hUniqueIn {x y z : V} (hy : F.Adj y x) (hz : F.Adj z x) : y = z := by
    by_cases hx : x ∈ Z
    · exact ((hInZ ⟨x,hx⟩ y).mp hy).symm.trans ((hInZ ⟨x,hx⟩ z).mp hz)
    · rcases hInOrd hx hy with h | ⟨u,hy,hu⟩ <;> rcases hInOrd hx hz with h' | ⟨v,hz,hv⟩
      · exact P.is_path_system.in_unique h.1 h'.1
      · exact (h.2 ⟨v,P.is_path_system.in_unique (hv ▸ hKeep v) h.1,hv⟩).elim
      · exact (h'.2 ⟨u,P.is_path_system.in_unique (hu ▸ hKeep u) h'.1,hu⟩).elim
      · exact hy.symm.trans ((congrArg Subtype.val (hb (hu.trans hv.symm))).trans hz)
  obtain ⟨rank,hRank⟩ := P.exists_rank
  let q (x : V) := if h : x ∈ Z then 2*rank (a ⟨x,h⟩)+1 else 2*rank x
  have hQ {x y : V} (h : F.Adj x y) : q x < q y := by
    rcases h with h | ⟨z,rfl,rfl⟩ | ⟨z,rfl,rfl⟩
    · have ht := hRank x y h.1
      simp only [q,dif_neg (hD h.1).1,dif_neg (hD h.1).2]
      omega
    · simp [q,hA z,z.prop]
    · have ht := hRank (a z) (b z) (hKeep z)
      simp only [q,dif_pos z.prop,dif_neg (hB z)]
      change 2*rank (a z)+1 < 2*rank (b z)
      omega
  have hAcyclic : NoDirectedCycle F := by
    intro x h
    have hR {v w : V} (h : Relation.TransGen F.Adj v w) : q v < q w := by
      induction h with
      | single h => exact hQ h
      | tail _ h ih => exact ih.trans (hQ h)
    exact lt_irrefl _ (hR h)
  have hCrossOut {x y : V} (hx : x ∉ Z) (h : (exceptionalPart F Z).Adj x y) :
      ∃ z : Z, a z = x ∧ z.val = y := by
    rcases hOutOrd hx h.1 with h' | h'
    · exact ((hD h'.1).2 (h.2.resolve_left hx)).elim
    · exact h'
  have hCrossIn {x y : V} (hx : x ∉ Z) (h : (exceptionalPart F Z).Adj y x) :
      ∃ z : Z, z.val = y ∧ b z = x := by
    rcases hInOrd hx h.1 with h' | h'
    · exact ((hD h'.1).1 (h.2.resolve_right hx)).elim
    · exact h'
  refine ⟨⟨F,?_,⟨hAcyclic,hUniqueOut,hUniqueIn⟩,?_,?_,?_,?_,?_,?_⟩⟩
  · rintro x y (h | ⟨z,rfl,rfl⟩ | ⟨z,rfl,rfl⟩)
    · exact hOrd x y h.1 h.2
    · exact (hExc z).1
    · exact (hExc z).2
  · intro x hx
    let z : Z := ⟨x,hx⟩
    exact ⟨⟨b z,(hOutZ z _).mpr rfl⟩,⟨a z,(hInZ z _).mpr rfl⟩⟩
  · intro x y h hx
    exact ((hOutZ ⟨x,hx⟩ y).mp h) ▸ hB ⟨x,hx⟩
  · intro x hx
    exact ⟨hOrdOut hx |>.trans (P.slots x).1,hOrdIn hx |>.trans (P.slots x).2⟩
  · intro x hx h
    rcases h with ⟨y,hy⟩ | ⟨y,hy⟩
    · obtain ⟨z,rfl,_⟩ := hCrossOut hx hy
      exact hEnd (false,z)
    · obtain ⟨z,_,rfl⟩ := hCrossIn hx hy
      exact hEnd (true,z)
  · intro x y z hx hy hz
    obtain ⟨u,_,hu⟩ := hCrossIn hx hy
    obtain ⟨v,hv,_⟩ := hCrossOut hx hz
    exact hab v u (hv.trans hu.symm)
  · exact ⟨H,P,endpoint,hInj,hEnd,hKeep,fun _ _ => Iff.rfl⟩

/-- Connect the reopened quotient to the physical original graph.
The regular arcs lift into the host. The distinguished shortcuts
lift into the host only after inserting their exceptional vertices. -/
theorem exists_original_interval_of_reopened_quotient {W : Type*}
    (G : Digraph V) (D R : Digraph W) (Z A S T : Finset V) (B : Finset W)
    (e : W ⊕ B ≃ A) (first : B ≃ S) (last : B ≃ T)
    (hFirst : ∀ b : B, (e (Sum.inl b.val)).val = (first b).val)
    (hLast : ∀ b : B, (e (Sum.inr b)).val = (last b).val)
    (endpoint : Bool × Z → V)
    (hDis : Disjoint A Z) (hEnd : ∀ p, endpoint p ∈ A \ (S ∪ T))
    (hInj : Function.Injective endpoint)
    (hExc : ∀ z : Z, G.Adj (endpoint (false,z)) z ∧ G.Adj z (endpoint (true,z)))
    (hArc : ∀ x y, (splitIntervalDigraph (D ⊔ R) B).Adj x y →
      G.Adj (e x).val (e y).val ∨
        ∃ z : Z, endpoint (false,z) = (e x).val ∧ endpoint (true,z) = (e y).val)
    (hKeep : ∀ z : Z, ∃ x y : W, D.Adj x y ∧
      (e (Sum.inl x)).val = endpoint (false,z) ∧ (e (Sum.inl y)).val = endpoint (true,z))
    (P : B → DirectedAbsorbingLadder.PathRequest (splitIntervalDigraph (D ⊔ R) B))
    (start : Equiv.Perm B)
    (hEnds : ∀ b, (P b).source = Sum.inl (start b).val ∧ (P b).target = Sum.inr b)
    (hApart : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices)
    (hCover : ∀ v, ∃ i, v ∈ (P i).vertices)
    (hProtected : ∀ x y, D.Adj x y →
      ∃ i, [(Sum.inl x : W ⊕ B),Sum.inl y] <:+: (P i).vertices) :
    Nonempty (OriginalInterval G Z A S T) := by
  let M : Digraph V := ⟨fun x y =>
    ∃ z : Z, endpoint (false,z) = x ∧ endpoint (true,z) = y⟩
  obtain ⟨Q,hQ⟩ := transport_split_interval_paths (G ⊔ M) (D ⊔ R) A S T B e first last
    hFirst hLast (fun x y h => (Digraph.sup_adj _ _ _ _).mpr (hArc x y h))
    P start hEnds hApart hCover
  refine exists_original_interval_of_path_cover G (G ⊔ M) Z A S T Q endpoint hDis hEnd hInj ?_ hExc ?_
  · intro z
    obtain ⟨x,y,hxy,hx,hy⟩ := hKeep z
    rw [←hx,←hy]
    exact hQ (Sum.inl x) (Sum.inl y) (hProtected x y hxy)
  · intro x y h hNo
    exact ((Digraph.sup_adj _ _ _ _).mp (Q.digraph_le h)).resolve_right hNo

universe u

/-- Local form of Lemma 7.6 with physical coordinates and explicit
superregularity margins. The output is in the original digraph and
can be used as one piece in the deletion induction. -/
theorem exists_original_interval_of_wrapped_superregular_pairs
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) :
    ∃ N : ℕ, ∀ {X : Type*} [Fintype X] {W : Type u} [Fintype W] {n : ℕ}
      (G : Digraph X) (D R : Digraph W) (Z A S T : Finset X)
      (cluster : W → Fin (n+1)) (r : Fin (n+1) → ℕ),
      let B := (univ : Finset W).filter (fun x => cluster x = 0)
      let O := freeOut D cluster
      let I i := freeIn D cluster (finRotate (n+1) i)
      ∀ (e : W ⊕ B ≃ A) (first : B ≃ S) (last : B ≃ T)
        (endpoint : Bool × Z → X),
        (∀ b : B, (e (Sum.inl b.val)).val = (first b).val) →
        (∀ b : B, (e (Sum.inr b)).val = (last b).val) →
        Disjoint A Z → (∀ p, endpoint p ∈ A \ (S ∪ T)) → Function.Injective endpoint →
        (∀ z : Z, G.Adj (endpoint (false,z)) z ∧ G.Adj z (endpoint (true,z))) →
        (∀ x y, (splitIntervalDigraph (D ⊔ R) B).Adj x y →
          G.Adj (e x).val (e y).val ∨
            ∃ z : Z, endpoint (false,z) = (e x).val ∧ endpoint (true,z) = (e y).val) →
        (∀ z : Z, ∃ x y : W, D.Adj x y ∧
          (e (Sum.inl x)).val = endpoint (false,z) ∧ (e (Sum.inl y)).val = endpoint (true,z)) →
        IsDirectedPathSystem D → (∀ x y, D.Adj x y → y ∉ B) →
        (∀ i, (O i).card = (I i).card) →
        (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ O i) →
        (∀ i, N ≤ (O i).card) →
        (∀ i, 0 < r i ∧ ε*((O i).card:ℝ) ≤ (r i:ℝ) ∧ (r i:ℝ) ≤ (d-2*ε)*((O i).card:ℝ)) →
        (∀ i, IsSuperregularPair R ε d (O i) (I i)) →
        Nonempty (OriginalInterval G Z A S T) := by
  obtain ⟨N,hN⟩ := exists_exceptional_interval_completion_of_superregular_pairs.{u}
    d ε ν τ γ hν hWidth hε hτγ hγ hd hCost hDegrees
  refine ⟨N,?_⟩
  intro X _ W _ n G D R Z A S T cluster r B O I e first last endpoint
    hFirst hLast hDis hEnd hInj hExc hArc hKeep hPath hInside hBal hOverlap hSize hr hPair
  obtain ⟨P,start,hPends,hPart,hCover,hProtected⟩ :=
    hN D R cluster r hPath hInside hBal hOverlap hSize hr hPair
  exact exists_original_interval_of_reopened_quotient G D R Z A S T B e first last
    hFirst hLast endpoint hDis hEnd hInj hExc hArc hKeep P start hPends hPart hCover hProtected

/-- Local form of Lemma 7.6 with physical coordinates and explicit
individual superregularity parameters. The output is in the original digraph and
can be used as one piece in the deletion induction. -/
theorem exists_original_interval_of_wrapped_lower_superregular_pairs
    (d ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) :
    ∃ N : ℕ, ∀ {X : Type*} [Fintype X] {W : Type u} [Fintype W] {n : ℕ}
      (G : Digraph X) (D R : Digraph W) (Z A S T : Finset X)
      (cluster : W → Fin (n+1)) (r : Fin (n+1) → ℕ),
      let B := (univ : Finset W).filter (fun x => cluster x = 0)
      let O := freeOut D cluster
      let I i := freeIn D cluster (finRotate (n+1) i)
      ∀ (e : W ⊕ B ≃ A) (first : B ≃ S) (last : B ≃ T)
        (endpoint : Bool × Z → X),
        (∀ b : B, (e (Sum.inl b.val)).val = (first b).val) →
        (∀ b : B, (e (Sum.inr b)).val = (last b).val) →
        Disjoint A Z → (∀ p, endpoint p ∈ A \ (S ∪ T)) → Function.Injective endpoint →
        (∀ z : Z, G.Adj (endpoint (false,z)) z ∧ G.Adj z (endpoint (true,z))) →
        (∀ x y, (splitIntervalDigraph (D ⊔ R) B).Adj x y →
          G.Adj (e x).val (e y).val ∨
            ∃ z : Z, endpoint (false,z) = (e x).val ∧ endpoint (true,z) = (e y).val) →
        (∀ z : Z, ∃ x y : W, D.Adj x y ∧
          (e (Sum.inl x)).val = endpoint (false,z) ∧ (e (Sum.inl y)).val = endpoint (true,z)) →
        IsDirectedPathSystem D → (∀ x y, D.Adj x y → y ∉ B) →
        (∀ i, (O i).card = (I i).card) →
        (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ O i) →
        (∀ i, N ≤ (O i).card) →
        (∀ i, 0 < r i ∧ ε*((O i).card:ℝ) ≤ (r i:ℝ) ∧ (r i:ℝ) ≤ (d-2*ε)*((O i).card:ℝ)) →
        (∀ i, IsLowerSuperregularPair R ε d (O i) (I i)) →
        Nonempty (OriginalInterval G Z A S T) := by
  obtain ⟨N,hN⟩ := exists_exceptional_interval_completion_of_lower_superregular_pairs.{u}
    d ε ν τ γ hν hWidth hε hτγ hγ hd hCost hDegrees
  refine ⟨N,?_⟩
  intro X _ W _ n G D R Z A S T cluster r B O I e first last endpoint
    hFirst hLast hDis hEnd hInj hExc hArc hKeep hPath hInside hBal hOverlap hSize hr hPair
  obtain ⟨P,start,hPends,hPart,hCover,hProtected⟩ :=
    hN D R cluster r hPath hInside hBal hOverlap hSize hr hPair
  exact exists_original_interval_of_reopened_quotient G D R Z A S T B e first last
    hFirst hLast endpoint hDis hEnd hInj hExc hArc hKeep P start hPends hPart hCover hProtected

end OverfullWork.DirectedRobustExpansion
