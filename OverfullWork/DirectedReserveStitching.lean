module

public import OverfullWork.RealDirectedSpanningLinkage
public import OverfullWork.DirectedPathCoverAbsorption
public import OverfullWork.DenseHall

@[expose] public section


/-! Join disjoint directed paths through a designated robust set,
as in GGKLO Corollary 4.8(c). The long path pieces and the attachment
arcs come from the bulk. The connectors lie entirely in the reserve. -/
namespace OverfullWork.DirectedReserveStitching

open Finset DirectedAbsorbingLadder DirectedListRoutes DirectedRobustExpansion
open scoped Classical
universe u v
variable {V : Type u} {W : Type v}

/-- The mixed graph used in the long-path construction. Only reserve
arcs are allowed between two reserve vertices. -/
def mixed (D : Digraph V) (Γ : Digraph W) (e : W ↪ V) : Digraph V where
  Adj x y := (∃ a b, Γ.Adj a b ∧ e a = x ∧ e b = y) ∨
    ((x ∉ Set.range e ∨ y ∉ Set.range e) ∧ D.Adj x y)

theorem chain_of_blocks (D : Digraph V) {I : Type*} (A : I → List V)
    (source target : I → V) (hSource : ∀ i, (A i).head? = some (source i))
    (hTarget : ∀ i, (A i).getLast? = some (target i))
    (hChain : ∀ i, (A i).IsChain D.Adj)
    (z : I) (order : List I)
    (hOrder : (order ++ [z]).IsChain (fun i j => D.Adj (target i) (source j))) :
    (order.flatMap A ++ [source z]).IsChain D.Adj := by
  induction order with
  | nil => exact .singleton _
  | cons i rest ih =>
    rw [List.flatMap_cons, List.append_assoc]
    apply (hChain i).append (ih hOrder.tail)
    intro x hx y hy
    have hX := Option.mem_some_iff.mp (hTarget i ▸ hx)
    subst x
    cases rest with
    | nil =>
      have hy' : source z = y := by simpa using hy
      subst y
      exact hOrder.rel
    | cons j rest =>
      have hNonempty : A j ≠ [] := by
        intro h
        have hh := hSource j
        simp [h] at hh
      change y ∈ ((A j ++ rest.flatMap A) ++ [source z]).head? at hy
      rw [List.append_assoc, List.head?_append_of_ne_nil _ hNonempty, hSource j] at hy
      have hY := Option.mem_some_iff.mp hy
      subst y
      exact hOrder.rel

/-- Given the actual reserve connectors, concatenate all pieces into a
single simple directed cycle. Each original path occurs as a segment,
and the support is exactly the reserve and the original path vertices. -/
theorem stitch_of_connectors (D : Digraph V) (Γ : Digraph W) (e : W ↪ V) {k : ℕ}
    (P : Fin (k+1) → PathRequest D) (Q : Fin (k+1) → PathRequest Γ)
    (hPDis : ∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices)
    (hOutside : ∀ i x, x ∈ (P i).vertices → x ∉ Set.range e)
    (hQDis : ∀ i j, i ≠ j → List.Disjoint (Q i).vertices (Q j).vertices)
    (hQSpan : ∀ w, ∃ i, w ∈ (Q i).vertices)
    (hFirst : ∀ i, D.Adj (P i).target (e (Q i).source))
    (hLast : ∀ i, D.Adj (e (Q i).target) (P (finRotate (k+1) i)).source) :
    ∃ T : List V, T.Nodup ∧ T.head? = some (P 0).source ∧
      (T ++ [(P 0).source]).IsChain (mixed D Γ e).Adj ∧
      (∀ x, x ∈ T ↔ x ∈ Set.range e ∨ ∃ i, x ∈ (P i).vertices) ∧
      ∀ i, List.IsInfix (P i).vertices T := by
  let part := fun i => (P i).vertices ++ (Q i).vertices.map e
  let a := fun i => (P i).source
  let b := fun i => e (Q i).target
  let order := List.ofFn (id : Fin (k+1) → Fin (k+1))
  let T := order.flatMap part
  have hA : ∀ i, (part i).head? = some (a i) := by
    intro i
    simp [part, PathRequest.vertices, a]
  have hB : ∀ i, (part i).getLast? = some (b i) := by
    intro i
    change ((P i).vertices ++ (Q i).vertices.map e).getLast? = _
    rw [List.getLast?_append_of_ne_nil _ (by simp [PathRequest.vertices]), List.getLast?_map]
    rw [show (Q i).vertices.getLast? = some (Q i).target from (Q i).route.2]
    rfl
  have eMem : ∀ i x, x ∈ (Q i).vertices.map e → x ∈ Set.range e := by
    intro i x hx
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hx
    exact ⟨w,rfl⟩
  have hChain : ∀ i, (part i).IsChain (mixed D Γ e).Adj := by
    intro i
    apply List.IsChain.append
    · apply (P i).route.1.imp_of_mem_imp
      intro x y hx _ h
      exact Or.inr ⟨Or.inl (hOutside i x hx),h⟩
    · apply (List.isChain_map (e : W → V)).mpr
      exact (Q i).route.1.imp (fun x y h => Or.inl ⟨x,y,h,rfl,rfl⟩)
    · intro x hx y hy
      have hEnd : (P i).vertices.getLast? = some (P i).target := (P i).route.2
      have hx' := Option.mem_some_iff.mp (hEnd ▸ hx)
      have hy' : e (Q i).source = y := by simpa [PathRequest.vertices] using hy
      subst x
      subst y
      exact Or.inr ⟨Or.inl (hOutside i _ (List.mem_of_mem_getLast? (by rw [hEnd]; rfl))),hFirst i⟩
  have hNext : ∀ i, (mixed D Γ e).Adj (b i) (a (finRotate (k+1) i)) :=
    fun i => Or.inr ⟨Or.inr (hOutside (finRotate (k+1) i) _
      (List.mem_cons_self ..)),hLast i⟩
  have hPairs : ∀ i j, i ≠ j → List.Disjoint (part i) (part j) := by
    intro i j hij x hi hj
    rcases List.mem_append.mp hi with hi|hi <;> rcases List.mem_append.mp hj with hj|hj
    · exact hPDis i j hij hi hj
    · exact hOutside i x hi (eMem j x hj)
    · exact hOutside j x hj (eMem i x hi)
    · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hi
      obtain ⟨v,hv,he⟩ := List.mem_map.mp hj
      have hh := e.injective he
      subst v
      exact hQDis i j hij hu hv
  have hSimple : ∀ i, (part i).Nodup := by
    intro i
    refine List.nodup_append.mpr ⟨(P i).simple,(Q i).simple.map e.injective,?_⟩
    intro x hx y hy he
    subst y
    exact hOutside i x hx (eMem i x hy)
  have hND : T.Nodup :=
    List.nodup_flatMap.mpr ⟨fun i _ => hSimple i,
      (List.nodup_ofFn.mpr Function.injective_id).imp (fun hij => hPairs _ _ hij)⟩
  have hCycle := chain_of_blocks (mixed D Γ e) part a b hA hB hChain 0 order
    (DirectedRungCycle.rotate_order hNext)
  have hHead : T.head? = some (a 0) := by
    have he : order = 0 :: List.ofFn (fun i : Fin k => i.succ) := List.ofFn_succ
    have hn : part 0 ≠ [] := by intro h; have hh := hA 0; simp [h] at hh
    change (order.flatMap part).head? = _
    rw [he,List.flatMap_cons,List.head?_append_of_ne_nil _ hn]
    exact hA 0
  refine ⟨T,hND,hHead,hCycle,?_,?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hx
      exact (List.mem_append.mp hi).elim (fun hp => Or.inr ⟨i,hp⟩) (fun hq => Or.inl (eMem i x hq))
    · intro hx
      obtain ⟨i,hi⟩ : ∃ i, x ∈ part i := by
        rcases hx with ⟨w,rfl⟩|⟨i,hi⟩
        · obtain ⟨i,hw⟩ := hQSpan w
          exact ⟨i,List.mem_append_right _ (List.mem_map.mpr ⟨w,hw,rfl⟩)⟩
        · exact ⟨i,List.mem_append_left _ hi⟩
      exact List.mem_flatMap.mpr ⟨i,List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩
  · intro i
    have hi : part i ∈ order.map part :=
      List.mem_map.mpr ⟨i,List.mem_ofFn.mpr ⟨i,rfl⟩,rfl⟩
    have hBlock : List.IsInfix (part i) T := List.infix_of_mem_flatten hi
    have hPiece : List.IsInfix (P i).vertices (part i) :=
      ⟨[],(Q i).vertices.map e,by simp [part]⟩
    exact hPiece.trans hBlock

private theorem exists_attachment_embedding [Fintype W] {k : ℕ} (D : Digraph V) (e : W ↪ V)
    (P : Fin (k+1) → PathRequest D)
    (hOut : ∀ i, 2*(k+1) ≤ ((univ : Finset W).filter (fun w => D.Adj (P i).target (e w))).card)
    (hIn : ∀ i, 2*(k+1) ≤ ((univ : Finset W).filter (fun w => D.Adj (e w) (P i).source)).card) :
    ∃ f : Fin (k+1) × Bool ↪ W, (∀ i,D.Adj (P i).target (e (f (i,false)))) ∧
      (∀ i,D.Adj (e (f (i,true))) (P (finRotate (k+1) i)).source) := by
  let R : Fin (k+1) × Bool → W → Prop := fun i w =>
    if i.2 then D.Adj (e w) (P (finRotate (k+1) i.1)).source else D.Adj (P i.1).target (e w)
  have hRow : ∀ a, 2*(k+1) ≤ ((univ : Finset W).filter (R a)).card := by
    rintro ⟨i,s⟩
    cases s
    · simpa [R] using hOut i
    · simpa [R] using hIn (finRotate (k+1) i)
  have hHall : ∀ S : Finset (Fin (k+1) × Bool),
      S.card ≤ ((univ : Finset W).filter (fun w => ∃ a ∈ S, R a w)).card := by
    intro S
    rcases S.eq_empty_or_nonempty with h|⟨a,ha⟩
    · simp [h]
    · have hSub : univ.filter (R a) ⊆ univ.filter (fun w => ∃ i ∈ S, R i w) := by
        intro w hw
        exact mem_filter.mpr ⟨mem_univ _,a,ha,(mem_filter.mp hw).2⟩
      have hCard : S.card ≤ 2*(k+1) := by
        simpa [Fintype.card_prod,Nat.mul_comm] using card_le_univ S
      exact hCard.trans ((hRow a).trans (card_le_card hSub))
  obtain ⟨f,hf,hR⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hHall
  exact ⟨⟨f,hf⟩,(fun i => by simpa [R] using hR (i,false)),fun i => by simpa [R] using hR (i,true)⟩

/-- Corollary 4.8(c) for paths entirely outside the reserve, in the
form used by the long-path step of Lemma 7.3(i). Reserve order and
attachment budgets are measured on the reserve itself. -/
theorem exists_stitched_cycle_threshold (ν τ α : ℝ) (hν : 0 < ν)
    (hντ : ν ≤ τ) (hτα : 256*τ ≤ α) (hα : α ≤ 1) :
    ∃ N : ℕ, ∀ {V : Type u} {W : Type v} [Fintype W]
      (D : Digraph V) (Γ : Digraph W) (e : W ↪ V),
      N ≤ Fintype.card W → IsRealRobust Γ ν τ →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (inDegree Γ v:ℝ)) →
      (∀ v, α*(Fintype.card W:ℝ) ≤ (outDegree Γ v:ℝ)) →
      ∀ (k : ℕ), ((k+1:ℕ):ℝ) ≤ (ν/4)^3*(Fintype.card W:ℝ) →
      ∀ P : Fin (k+1) → PathRequest D,
        (∀ i j, i ≠ j → List.Disjoint (P i).vertices (P j).vertices) →
        (∀ i x, x ∈ (P i).vertices → x ∉ Set.range e) →
        (∀ i, 2*(k+1) ≤ ((univ : Finset W).filter (fun w => D.Adj (P i).target (e w))).card) →
        (∀ i, 2*(k+1) ≤ ((univ : Finset W).filter (fun w => D.Adj (e w) (P i).source)).card) →
        ∃ T : List V, T.Nodup ∧ T.head? = some (P 0).source ∧
          (T ++ [(P 0).source]).IsChain (mixed D Γ e).Adj ∧
          (∀ x, x ∈ T ↔ x ∈ Set.range e ∨ ∃ i, x ∈ (P i).vertices) ∧
          ∀ i, List.IsInfix (P i).vertices T := by
  obtain ⟨N,hN⟩ := RobustSpanningLinkage.exists_directed_spanning_linkage_threshold.{v}
    ν τ α hν hντ hτα hα
  refine ⟨N,?_⟩
  intro V W _ D Γ e hn hR hIn hOut k hp P hDis hOutside hTo hFrom
  obtain ⟨f,hFirst,hLast⟩ := exists_attachment_embedding D e P hTo hFrom
  let a := fun i : Fin (k+1) => f (i,false)
  let b := fun i : Fin (k+1) => f (i,true)
  have ha : Function.Injective a := fun _ _ he => congrArg Prod.fst (f.injective he)
  have hb : Function.Injective b := fun _ _ he => congrArg Prod.fst (f.injective he)
  have hab : ∀ i j, a i ≠ b j := fun _ _ he => Bool.false_ne_true (congrArg Prod.snd (f.injective he))
  obtain ⟨tail,hPath,hQDis,hQSpan⟩ := hN Γ hn hR hIn hOut k hp a b ha hb hab
  let Q : Fin (k+1) → PathRequest Γ := fun i => ⟨a i,b i,tail i,(hPath i).1,(hPath i).2⟩
  exact stitch_of_connectors D Γ e P Q hDis hOutside hQDis hQSpan hFirst hLast

end OverfullWork.DirectedReserveStitching
