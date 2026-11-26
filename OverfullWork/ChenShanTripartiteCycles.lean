module

public import OverfullWork.ChenShanDirectedCycles
public import OverfullWork.ChenShanTripartiteCompletion
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW}

/-- Orient each edge around the three classes in the order A, B, W. -/
def tripartiteArc (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop) :
    A ⊕ (B ⊕ W) → A ⊕ (B ⊕ W) → Prop
  | .inl a, .inr (.inl b) => E a b
  | .inr (.inl b), .inr (.inr w) => r b w
  | .inr (.inr w), .inl a => l a w
  | _, _ => False

noncomputable def tripartiteArcs [Fintype A] [Fintype B] [Fintype W]
    (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop) :
    Finset ((A ⊕ (B ⊕ W)) × (A ⊕ (B ⊕ W))) :=
  univ.filter (fun e => tripartiteArc E l r e.1 e.2)

private theorem card_filter_arcs_out {V : Type*} [Fintype V] (P : V → V → Prop) (v : V) :
    ((univ.filter (fun e : V × V => P e.1 e.2)).filter (fun e => e.1 = v)).card =
      ∑ w : V, if P v w then 1 else 0 := by
  let i : V ↪ V × V := ⟨fun w => (v,w), fun _ _ h => congrArg Prod.snd h⟩
  have h : ((univ.filter (fun e : V × V => P e.1 e.2)).filter (fun e => e.1 = v)) =
      (univ.filter (P v)).map i := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨y,h,rfl⟩
    · rintro ⟨z,h,he⟩
      change (v,z) = (x,y) at he
      cases he
      exact ⟨h,rfl⟩
  rw [h,card_map,card_filter]

private theorem card_filter_arcs_in {V : Type*} [Fintype V] (P : V → V → Prop) (v : V) :
    ((univ.filter (fun e : V × V => P e.1 e.2)).filter (fun e => e.2 = v)).card =
      ∑ w : V, if P w v then 1 else 0 := by
  let i : V ↪ V × V := ⟨fun w => (w,v), fun _ _ h => congrArg Prod.fst h⟩
  have h : ((univ.filter (fun e : V × V => P e.1 e.2)).filter (fun e => e.2 = v)) =
      (univ.filter (fun w => P w v)).map i := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨x,h,rfl⟩
    · rintro ⟨z,h,he⟩
      change (z,v) = (x,y) at he
      cases he
      exact ⟨h,rfl⟩
  rw [h,card_map,card_filter]

theorem arcBalanced_of_tripartiteLocallyBalanced [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (h : TripartiteLocallyBalanced E l r) : ArcBalanced (tripartiteArcs E l r) := by
  intro v
  unfold tripartiteArcs
  rw [card_filter_arcs_out,card_filter_arcs_in]
  rcases v with a | (b | w)
  · have ht := h.1 a
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter, card_filter] at ht
    simp [Fintype.sum_sum_type,tripartiteArc, -Finset.sum_boole]
    convert ht using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split_ifs <;> simp_all
  · have ht := (h.2.1 b).symm
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter, card_filter] at ht
    simp [Fintype.sum_sum_type,tripartiteArc, -Finset.sum_boole]
    convert ht using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split_ifs <;> simp_all
  · have ht := h.2.2 w
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter, card_filter] at ht
    simp [Fintype.sum_sum_type,tripartiteArc, -Finset.sum_boole]
    convert ht using 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> split_ifs <;> simp_all

private def tripartiteClass : A ⊕ (B ⊕ W) → ZMod 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

private theorem tripartiteClass_step {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    {v w : A ⊕ (B ⊕ W)} (h : tripartiteArc E l r v w) :
    tripartiteClass w = tripartiteClass v + 1 := by
  rcases v with a | (b | x) <;> rcases w with a' | (b' | x') <;>
    simp [tripartiteArc] at h <;> simp only [tripartiteClass] <;> decide

theorem tripartite_cycle_length_dvd [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (n : ℕ) (f : Fin (n+1) ↪ A ⊕ (B ⊕ W))
    (h : cycleArcs n f ⊆ tripartiteArcs E l r) : 3 ∣ n+1 := by
  have hstep (i : Fin (n+1)) :
      tripartiteClass (f (finRotate (n+1) i)) = tripartiteClass (f i) + 1 := by
    have hi : (f i, f (finRotate (n+1) i)) ∈ cycleArcs n f :=
      mem_map.mpr ⟨i,mem_univ _,rfl⟩
    exact tripartiteClass_step (mem_filter.mp (h hi)).2
  have hs := Equiv.sum_comp (finRotate (n+1)) (fun i => tripartiteClass (f i))
  simp_rw [hstep] at hs
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_one] at hs
  exact (ZMod.natCast_eq_zero_iff _ _).mp (add_eq_left.mp hs)

theorem exists_tripartite_cycle_decomposition [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (h : TripartiteLocallyBalanced E l r) :
    let F := tripartiteArcs E l r
    ∃ L : List (Finset ((A ⊕ (B ⊕ W)) × (A ⊕ (B ⊕ W)))),
      L.Pairwise Disjoint ∧
      (∀ C ∈ L, ∃ n : ℕ, ∃ f : Fin (n+1) ↪ A ⊕ (B ⊕ W),
        cycleArcs n f = C ∧ 3 ∣ n+1) ∧
      (∀ e, e ∈ F ↔ ∃ C ∈ L, e ∈ C) ∧ (L.map Finset.card).sum = F.card := by
  obtain ⟨L,hDisj,hCycles,hCover,hCount⟩ := exists_directed_cycle_decomposition _
    (arcBalanced_of_tripartiteLocallyBalanced h)
  refine ⟨L,hDisj,?_,hCover,hCount⟩
  intro C hC
  obtain ⟨n,f,rfl⟩ := hCycles C hC
  exact ⟨n,f,rfl,tripartite_cycle_length_dvd n f (fun e he => (hCover e).mpr ⟨_,hC,he⟩)⟩

private def cycleLayerEquiv {J : Type*} (q : Equiv.Perm J) (P Q : J → Prop)
    (h : ∀ i, Q (q i) ↔ P i) : {i // P i} ≃ {i // Q i} where
  toFun i := ⟨q i.val, (h i.val).mpr i.property⟩
  invFun i := ⟨q.symm i.val, (h _).mp (by simpa using i.property)⟩
  left_inv i := Subtype.ext (q.symm_apply_apply i.val)
  right_inv i := Subtype.ext (q.apply_symm_apply i.val)

/-- The three classes of an oriented cycle, indexed by its A-vertices.
The permutation sends an A-vertex to the next A-vertex around the cycle. -/
theorem exists_tripartite_cycle_labels [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (n : ℕ) (f : Fin (n+1) ↪ A ⊕ (B ⊕ W))
    (h : cycleArcs n f ⊆ tripartiteArcs E l r) :
    let I := {j : Fin (n+1) // ∃ a : A, f j = Sum.inl a}
    ∃ (s : Equiv.Perm I) (a : I ↪ A) (b : I ↪ B) (w : I ↪ W),
      ∀ e, e ∈ cycleArcs n f ↔
        (∃ i : I, e = (Sum.inl (a i), Sum.inr (Sum.inl (b i)))) ∨
        (∃ i : I, e = (Sum.inr (Sum.inl (b i)), Sum.inr (Sum.inr (w i)))) ∨
        (∃ i : I, e = (Sum.inr (Sum.inr (w i)), Sum.inl (a (s i)))) := by
  let q := finRotate (n+1)
  let PA (i : Fin (n+1)) := ∃ a : A, f i = Sum.inl a
  let PB (i : Fin (n+1)) := ∃ b : B, f i = Sum.inr (Sum.inl b)
  let PW (i : Fin (n+1)) := ∃ w : W, f i = Sum.inr (Sum.inr w)
  have hArc (i : Fin (n+1)) : tripartiteArc E l r (f i) (f (q i)) :=
    (mem_filter.mp (h (mem_map.mpr ⟨i,mem_univ _,rfl⟩))).2
  have hLayers (i : Fin (n+1)) : (PB (q i) ↔ PA i) ∧
      (PW (q i) ↔ PB i) ∧ (PA (q i) ↔ PW i) := by
    have hi := hArc i
    rcases h₁ : f i with a | (b | w) <;>
      rcases h₂ : f (q i) with a' | (b' | w') <;>
      simp [h₁, h₂, tripartiteArc] at hi <;>
      simp [PA, PB, PW, h₁, h₂]
  let u := cycleLayerEquiv q PA PB (fun i => (hLayers i).1)
  let v := cycleLayerEquiv q PB PW (fun i => (hLayers i).2.1)
  let z := cycleLayerEquiv q PW PA (fun i => (hLayers i).2.2)
  let s := (u.trans v).trans z
  let a₀ (i : {i // PA i}) := i.property.choose
  let b₀ (i : {i // PB i}) := i.property.choose
  let w₀ (i : {i // PW i}) := i.property.choose
  have ha (i : {i // PA i}) : f i.val = Sum.inl (a₀ i) := i.property.choose_spec
  have hb (i : {i // PB i}) : f i.val = Sum.inr (Sum.inl (b₀ i)) := i.property.choose_spec
  have hw (i : {i // PW i}) : f i.val = Sum.inr (Sum.inr (w₀ i)) := i.property.choose_spec
  let a : {i // PA i} ↪ A := ⟨a₀,fun i j hEq =>
    Subtype.ext (f.injective ((ha i).trans ((congrArg Sum.inl hEq).trans (ha j).symm)))⟩
  let b : {i // PA i} ↪ B := ⟨fun i => b₀ (u i),fun i j hEq =>
    u.injective (Subtype.ext (f.injective ((hb (u i)).trans
      ((congrArg (fun b : B => Sum.inr (Sum.inl b)) hEq).trans (hb (u j)).symm))))⟩
  let w : {i // PA i} ↪ W := ⟨fun i => w₀ (v (u i)),fun i j hEq =>
    (u.trans v).injective (Subtype.ext (f.injective ((hw (v (u i))).trans
      ((congrArg (fun w : W => Sum.inr (Sum.inr w)) hEq).trans (hw (v (u j))).symm))))⟩
  have hAB (i : {i // PA i}) :
      (f i.val, f (q i.val)) = (Sum.inl (a i), Sum.inr (Sum.inl (b i))) :=
    Prod.ext (ha i) (hb (u i))
  have hBW (i : {i // PA i}) :
      (f (u i).val, f (q (u i).val)) = (Sum.inr (Sum.inl (b i)), Sum.inr (Sum.inr (w i))) :=
    Prod.ext (hb (u i)) (hw (v (u i)))
  have hWA (i : {i // PA i}) :
      (f (v (u i)).val, f (q (v (u i)).val)) =
        (Sum.inr (Sum.inr (w i)), Sum.inl (a (s i))) :=
    Prod.ext (hw (v (u i))) (ha (s i))
  refine ⟨s,a,b,w,?_⟩
  intro e
  constructor
  · intro he
    obtain ⟨j,_,rfl⟩ := mem_map.mp he
    change (∃ i, (f j, f (q j)) = _) ∨ (∃ i, (f j, f (q j)) = _) ∨
      (∃ i, (f j, f (q j)) = _)
    rcases hj : f j with a' | (b' | w')
    · exact Or.inl ⟨⟨j,a',hj⟩,by simpa only [Subtype.coe_mk, hj] using hAB ⟨j,a',hj⟩⟩
    · obtain ⟨i,hi⟩ := u.surjective (⟨j,b',hj⟩ : {i // PB i})
      exact Or.inr (Or.inl ⟨i,by simpa only [hi, Subtype.coe_mk, hj] using hBW i⟩)
    · obtain ⟨i,hi⟩ := (u.trans v).surjective (⟨j,w',hj⟩ : {i // PW i})
      change v (u i) = ⟨j,w',hj⟩ at hi
      exact Or.inr (Or.inr ⟨i,by simpa only [hi, Subtype.coe_mk, hj] using hWA i⟩)
  · rintro (⟨i,hi⟩ | ⟨i,hi⟩ | ⟨i,hi⟩)
    · exact mem_map.mpr ⟨i.val,mem_univ _,(hAB i).trans hi.symm⟩
    · exact mem_map.mpr ⟨(u i).val,mem_univ _,(hBW i).trans hi.symm⟩
    · exact mem_map.mpr ⟨(v (u i)).val,mem_univ _,(hWA i).trans hi.symm⟩

/-- The absorber uses one index for each group of three cycle edges. -/
theorem tripartite_cycle_index_count [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (n : ℕ) (f : Fin (n+1) ↪ A ⊕ (B ⊕ W))
    (h : cycleArcs n f ⊆ tripartiteArcs E l r) :
    3 * Fintype.card {j : Fin (n+1) // ∃ a : A, f j = Sum.inl a} = (cycleArcs n f).card := by
  obtain ⟨s,a,b,w,hLabels⟩ := exists_tripartite_cycle_labels n f h
  let I := {j : Fin (n+1) // ∃ a : A, f j = Sum.inl a}
  let g : I ⊕ (I ⊕ I) → (A ⊕ (B ⊕ W)) × (A ⊕ (B ⊕ W)) :=
    Sum.elim (fun i => (Sum.inl (a i), Sum.inr (Sum.inl (b i))))
      (Sum.elim (fun i => (Sum.inr (Sum.inl (b i)), Sum.inr (Sum.inr (w i))))
        (fun i => (Sum.inr (Sum.inr (w i)), Sum.inl (a (s i)))))
  have hIn (i) : g i ∈ cycleArcs n f := by
    apply (hLabels _).mpr
    rcases i with i | (i | i)
    · exact Or.inl ⟨i,rfl⟩
    · exact Or.inr (Or.inl ⟨i,rfl⟩)
    · exact Or.inr (Or.inr ⟨i,rfl⟩)
  let p : I ⊕ (I ⊕ I) → ↥(cycleArcs n f) := fun i => ⟨g i,hIn i⟩
  have hp : Function.Bijective p := by
    constructor
    · intro x y hxy
      have hxy' : (g x).1 = (g y).1 :=
        congrArg (fun e : ↥(cycleArcs n f) => e.val.1) hxy
      rcases x with i | (i | i) <;> rcases y with j | (j | j) <;>
        simp [g, a.injective.eq_iff, b.injective.eq_iff, w.injective.eq_iff] at hxy' ⊢ <;>
        assumption
    · intro e
      rcases (hLabels _).mp e.property with (⟨i,hi⟩ | ⟨i,hi⟩ | ⟨i,hi⟩)
      · exact ⟨.inl i,Subtype.ext hi.symm⟩
      · exact ⟨.inr (.inl i),Subtype.ext hi.symm⟩
      · exact ⟨.inr (.inr i),Subtype.ext hi.symm⟩
  have hc := Fintype.card_congr (Equiv.ofBijective p hp)
  simp only [Fintype.card_sum, Fintype.card_coe] at hc
  change 3 * Fintype.card I = _
  omega

/-- Labels in the `Fin` form used to place the simultaneous absorbers. -/
theorem exists_tripartite_cycle_fin_labels [Fintype A] [Fintype B] [Fintype W]
    {E : A → B → Prop} {l : A → W → Prop} {r : B → W → Prop}
    (n : ℕ) (f : Fin (n+1) ↪ A ⊕ (B ⊕ W))
    (h : cycleArcs n f ⊆ tripartiteArcs E l r) :
    ∃ (k : ℕ) (s : Equiv.Perm (Fin k)) (a : Fin k ↪ A) (b : Fin k ↪ B) (w : Fin k ↪ W),
      3*k = n+1 ∧ ∀ e, e ∈ cycleArcs n f ↔
        (∃ i, e = (Sum.inl (a i), Sum.inr (Sum.inl (b i)))) ∨
        (∃ i, e = (Sum.inr (Sum.inl (b i)), Sum.inr (Sum.inr (w i)))) ∨
        (∃ i, e = (Sum.inr (Sum.inr (w i)), Sum.inl (a (s i)))) := by
  obtain ⟨s,a,b,w,hLabels⟩ := exists_tripartite_cycle_labels n f h
  let I := {j : Fin (n+1) // ∃ a : A, f j = Sum.inl a}
  let τ := Fintype.equivFin I
  let σ : Equiv.Perm (Fin (Fintype.card I)) := (τ.symm.trans s).trans τ
  have hCount := tripartite_cycle_index_count n f h
  rw [cycleArcs_card] at hCount
  refine ⟨Fintype.card I,σ,τ.symm.toEmbedding.trans a,τ.symm.toEmbedding.trans b,
    τ.symm.toEmbedding.trans w,hCount,?_⟩
  intro e
  rw [hLabels]
  have hRelabel (P : I → Prop) : (∃ i, P i) ↔ ∃ j, P (τ.symm j) :=
    ⟨fun ⟨i,hi⟩ => ⟨τ i, by simpa only [Equiv.symm_apply_apply] using hi⟩,
      fun ⟨j,hj⟩ => ⟨τ.symm j,hj⟩⟩
  rw [hRelabel, hRelabel, hRelabel]
  simp only [σ, Equiv.trans_apply, Equiv.symm_apply_apply, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply]

end OverfullWork.ChenShan
