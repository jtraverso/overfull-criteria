module

public import OverfullWork.ChenShanAbsorberCatalogue
public import OverfullWork.ChenShanEmbeddedAbsorber

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical BigOperators

universe uA uB uW

variable {A : Type uA} {B : Type uB} {W : Type uW} [Fintype A] [Fintype B] [Fintype W]

omit [Fintype A] [Fintype B] [Fintype W] in
private theorem FootprintEdge.reverse {Q Z : Finset (TripartiteVertex A B W)} {u v}
    (h : FootprintEdge Q Z u v) : FootprintEdge Q Z v u := h.symm

private theorem tripartiteArcs_or
    (E F : A → B → Prop) (l l' : A → W → Prop) (r r' : B → W → Prop) :
    tripartiteArcs (fun a b => E a b ∨ F a b) (fun a w => l a w ∨ l' a w)
      (fun b w => r b w ∨ r' b w) = tripartiteArcs E l r ∪ tripartiteArcs F l' r' := by
  ext e
  rcases e with ⟨u,v⟩
  rcases u with a | (b | w) <;> rcases v with a' | (b' | w') <;> simp [tripartiteArc]

private theorem tripartiteArcs_indexed {J : Type*} (S : Finset J)
    (E : J → A → B → Prop) (l : J → A → W → Prop) (r : J → B → W → Prop) :
    tripartiteArcs (fun a b => ∃ j ∈ S, E j a b) (fun a w => ∃ j ∈ S, l j a w)
      (fun b w => ∃ j ∈ S, r j b w) = S.biUnion (fun j => tripartiteArcs (E j) (l j) (r j)) := by
  ext e
  rcases e with ⟨u,v⟩
  rcases u with a | (b | w) <;> rcases v with a' | (b' | w') <;> simp [tripartiteArc]

private theorem tripartiteArcs_eq_relations {E F : A → B → Prop}
    {l l' : A → W → Prop} {r r' : B → W → Prop}
    (h : tripartiteArcs E l r = tripartiteArcs F l' r') : E = F ∧ l = l' ∧ r = r' := by
  have hMem (e : TripartiteVertex A B W × TripartiteVertex A B W) :
      e ∈ tripartiteArcs E l r ↔ e ∈ tripartiteArcs F l' r' := by rw [h]
  refine ⟨?_,?_,?_⟩
  · funext a b
    exact propext (by simpa [tripartiteArc] using hMem (.inl a,.inr (.inl b)))
  · funext a w
    exact propext (by simpa [tripartiteArc] using hMem (.inr (.inr w),.inl a))
  · funext b w
    exact propext (by simpa [tripartiteArc] using hMem (.inr (.inl b),.inr (.inr w)))

private theorem tripartite_decomposition_of_arc_partition {J : Type*} (S : Finset J)
    (E : J → A → B → Prop) (l : J → A → W → Prop) (r : J → B → W → Prop)
    {F : A → B → Prop} {l' : A → W → Prop} {r' : B → W → Prop}
    (hUnion : S.biUnion (fun j => tripartiteArcs (E j) (l j) (r j)) = tripartiteArcs F l' r')
    (hDisj : (↑S : Set J).PairwiseDisjoint (fun j => tripartiteArcs (E j) (l j) (r j)))
    (hD : ∀ j ∈ S, Nonempty (TripartiteTriangleDecomposition (E j) (l j) (r j))) :
    Nonempty (TripartiteTriangleDecomposition F l' r') := by
  obtain ⟨hE,hl,hr⟩ := tripartiteArcs_eq_relations ((tripartiteArcs_indexed S E l r).trans hUnion)
  rw [← hE,← hl,← hr]
  apply tripartite_decomposition_finite_union S E l r hD
  · intro i hi j hj hij a b h₁ h₂
    have h₁' := (mem_tripartiteArcs (E := E i) (l := l i) (r := r i) (e := (.inl a,.inr (.inl b)))).mpr h₁
    have h₂' := (mem_tripartiteArcs (E := E j) (l := l j) (r := r j) (e := (.inl a,.inr (.inl b)))).mpr h₂
    exact disjoint_left.mp (hDisj hi hj hij) h₁' h₂'
  · intro i hi j hj hij a w h₁ h₂
    have h₁' := (mem_tripartiteArcs (E := E i) (l := l i) (r := r i) (e := (.inr (.inr w),.inl a))).mpr h₁
    have h₂' := (mem_tripartiteArcs (E := E j) (l := l j) (r := r j) (e := (.inr (.inr w),.inl a))).mpr h₂
    exact disjoint_left.mp (hDisj hi hj hij) h₁' h₂'
  · intro i hi j hj hij b w h₁ h₂
    have h₁' := (mem_tripartiteArcs (E := E i) (l := l i) (r := r i) (e := (.inr (.inl b),.inr (.inr w)))).mpr h₁
    have h₂' := (mem_tripartiteArcs (E := E j) (l := l j) (r := r j) (e := (.inr (.inl b),.inr (.inr w)))).mpr h₂
    exact disjoint_left.mp (hDisj hi hj hij) h₁' h₂'

private theorem LabeledTripartiteCycle.arcSet {C : TripartiteArcSet A B W}
    (D : LabeledTripartiteCycle C) :
    tripartiteArcs (fun a b => ∃ i, D.x i = a ∧ D.y i = b)
      (fun a w => ∃ i, D.x (D.next i) = a ∧ D.w i = w)
      (fun b w => ∃ i, D.y i = b ∧ D.w i = w) = C := by
  ext e
  rcases e with ⟨u,v⟩
  rw [D.arcs]
  rcases u with a | (b | w) <;> rcases v with a' | (b' | w') <;>
    simp [tripartiteArc,eq_comm,and_comm]

/-- Select the augmented decomposition in precisely the copies assigned to
the current remainder, and combine it with the other copies unchanged. -/
theorem tripartite_absorber_union_absorbs_cycles {J : Type*} (S T : Finset J) (hTS : T ⊆ S)
    (E : J → A → B → Prop) (l : J → A → W → Prop) (r : J → B → W → Prop)
    (F : J → A → B → Prop) (l' : J → A → W → Prop) (r' : J → B → W → Prop)
    {L : A → B → Prop} {lL : A → W → Prop} {rL : B → W → Prop}
    (hUnion : T.biUnion (fun j => tripartiteArcs (F j) (l' j) (r' j)) = tripartiteArcs L lL rL)
    (hAbs : (↑S : Set J).PairwiseDisjoint (fun j => tripartiteArcs (E j) (l j) (r j)))
    (hCycles : (↑T : Set J).PairwiseDisjoint (fun j => tripartiteArcs (F j) (l' j) (r' j)))
    (hMixed : ∀ i ∈ S, ∀ j ∈ T, Disjoint (tripartiteArcs (E i) (l i) (r i))
      (tripartiteArcs (F j) (l' j) (r' j)))
    (hBefore : ∀ j ∈ S, Nonempty (TripartiteTriangleDecomposition (E j) (l j) (r j)))
    (hAfter : ∀ j ∈ T, Nonempty (TripartiteTriangleDecomposition
      (fun a b => E j a b ∨ F j a b) (fun a w => l j a w ∨ l' j a w)
      (fun b w => r j b w ∨ r' j b w))) :
    Nonempty (TripartiteTriangleDecomposition
      (fun a b => (∃ j ∈ S, E j a b) ∨ L a b)
      (fun a w => (∃ j ∈ S, l j a w) ∨ lL a w)
      (fun b w => (∃ j ∈ S, r j b w) ∨ rL b w)) := by
  let D (j : J) := tripartiteArcs (E j) (l j) (r j)
  let C (j : J) := tripartiteArcs (F j) (l' j) (r' j)
  let EB (j : J) (a : A) (b : B) := E j a b ∨ (j ∈ T ∧ F j a b)
  let EL (j : J) (a : A) (w : W) := l j a w ∨ (j ∈ T ∧ l' j a w)
  let ER (j : J) (b : B) (w : W) := r j b w ∨ (j ∈ T ∧ r' j b w)
  have hForms (j : J) (e : TripartiteVertex A B W × TripartiteVertex A B W) :
      e ∈ tripartiteArcs (EB j) (EL j) (ER j) ↔ e ∈ D j ∨ (j ∈ T ∧ e ∈ C j) := by
    rcases e with ⟨u,v⟩
    rcases u with a | (b | w) <;> rcases v with a' | (b' | w') <;>
      simp [EB,EL,ER,D,C,tripartiteArc]
  apply tripartite_decomposition_of_arc_partition S EB EL ER
  · rw [tripartiteArcs_or,tripartiteArcs_indexed,← hUnion]
    ext e
    simp only [mem_biUnion,hForms,mem_union]
    constructor
    · rintro ⟨j,hj,h | ⟨hjT,h⟩⟩
      · exact Or.inl ⟨j,hj,h⟩
      · exact Or.inr ⟨j,hjT,h⟩
    · rintro (⟨j,hj,h⟩ | ⟨j,hj,h⟩)
      · exact ⟨j,hj,Or.inl h⟩
      · exact ⟨j,hTS hj,Or.inr ⟨hj,h⟩⟩
  · intro i hi j hj hij
    apply disjoint_left.mpr
    intro e he he'
    rcases (hForms i e).mp he with h₁ | ⟨hiT,h₁⟩ <;>
      rcases (hForms j e).mp he' with h₂ | ⟨hjT,h₂⟩
    · exact disjoint_left.mp (hAbs hi hj hij) h₁ h₂
    · exact disjoint_left.mp (hMixed i hi j hjT) h₁ h₂
    · exact disjoint_left.mp (hMixed j hj i hiT) h₂ h₁
    · exact disjoint_left.mp (hCycles hiT hjT hij) h₁ h₂
  · intro j hj
    by_cases ht : j ∈ T
    · simpa only [EB,EL,ER,ht,true_and] using hAfter j ht
    · simpa only [EB,EL,ER,ht,false_and,or_false] using hBefore j hj

/-- Chen–Shan, Lemma 4.6, with the lower bound on the common side size
made explicit. The oriented arc set counts one arc per undirected edge.
The auxiliary set can be used together with U as the vertex set. -/
theorem exists_universal_tripartite_absorber
    (AB : A → B → Prop) (AW : A → W → Prop) (BW : B → W → Prop)
    (U Z : Finset (TripartiteVertex A B W)) (h : ℕ) (m η γ ε : ℝ)
    (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hSizeA : (Fintype.card A : ℝ) = m)
    (hSizeW : γ*m ≤ (Fintype.card W : ℝ))
    (hDegreeA : ∀ a, (1/2+η)*m ≤ ((univ.filter (AB a) : Finset B).card : ℝ))
    (hDegreeB : ∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => AB a b) : Finset A).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun z => ¬ AW a z) : Finset W).card : ℝ) ≤ ε*m)
    (hBW : ∀ b, ((univ.filter (fun z => ¬ BW b z) : Finset W).card : ℝ) ≤ ε*m)
    (hWA : ∀ z, ((univ.filter (fun a => ¬ AW a z) : Finset A).card : ℝ) ≤ ε*m)
    (hWB : ∀ z, ((univ.filter (fun b => ¬ BW b z) : Finset B).card : ℝ) ≤ ε*m)
    (hε : 0 ≤ ε) (hEps : ε ≤ η/32) (hEpsCycles : (h : ℝ)*ε ≤ γ/16)
    (hUZ : U ⊆ Z) (hU : U.card ≤ h) (hZ : (Z.card : ℝ) ≤ min η γ*m/16)
    (hRoom : ((4*(h*h)*2^(h*h) : ℕ) : ℝ) ≤ min η γ*m/16) :
    ∃ (Q : Finset (TripartiteVertex A B W))
      (E : A → B → Prop) (l : A → W → Prop) (r : B → W → Prop),
      Disjoint Q Z ∧
      tripartiteArcs E l r ⊆ tripartiteArcs AB AW BW ∧
      (∀ e ∈ tripartiteArcs E l r, FootprintEdge Q U e.1 e.2) ∧
      (tripartiteArcs E l r).card + Q.card ≤ 4*(h*h)*2^(h*h) ∧
      Nonempty (TripartiteTriangleDecomposition E l r) ∧
      ∀ (L : A → B → Prop) (lL : A → W → Prop) (rL : B → W → Prop),
        tripartiteArcs L lL rL ⊆ tripartiteArcs AB AW BW →
        tripartiteArcs L lL rL ⊆ U ×ˢ U → TripartiteLocallyBalanced L lL rL →
        Nonempty (TripartiteTriangleDecomposition
          (fun a b => E a b ∨ L a b) (fun a w => l a w ∨ lL a w)
          (fun b w => r b w ∨ rL b w)) := by
  classical
  let G := tripartiteArcs AB AW BW
  let R := balancedRemainders G U
  have hR (L : R) := mem_balancedRemainders.mp L.property
  have hPartition (L : R) := exists_labeled_tripartite_cycle_partition L.val (hR L).1 (hR L).2.2
  choose C hPart hLabels hCovers hSum using hPartition
  let J := Σ L : R, Fin (C L).length
  let D (j : J) : LabeledTripartiteCycle ((C j.1).get j.2) := (hLabels j.1 j.2).some
  let len (j : J) := (D j).length
  have hCSub (j : J) : (C j.1).get j.2 ⊆ U ×ˢ U :=
    fun e he => (hR j.1).2.1 ((hCovers j.1 e).mpr ⟨j.2,he⟩)
  have hLocalRoom (j : J) : 2*(len j : ℝ)*ε ≤ γ/16 := by
    have hn : 2*len j ≤ h := by
      have hcard := ((D j).card_le_vertices (hCSub j)).trans hU
      change 3*len j ≤ h at hcard
      omega
    have hreal : 2*(len j : ℝ) ≤ (h : ℝ) := by exact_mod_cast hn
    exact (mul_le_mul_of_nonneg_right hreal hε).trans hEpsCycles
  let Bnd := 4*(h*h)*2^(h*h)
  have hBudget : (∑ j : J, (9*len j + (2*len j+1))) ≤ Bnd := by
    have hCount (L : R) : (∑ i : Fin (C L).length, 3*len ⟨L,i⟩) = L.val.card := by
      calc
        _ = ∑ i : Fin (C L).length, ((C L).get i).card := by
          apply sum_congr rfl
          intro i _
          exact (D ⟨L,i⟩).card_eq.symm
        _ = _ := hSum L
    have hAll := balancedRemainders_bounds G U hU
    calc
      _ ≤ ∑ j : J, 4*(3*len j) := by
        apply sum_le_sum
        intro j _
        have hj : 0 < len j := (D j).positive
        omega
      _ = 4*(∑ L : R, L.val.card) := by
        rw [← mul_sum, Fintype.sum_sigma]
        simp_rw [hCount]
      _ ≤ 4*(R.card*(h*h)) := by
        apply Nat.mul_le_mul_left
        calc
          _ ≤ ∑ _ : R, h*h := sum_le_sum (fun L _ => hAll.2 L.val L.property)
          _ = _ := by simp
      _ ≤ Bnd := by
        calc
          _ ≤ 4*(2^(h*h)*(h*h)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hAll.1)
          _ = Bnd := by unfold Bnd; ac_rfl
  have hAux : (↑(∑ j : J, (2*len j+1)) : ℝ) ≤ min η γ*m/16 := by
    apply le_trans _ hRoom
    have hn : (∑ j : J, (2*len j+1)) ≤ Bnd :=
      (sum_le_sum (fun _ _ => Nat.le_add_left _ _)).trans hBudget
    exact_mod_cast hn
  obtain ⟨P,hPDisj,hP⟩ := exists_disjoint_cycle_absorber_footprints
    (univ : Finset J) len AB AW BW (fun j => (D j).next)
    (fun j => (D j).x) (fun j => (D j).y) (fun j => (D j).w) Z m η γ ε
    hm hη hγ hSizeA hSizeW hDegreeA hDegreeB hAW hBW hWA hWB hEps
    (fun j _ => hLocalRoom j) hZ hAux
  have hCopy (j : J) := exists_embedded_cycle_absorber_of_footprint
    (D j).next (D j).x (D j).y (D j).w
    (fun i => ((D j).vertices_mem (hCSub j) i).1)
    (fun i => ((D j).vertices_mem (hCSub j) i).2.1)
    (fun i => ((D j).vertices_mem (hCSub j) i).2.2)
    ((hP j (mem_univ _)).2.1.mono_right hUZ) (hP j (mem_univ _)).1
  choose E l r hE hl hr hEdges hBefore hAfter using hCopy
  let S : Finset J := univ
  let Q := S.biUnion P
  let H (j : J) := tripartiteArcs (E j) (l j) (r j)
  let Eall (a : A) (b : B) := ∃ j ∈ S, E j a b
  let Lall (a : A) (w : W) := ∃ j ∈ S, l j a w
  let Rall (b : B) (w : W) := ∃ j ∈ S, r j b w
  have hH : tripartiteArcs Eall Lall Rall = S.biUnion H := tripartiteArcs_indexed S E l r
  have hPQ (j : J) : P j ⊆ Q := fun _ he => mem_biUnion.mpr ⟨j,mem_univ _,he⟩
  have hQ : Disjoint Q Z := by
    apply disjoint_left.mpr
    intro v hv hV
    obtain ⟨j,hj,hv'⟩ := mem_biUnion.mp hv
    exact disjoint_left.mp (hP j hj).2.1 hv' hV
  have hSupport (j : J) (e) (he : e ∈ H j) : e ∈ G ∧ FootprintEdge (P j) U e.1 e.2 := by
    have hj := mem_tripartiteArcs.mp he
    rcases e with ⟨u,v⟩
    rcases u with a | (b | w) <;> rcases v with a' | (b' | w') <;>
      simp only [tripartiteArc] at hj
    · exact ⟨mem_tripartiteArcs.mpr (hE j _ _ hj).1,(hE j _ _ hj).2⟩
    · exact ⟨mem_tripartiteArcs.mpr (hr j _ _ hj).1,(hr j _ _ hj).2⟩
    · exact ⟨mem_tripartiteArcs.mpr (hl j _ _ hj).1,(hl j _ _ hj).2.reverse⟩
  have hDisj : (↑S : Set J).PairwiseDisjoint H := by
    intro i hi j hj hij
    exact disjoint_left.mpr (fun e he he' =>
      FootprintEdge.disjoint (hPDisj hi hj hij) ((hP i hi).2.1.mono_right hUZ)
        (hSupport i e he).2 (hSupport j e he').2)
  refine ⟨Q,Eall,Lall,Rall,hQ,?_,?_,?_,?_,?_⟩
  · rw [hH]
    intro e he
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
    exact (hSupport j e hj).1
  · rw [hH]
    intro e he
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp he
    rcases (hSupport j e hj).2 with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact Or.inl ⟨hPQ j h₁,h₂.imp (fun hv => hPQ j hv) id⟩
    · exact Or.inr ⟨hPQ j h₁,h₂.imp (fun hv => hPQ j hv) id⟩
  · rw [hH]
    have h1 : (S.biUnion H).card ≤ ∑ j : J, 9*len j :=
      card_biUnion_le.trans (sum_le_sum (fun j _ => by
        simpa only [Fintype.card_fin] using hEdges j))
    have h2 : Q.card ≤ ∑ j : J, (2*len j+1) :=
      card_biUnion_le.trans (sum_le_sum (fun j hj => (hP j hj).2.2))
    exact (Nat.add_le_add h1 h2).trans (by rw [← sum_add_distrib]; exact hBudget)
  · exact tripartite_decomposition_of_arc_partition S E l r hH.symm hDisj (fun j _ => hBefore j)
  · intro L lL rL hLG hLU hBal
    let O : R := ⟨tripartiteArcs L lL rL,mem_balancedRemainders.mpr
      ⟨hLG,hLU,arcBalanced_of_tripartiteLocallyBalanced hBal⟩⟩
    let T := S.filter (fun j => j.1 = O)
    have hT (j : J) : j ∈ T ↔ j.1 = O := by simp [T,S]
    let F (j : J) (a : A) (b : B) := ∃ i, (D j).x i = a ∧ (D j).y i = b
    let lF (j : J) (a : A) (w : W) := ∃ i, (D j).x ((D j).next i) = a ∧ (D j).w i = w
    let rF (j : J) (b : B) (w : W) := ∃ i, (D j).y i = b ∧ (D j).w i = w
    have hF (j : J) : tripartiteArcs (F j) (lF j) (rF j) = (C j.1).get j.2 := (D j).arcSet
    apply tripartite_absorber_union_absorbs_cycles S T (filter_subset _ _) E l r F lF rF
    · change T.biUnion _ = O.val
      ext e
      simp only [mem_biUnion,hT,hF,hCovers O e]
      constructor
      · rintro ⟨⟨L',i⟩,hL',he⟩
        change L' = O at hL'
        subst L'
        exact ⟨i,he⟩
      · rintro ⟨i,he⟩
        exact ⟨⟨O,i⟩,rfl,he⟩
    · exact hDisj
    · rintro ⟨L',i⟩ hi ⟨L'',j⟩ hj hne
      have hi' : L' = O := (hT _).mp hi
      have hj' : L'' = O := (hT _).mp hj
      subst L'
      subst L''
      change Disjoint (tripartiteArcs (F ⟨O,i⟩) (lF ⟨O,i⟩) (rF ⟨O,i⟩))
        (tripartiteArcs (F ⟨O,j⟩) (lF ⟨O,j⟩) (rF ⟨O,j⟩))
      rw [hF,hF]
      exact hPart O i j (fun h => hne (h ▸ rfl))
    · intro i hi j hj
      apply disjoint_left.mpr
      intro e he he'
      have hp := (hP i hi).2.1.mono_right hUZ
      have hUe := mem_product.mp (hCSub j (hF j ▸ he'))
      rcases (hSupport i e he).2 with ⟨hx,_⟩ | ⟨hx,_⟩
      · exact disjoint_left.mp hp hx hUe.1
      · exact disjoint_left.mp hp hx hUe.2
    · exact fun j _ => hBefore j
    · exact fun j _ => hAfter j

end OverfullWork.ChenShan
