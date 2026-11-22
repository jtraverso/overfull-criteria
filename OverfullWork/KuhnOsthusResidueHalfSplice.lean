module

public import OverfullWork.KuhnOsthusCycleAbsorberConstruction

@[expose] public section


/-! Split a winding 1-factor of the chord residue into its two half
path covers and perform the opposite-half splices of Lemma 10.2. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function
open scoped Classical
variable {V : Type*} [Fintype V]

/-- Complementary covers use disjoint incoming and outgoing slots, even though
both covers contain the two boundary clusters. -/
theorem IntervalPathCover.complementary_slots {G H : Digraph V} {A B S T : Finset V}
    (P : IntervalPathCover G A S T) (Q : IntervalPathCover H B T S)
    (hMeet : A ∩ B = S ∪ T) :
    (∀ {x a y z}, P.digraph.Adj x y → Q.digraph.Adj a z → x ≠ a) ∧
    (∀ {x a y z}, P.digraph.Adj x y → Q.digraph.Adj a z → y ≠ z) := by
  constructor
  · rintro x _ y z hp hq rfl
    obtain ⟨hA,hT⟩ := mem_sdiff.mp ((P.slots x).1.mp ⟨_,hp⟩)
    obtain ⟨hB,hS⟩ := mem_sdiff.mp ((Q.slots x).1.mp ⟨_,hq⟩)
    exact (mem_union.mp (hMeet ▸ mem_inter.mpr ⟨hA,hB⟩)).elim hS hT
  · rintro x a y _ hp hq rfl
    obtain ⟨hA,hS⟩ := mem_sdiff.mp ((P.slots y).2.mp ⟨_,hp⟩)
    obtain ⟨hB,hT⟩ := mem_sdiff.mp ((Q.slots y).2.mp ⟨_,hq⟩)
    exact (mem_union.mp (hMeet ▸ mem_inter.mpr ⟨hA,hB⟩)).elim hS hT

omit [Fintype V] in
/-- The winding permutation determines all paths across a consecutive
interval. At each cluster the iterates fill the entire cell. -/
theorem exists_ordered_paths_of_winding_permutation
    (σ : Equiv.Perm V) (A : ℕ → Finset V) {l r : ℕ}
    (_hlr : l ≤ r) (hSize : ∀ i, l ≤ i → i ≤ r → (A i).card = (A l).card)
    (hStep : ∀ i, l ≤ i → i < r → ∀ x ∈ A i, σ x ∈ A (i+1)) :
    ∃ P : OrderedClusterPaths ⟨fun x y => σ x = y⟩ A (A l) l r,
      ∀ i j, P.vertex i j = (σ : V → V)^[i-l] j.val := by
  let f (i : ℕ) (j : A l) := (σ : V → V)^[i-l] j.val
  have hAt (j : A l) (n : ℕ) (hn : l+n ≤ r) : (σ : V → V)^[n] j.val ∈ A (l+n) := by
    induction n with
    | zero => simp [j.prop]
    | succ n ih =>
      rw [iterate_succ_apply']
      exact hStep (l+n) (by omega) (by omega) _ (ih (by omega))
  have hPart (i : ℕ) (hi : l ≤ i) (hir : i ≤ r) (j : A l) : f i j ∈ A i := by
    have h := hAt j (i-l) (by omega)
    rwa [Nat.add_sub_of_le hi] at h
  have hInj (i : ℕ) : Injective (f i) := fun _ _ he =>
    Subtype.ext (σ.injective.iterate _ he)
  refine ⟨⟨f,hPart,fun i _ _ => hInj i,?_,?_⟩,fun _ _ => rfl⟩
  · intro i hi hir x hx
    let g (j : A l) : A i := ⟨f i j,hPart i hi hir j⟩
    have hg : Injective g := fun _ _ he => hInj i (congrArg (fun z : A i => z.val) he)
    have hCard : Fintype.card (A l) = Fintype.card (A i) := by
      simp only [Fintype.card_coe]
      exact (hSize i hi hir).symm
    have hSurj := ((Fintype.bijective_iff_injective_and_card g).mpr ⟨hg,hCard⟩).2
    obtain ⟨j,hj⟩ := hSurj ⟨x,hx⟩
    exact ⟨j,congrArg (fun z : A i => z.val) hj⟩
  · intro i hi _ j
    change σ (f i j) = f (i+1) j
    have hIdx : i+1-l = (i-l)+1 := by omega
    simp only [f,hIdx,iterate_succ_apply']

/-- The two main splicings are permutation factors. Each uses exactly
one half of the winding residue and the opposite half of the primary
cycle absorber. -/
theorem IntervalPathCover.exists_opposite_half_splices {G : Digraph V} {A B S T : Finset V}
    (F₀ : IntervalPathCover G A S T) (F₁ : IntervalPathCover G B T S)
    (H₀ : IntervalPathCover G A S T) (H₁ : IntervalPathCover G B T S)
    (hAll : A ∪ B = univ) (hMeet : A ∩ B = S ∪ T) (hDis : Disjoint S T) :
    ∃ σ₀ σ₁ : Equiv.Perm V,
      (∀ x y, (F₀.digraph ⊔ H₁.digraph).Adj x y ↔ σ₀ x = y) ∧
      (∀ x y, (H₀.digraph ⊔ F₁.digraph).Adj x y ↔ σ₁ x = y) := by
  obtain ⟨σ₀,h₀⟩ := F₀.exists_winding_factor H₁ hAll hMeet hDis
  obtain ⟨σ₁,h₁⟩ := H₀.exists_winding_factor F₁ hAll hMeet hDis
  exact ⟨σ₀,σ₁,h₀,h₁⟩

/-- Split a winding residue permutation into complementary exact
interval arc sets, retaining its ordinary vertex order. -/
theorem exists_winding_residue_halves (σ : Equiv.Perm V) {k t : ℕ}
    (X : Fin k → Finset V) (hk : 0 < k) (ht : 0 < t) (htk : t < k)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hApart : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = (X ⟨0,hk⟩).card)
    (hNext : ∀ i x, x ∈ X i → σ x ∈ X (finRotate k i)) :
    let A := cyclicCluster X hk
    let B := fun i => A (t+i)
    let G : Digraph V := ⟨fun x y => σ x = y⟩
    ∃ (P : IntervalPathCover G (clusterIntervalVertices A 0 t) (A 0) (A t))
      (Q : IntervalPathCover G (clusterIntervalVertices B 0 (k-t)) (A t) (A 0)),
      P.digraph ⊔ Q.digraph = G := by
  intro A B G
  obtain ⟨hB₀,hBn,hAll,hMeet,hDisA,hDisB⟩ :=
    cyclicCluster_complementary_intervals X ht htk hCover hApart
  rw [Nat.add_zero] at hBn hAll hMeet hDisB
  have hStep (i : ℕ) (x : V) (hx : x ∈ A i) : σ x ∈ A (i+1) := by
    change σ x ∈ cyclicCluster X hk (i+1)
    rw [cyclicCluster_successor]
    exact hNext _ x hx
  obtain ⟨P₀,_⟩ := exists_ordered_paths_of_winding_permutation σ A (Nat.zero_le t)
    (fun i _ _ => hSize _) (fun i _ _ => hStep i)
  obtain ⟨Q₀,_⟩ := exists_ordered_paths_of_winding_permutation σ B (Nat.zero_le (k-t))
    (fun i _ _ => (hSize _).trans (hSize _).symm)
    (fun i _ _ x hx => by simpa only [B,Nat.add_assoc] using hStep (t+i) x hx)
  obtain ⟨P,_,_⟩ := P₀.exists_interval_path_cover (Nat.zero_le t) hDisA
  obtain ⟨Q,_,_⟩ := Q₀.exists_interval_path_cover (Nat.zero_le (k-t))
    (fun i j _ hi _ hj h => hDisB i j hi hj h)
  let Q' := Q.castBoundaries hB₀ hBn
  have hDis : Disjoint (A 0) (A t) := hDisA 0 t le_rfl (Nat.zero_le _) (Nat.zero_le _) le_rfl (by omega)
  have hMeet' : clusterIntervalVertices A 0 t ∩ clusterIntervalVertices B 0 (k-t) = A 0 ∪ A t := by
    have h₀ : B 0 = A t := hB₀
    have h₁ : B (k-t) = A 0 := hBn
    change clusterIntervalVertices A 0 t ∩ clusterIntervalVertices B 0 (k-t) = B (k-t) ∪ B 0 at hMeet
    rwa [h₀,h₁] at hMeet
  obtain ⟨ρ,hρ⟩ := P.exists_winding_factor Q' hAll hMeet' hDis
  have hσ (x : V) : ρ x = σ x := ((sup_le P.digraph_le Q'.digraph_le) ((hρ x (ρ x)).mpr rfl)).symm
  exact ⟨P,Q',by ext x y; exact (hρ x y).trans (by rw [hσ])⟩

/-- The two splices with a representative of each cycle at its
initial cluster, as required by the two sweeps of Lemma 10.2. -/
theorem NormalizedCycleAbsorber.exists_residue_half_splices_with_roots
    {G H : Digraph V} {q m : ℕ} (X : Fin (14*q) → Finset V) (hq : 0 < q)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m) (σ : Equiv.Perm V)
    (hNext : ∀ i x, x ∈ X i → σ x ∈ X (finRotate (14*q) i)) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q} {eTop : Fin (2*m) ≃ A 0}
      {eLow : Fin (2*m) ≃ B 0} (N : NormalizedCycleAbsorber (G := G) E eTop eLow),
      let D : Digraph V := ⟨fun x y => σ x = y⟩
      ∃ (P Q : Digraph V) (τ₀ τ₁ : Equiv.Perm V),
        let F₀ := (N.top.paths.unionPaths ⊔ E.third.digraph) ⊔ N.topTail.unionPaths
        let F₁ := (N.low.paths.unionPaths ⊔ E.fifth.digraph) ⊔ N.lowTail.unionPaths
        P ⊔ Q = D ∧
        (∀ x y, (F₀ ⊔ Q).Adj x y ↔ τ₀ x = y) ∧
        (∀ x y, (P ⊔ F₁).Adj x y ↔ τ₁ x = y) ∧
        Disjoint P Q ∧
        (∀ {x a y z}, F₀.Adj x y → F₁.Adj a z → x ≠ a) ∧
        (∀ {x a y z}, F₀.Adj x y → F₁.Adj a z → y ≠ z) ∧
        (∀ {x y z}, F₀.Adj x y → Q.Adj x z → False) ∧
        (∀ {x y z}, P.Adj x y → F₁.Adj x z → False) ∧
        (∀ v, ∃ a, τ₀.SameCycle (N.top.paths.vertex 0 a) v) ∧
        (∀ v, ∃ a, τ₁.SameCycle (N.low.paths.vertex 0 a) v) := by
  intro hk A B E eTop eLow N D
  let L (i : ℕ) := A (7*q+i)
  have hB (i : ℕ) : B i = L i := cyclicCluster_rotateClusterArray X hk _ _
  have hBL : B = L := funext hB
  have hT : 0 < 7*q := by omega
  have hTk : 7*q < 14*q := by omega
  have hLen : 14*q+0-7*q = 7*q := by omega
  obtain ⟨hL₀,hLn,hAll,hMeet,hDisA,hDisL⟩ :=
    cyclicCluster_complementary_intervals X hT hTk hCover hDis
  rw [hLen] at hLn hAll hMeet hDisL
  have hL₀' : L 0 = A (7*q) := hL₀
  have hLn' : L (7*q) = A 0 := hLn
  have hMeet' : clusterIntervalVertices A 0 (7*q) ∩ clusterIntervalVertices L 0 (7*q) =
      A 0 ∪ A (7*q) := by
    change clusterIntervalVertices A 0 (7*q) ∩ clusterIntervalVertices L 0 (7*q) =
      L (7*q) ∪ L 0 at hMeet
    rwa [hL₀',hLn'] at hMeet
  obtain ⟨P,Q,hR⟩ := exists_winding_residue_halves σ X hk hT hTk hCover hDis
    (fun i => (hSize i).trans (hSize _).symm) hNext
  have he : 14*q-7*q = 7*q := by omega
  let Q' := Q.castSupport (congrArg (fun n => clusterIntervalVertices L 0 n) he)
  have hQ' : Q'.digraph = Q.digraph := IntervalPathCover.castSupport_digraph _ _
  obtain ⟨F₀,hF₀⟩ := N.top.exists_half_path_cover_of_tail (by omega) (by omega) E.third N.topTail
    (fun i j hi hj h => hDisA i j (Nat.zero_le _) hi (Nat.zero_le _) hj h)
  obtain ⟨_,E₅,_,hE₅⟩ := E.exists_rotated X hk
  obtain ⟨F₁,hF₁⟩ := N.low.exists_half_path_cover_of_tail (by omega) (by omega) E₅ N.lowTail
    (fun i j hi hj h => by rw [hB,hB]; exact hDisL i j hi hj h)
  have hLow : F₁.digraph = (N.low.paths.unionPaths ⊔ E.fifth.digraph) ⊔ N.lowTail.unionPaths :=
    hF₁.trans (by rw [hE₅])
  let F₁₀ := F₁.castSupport (congrArg (fun Y => clusterIntervalVertices Y 0 (7*q)) hBL)
  let F₁' := F₁₀.castBoundaries ((hB 0).trans hL₀') ((hB (7*q)).trans hLn')
  have hLF : F₁'.digraph = F₁.digraph :=
    (IntervalPathCover.castBoundaries_digraph _ _ _).trans (IntervalPathCover.castSupport_digraph _ _)
  let K := (G ⊔ H) ⊔ D
  have hApart := hDisA 0 (7*q) le_rfl (by omega) (by omega) le_rfl (by omega)
  obtain ⟨τ₀,hτ₀,⟨S₀⟩⟩ := (F₀.rehost (le_sup_left : G ⊔ H ≤ K)).exists_winding_factor_with_return
    (Q'.rehost (le_sup_right : D ≤ K)) hAll hMeet' hApart
  obtain ⟨τ₁,hτ₁,⟨S₁⟩⟩ := (F₁'.rehost (le_sup_left : G ⊔ H ≤ K)).exists_winding_factor_with_return
    (P.rehost (le_sup_right : D ≤ K)) (by rwa [union_comm])
    (by rwa [inter_comm,union_comm]) hApart.symm
  simp only [IntervalPathCover.rehost_digraph] at hτ₀ hτ₁
  rw [hF₀,hQ'] at hτ₀
  rw [hLF,hLow] at hτ₁
  obtain ⟨hOutH,_⟩ := P.complementary_slots Q' hMeet'
  obtain ⟨hOutF,hInF⟩ := F₀.complementary_slots F₁' hMeet'
  obtain ⟨hOut₀,_⟩ := F₀.complementary_slots Q' hMeet'
  obtain ⟨hOut₁,_⟩ := P.complementary_slots F₁' hMeet'
  rw [hQ'] at hOutH
  rw [hF₀,hLF,hLow] at hOutF hInF
  rw [hF₀,hQ'] at hOut₀
  rw [hLF,hLow] at hOut₁
  refine ⟨P.digraph,Q.digraph,τ₀,τ₁,hR,hτ₀,?_,?_,hOutF,hInF,
    fun hp hq => hOut₀ hp hq rfl,fun hp hq => hOut₁ hp hq rfl,?_,?_⟩
  · intro x y
    rw [sup_comm]
    exact hτ₁ x y
  · rw [disjoint_iff_inf_le]
    rintro x y ⟨hp,hq⟩
    exact hOutH hp hq rfl
  · intro v
    obtain ⟨a,ha⟩ := S₀.cycle_meets_mark v
    refine ⟨eTop.symm a,?_⟩
    rw [N.top_start,Equiv.apply_symm_apply]
    exact ha
  · intro v
    obtain ⟨a,ha⟩ := S₁.cycle_meets_mark v
    let b : B 0 := ⟨a.val,((hB 0).trans hL₀').symm ▸ a.prop⟩
    refine ⟨eLow.symm b,?_⟩
    rw [N.low_start,Equiv.apply_symm_apply]
    exact ha

/-- Form the two opposite-half splicings of the actual constructed
primary factor and a winding residue permutation. The four half
digraphs have their exact physical arc sets. -/
theorem NormalizedCycleAbsorber.exists_residue_half_splices
    {G H : Digraph V} {q m : ℕ} (X : Fin (14*q) → Finset V) (hq : 0 < q)
    (hCover : ∀ x, ∃ i, x ∈ X i) (hDis : ∀ i j, i ≠ j → Disjoint (X i) (X j))
    (hSize : ∀ i, (X i).card = 2*m) (σ : Equiv.Perm V)
    (hNext : ∀ i x, x ∈ X i → σ x ∈ X (finRotate (14*q) i)) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let B := cyclicCluster (rotateClusterArray X hk (7*q)) hk
    ∀ {E : CycleAbsorberExceptionalCovers H A q} {eTop : Fin (2*m) ≃ A 0}
      {eLow : Fin (2*m) ≃ B 0} (N : NormalizedCycleAbsorber (G := G) E eTop eLow),
      let D : Digraph V := ⟨fun x y => σ x = y⟩
      ∃ (P Q : Digraph V) (τ₀ τ₁ : Equiv.Perm V),
        let F₀ := (N.top.paths.unionPaths ⊔ E.third.digraph) ⊔ N.topTail.unionPaths
        let F₁ := (N.low.paths.unionPaths ⊔ E.fifth.digraph) ⊔ N.lowTail.unionPaths
        P ⊔ Q = D ∧
        (∀ x y, (F₀ ⊔ Q).Adj x y ↔ τ₀ x = y) ∧
        (∀ x y, (P ⊔ F₁).Adj x y ↔ τ₁ x = y) := by
  intro hk A B E eTop eLow N D
  obtain ⟨P,Q,τ₀,τ₁,hR,h₀,h₁,_,_,_,_,_,_,_⟩ :=
    NormalizedCycleAbsorber.exists_residue_half_splices_with_roots X hq hCover hDis hSize σ hNext N
  exact ⟨P,Q,τ₀,τ₁,hR,h₀,h₁⟩

end OverfullWork.DirectedRobustExpansion
