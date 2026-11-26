module

public import OverfullWork.ChenShanShortRepairPaths

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

variable {V : Type*} [Fintype V]

noncomputable def arcOutNeighbors (G : Finset (V × V)) (v : V) : Finset V :=
  univ.filter (fun w => (v,w) ∈ G)

noncomputable def arcInNeighbors (G : Finset (V × V)) (v : V) : Finset V :=
  univ.filter (fun w => (w,v) ∈ G)

@[simp] theorem mem_arcOutNeighbors {G : Finset (V × V)} {v w : V} :
    w ∈ arcOutNeighbors G v ↔ (v,w) ∈ G := by simp [arcOutNeighbors]

@[simp] theorem mem_arcInNeighbors {G : Finset (V × V)} {v w : V} :
    w ∈ arcInNeighbors G v ↔ (w,v) ∈ G := by simp [arcInNeighbors]

private theorem card_neighbors_sdiff_add_incidentDegree
    (G D : Finset (V × V)) (v : V) (f : V ↪ V × V)
    (hf : ∀ w, (f w).1 = v ∨ (f w).2 = v) :
    (univ.filter (fun w => f w ∈ G)).card ≤
      (univ.filter (fun w => f w ∈ G \ D)).card + incidentDegree D v := by
  let S := univ.filter (fun w => f w ∈ G)
  let T := univ.filter (fun w => f w ∈ G \ D)
  have hSub : S ⊆ T ∪ univ.filter (fun w => f w ∈ D) := by
    intro w hw
    simp only [S,mem_filter,mem_univ,true_and] at hw
    by_cases hd : f w ∈ D <;> simp [T,hw,hd]
  have hD : (univ.filter (fun w => f w ∈ D)).card ≤ incidentDegree D v := by
    rw [← card_map f]
    apply card_le_card
    rintro e he
    obtain ⟨w,hw,rfl⟩ := mem_map.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2,hf w⟩
  exact (card_le_card hSub).trans ((card_union_le _ _).trans (Nat.add_le_add_left hD _))

theorem card_arcOutNeighbors_sdiff (G D : Finset (V × V)) (v : V) :
    (arcOutNeighbors G v).card ≤ (arcOutNeighbors (G \ D) v).card + incidentDegree D v :=
  card_neighbors_sdiff_add_incidentDegree G D v
    ⟨fun w => (v,w),fun _ _ h => congrArg Prod.snd h⟩ (fun _ => Or.inl rfl)

theorem card_arcInNeighbors_sdiff (G D : Finset (V × V)) (v : V) :
    (arcInNeighbors G v).card ≤ (arcInNeighbors (G \ D) v).card + incidentDegree D v :=
  card_neighbors_sdiff_add_incidentDegree G D v
    ⟨fun w => (w,v),fun _ _ h => congrArg Prod.fst h⟩ (fun _ => Or.inr rfl)

omit [Fintype V] in
private theorem exists_common_neighbor_outside
    (U P Q F : Finset V) (hP : P ⊆ U) (hQ : Q ⊆ U)
    (hSize : U.card + F.card < P.card + Q.card) :
    ∃ x, x ∉ F ∧ x ∈ P ∧ x ∈ Q := by
  have hUnion := card_le_card (union_subset hP hQ)
  have hInter := card_union_add_card_inter P Q
  have hSmall : F.card < (P ∩ Q).card := by omega
  obtain ⟨x,hx,hf⟩ := exists_mem_notMem_of_card_lt_card hSmall
  exact ⟨x,hf,(mem_inter.mp hx).1,(mem_inter.mp hx).2⟩

noncomputable def repairClass (part : V → ZMod 3) (i : ZMod 3) : Finset V :=
  univ.filter (fun v => part v = i)

/-- If each original neighborhood exceeds half its target class by enough
to pay for deleted edges and forbidden vertices, short repair paths survive. -/
theorem exists_short_repair_path_of_budgets (part : V → ZMod 3)
    (G D : Finset (V × V)) (F : Finset V) (K B : ℕ)
    (hArc : ∀ a b, (a,b) ∈ G → part b = part a + 1)
    (hDeleted : ∀ a, incidentDegree D a ≤ K) (hForbidden : F.card + 2 ≤ B)
    (hOut : ∀ a, (repairClass part (part a + 1)).card + B + 2*K <
      2*(arcOutNeighbors G a).card)
    (hIn : ∀ b, (repairClass part (part b - 1)).card + B + 2*K <
      2*(arcInNeighbors G b).card)
    (u v : V) (hne : u ≠ v) :
    ∃ l : ℕ, l ≤ 4 ∧ ∃ f : Fin (l+1) ↪ V,
      f 0 = u ∧ f (Fin.last l) = v ∧ directedPathArcs l f ⊆ G \ D ∧
      ∀ i : Fin (l+1), i ≠ 0 → i ≠ Fin.last l → f i ∉ F := by
  let H := G \ D
  let S := insert u (insert v F)
  have hScard : S.card ≤ B := by
    dsimp only [S]
    have h := card_insert_le u (insert v F)
    have h' := card_insert_le v F
    omega
  have hStep a b (h : (a,b) ∈ H) := hArc a b (mem_sdiff.mp h).1
  have hP (a : V) : arcOutNeighbors H a ⊆ repairClass part (part a + 1) := by
    intro b hb
    exact mem_filter.mpr ⟨mem_univ b,hStep a b (mem_arcOutNeighbors.mp hb)⟩
  have hQ (b : V) : arcInNeighbors H b ⊆ repairClass part (part b - 1) := by
    intro a ha
    apply mem_filter.mpr
    refine ⟨mem_univ a,?_⟩
    have h := hStep a b (mem_arcInNeighbors.mp ha)
    linear_combination -h
  have hPSize (a : V) :
      (repairClass part (part a + 1)).card + S.card < 2*(arcOutNeighbors H a).card := by
    dsimp only [H]
    have h := card_arcOutNeighbors_sdiff G D a
    have hn := hDeleted a
    have h' := hOut a
    omega
  have hQSize (b : V) :
      (repairClass part (part b - 1)).card + S.card < 2*(arcInNeighbors H b).card := by
    dsimp only [H]
    have h := card_arcInNeighbors_sdiff G D b
    have hn := hDeleted b
    have h' := hIn b
    omega
  apply exists_short_repair_path part H F u v hne hStep
  · intro a
    have h := hPSize a
    have ht := card_le_card (hP a)
    have hLt : S.card < (arcOutNeighbors H a).card := by omega
    obtain ⟨x,hx,hx'⟩ := exists_mem_notMem_of_card_lt_card hLt
    exact ⟨x,hx',mem_arcOutNeighbors.mp hx⟩
  · intro b
    have h := hQSize b
    have ht := card_le_card (hQ b)
    have hLt : S.card < (arcInNeighbors H b).card := by omega
    obtain ⟨x,hx,hx'⟩ := exists_mem_notMem_of_card_lt_card hLt
    exact ⟨x,hx',mem_arcInNeighbors.mp hx⟩
  · intro a b hab
    have he : part b - 1 = part a + 1 := by linear_combination hab
    have hQ' := hQ b
    have hsQ := hQSize b
    rw [he] at hQ' hsQ
    have hSize := hPSize a
    obtain ⟨x,hx,hxa,hxb⟩ := exists_common_neighbor_outside _ _ _ S (hP a) hQ' (by omega)
    exact ⟨x,hx,mem_arcOutNeighbors.mp hxa,mem_arcInNeighbors.mp hxb⟩

end OverfullWork.ChenShan
