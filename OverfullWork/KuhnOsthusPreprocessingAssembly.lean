module

public import OverfullWork.KuhnOsthusExceptionalFactorAssembly
public import OverfullWork.KuhnOsthusExceptionalContraction
public import OverfullWork.KuhnOsthusExtenderIteration
public import Mathlib.Combinatorics.Hall.Finite

@[expose] public section


/-! The 1-factorization and assembly in Kühn–Osthus
Proposition 6.1, Lemma 8.4 and Corollary 8.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open DirectedDemandHall (Arc)
open scoped Classical
variable {V : Type*} [Fintype V]

private theorem exists_permutation_of_regular (D : Digraph V) (r : ℕ)
    (hr : 0 < r) (hReg : ∀ v, inDegree D v = r ∧ outDegree D v = r) :
    ∃ σ : Equiv.Perm V, ∀ v, D.Adj v (σ v) := by
  let N (v : V) := univ.filter (D.Adj v)
  have hHall (S : Finset V) : S.card ≤ (S.biUnion N).card := by
    let T := S.biUnion N
    have hIn (y : V) : inNeighbours D S y ≤ r := by
      rw [←(hReg y).1]
      exact card_le_card (filter_subset_filter _ (subset_univ _))
    have hCount : ∑ y ∈ T, inNeighbours D S y = S.card * r := by
      simp only [inNeighbours,card_filter]
      rw [sum_comm]
      calc
        (∑ x ∈ S, ∑ y ∈ T, if D.Adj x y then (1 : ℕ) else 0) =
            ∑ x ∈ S, outDegree D x := by
              apply sum_congr rfl
              intro x hx
              rw [outDegree,card_filter]
              apply sum_subset (subset_univ _)
              intro y _ hy
              exact if_neg (fun h => hy (mem_biUnion.mpr ⟨x,hx,mem_filter.mpr ⟨mem_univ _,h⟩⟩))
        _ = S.card * r := by simp only [(hReg _).2,sum_const,nsmul_eq_mul,Nat.cast_id]
    have hBound := sum_le_sum (s := T) (fun y _ => hIn y)
    rw [hCount,sum_const,nsmul_eq_mul] at hBound
    exact Nat.le_of_mul_le_mul_right hBound hr
  obtain ⟨f,hf,hN⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hHall
  exact ⟨Equiv.ofBijective f ⟨hf,Finite.surjective_of_injective hf⟩,
    fun v => (mem_filter.mp (hN v)).2⟩

/-- Kühn–Osthus Proposition 6.1. A digraph with equal constant
semidegrees has a decomposition into spanning permutation digraphs. -/
theorem exists_permutation_factorization_of_regular (D : Digraph V) (r : ℕ)
    (hReg : ∀ v, inDegree D v = r ∧ outDegree D v = r) :
    ∃ F : Fin r → Equiv.Perm V, matchingUnion F = D ∧
      ∀ i j, i ≠ j → ∀ v, F i v ≠ F j v := by
  induction r generalizing D with
  | zero =>
    refine ⟨Fin.elim0,?_,fun i => i.elim0⟩
    ext x y
    constructor
    · rintro ⟨i,_⟩
      exact i.elim0
    · intro h
      have hPos : 0 < outDegree D x := card_pos.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,h⟩⟩
      exact (Nat.ne_of_gt hPos (hReg x).2).elim
  | succ r ih =>
    obtain ⟨σ,hσ⟩ := exists_permutation_of_regular D (r+1) (Nat.succ_pos _) hReg
    let M : Digraph V := matchingUnion (fun _ : Fin 1 => σ)
    have hM (x y : V) : M.Adj x y ↔ σ x = y :=
      ⟨fun ⟨_,h⟩ => h,fun h => ⟨0,h⟩⟩
    have hMD : M ≤ D := fun x y h => (hM x y).mp h ▸ hσ x
    have hOne := matchingUnion_exact_semidegrees (fun _ : Fin 1 => σ)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    have hRest (v : V) : inDegree (D \ M) v = r ∧ outDegree (D \ M) v = r := by
      obtain ⟨hi,ho⟩ := residual_semidegrees D M hMD v
      obtain ⟨hMi,hMo⟩ := hOne v
      rw [hMi,(hReg v).1] at hi
      rw [hMo,(hReg v).2] at ho
      omega
    obtain ⟨F,hF,hApart⟩ := ih (D \ M) hRest
    have hEdge (i : Fin r) (v : V) : (D \ M).Adj v (F i v) := by
      rw [←hF]
      exact ⟨i,rfl⟩
    have hApartLast (i : Fin r) (v : V) : F i v ≠ σ v := fun h =>
      (hEdge i v).2 ((hM v (F i v)).mpr h.symm)
    refine ⟨Fin.snoc F σ,?_,?_⟩
    · ext x y
      constructor
      · rintro ⟨i,hi⟩
        revert hi
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]
          rintro rfl
          exact hσ x
        · simp only [Fin.snoc_castSucc]
          rintro rfl
          exact (hEdge j x).1
      · intro h
        by_cases hm : M.Adj x y
        · exact ⟨Fin.last _,by simpa only [Fin.snoc_last] using (hM x y).mp hm⟩
        · obtain ⟨i,hi⟩ : (matchingUnion F).Adj x y := hF ▸ (show (D \ M).Adj x y from ⟨h,hm⟩)
          exact ⟨i.castSucc,by simpa only [Fin.snoc_castSucc] using hi⟩
    · intro i j
      refine Fin.lastCases ?_ (fun a => ?_) j
      · refine Fin.lastCases (fun h => (h rfl).elim) (fun a _ v => ?_) i
        simpa only [Fin.snoc_castSucc,Fin.snoc_last] using hApartLast a v
      · refine Fin.lastCases (fun _ v => ?_) (fun b h v => ?_) i
        · simpa only [Fin.snoc_castSucc,Fin.snoc_last] using (hApartLast a v).symm
        · simpa only [Fin.snoc_castSucc] using hApart b a (fun hba => h (congrArg Fin.castSucc hba)) v

/-- Applying Lemma 8.1 to each permutation partitions the entire
approximate residue and exceptional factors into exactly `r*(50*l+1)`
small path systems. -/
theorem kuhn_osthus_preprocessing_path_partition
    {r l : ℕ} {label : V → Fin 50} {Z : Finset V}
    (H : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l)
    (hReg : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hLoop : ∀ v, ¬ H.Adj v v)
    (hIndependent : ∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y)
    (hDisH : ∀ j, Disjoint H (C j).digraph)
    (hDisC : ∀ i j, i ≠ j → Disjoint (C i).digraph (C j).digraph)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1)) :
    ∃ Q : Fin (r*(50*l+1)) → Digraph V,
      (⨆ i, Q i) = H ⊔ (⨆ j, (C j).digraph) ∧
      (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
      ∀ i, IsDirectedPathSystem (Q i) ∧ CoversExceptional (Q i) Z ∧
        (Fintype.card (Arc (Q i)) : ℝ) ≤ 1230 * Fintype.card V / (50*l+1) ∧
        ∃ S : Finset (Fin 50), S.card ≤ 5 ∧ SupportedByStyles label Z S (Q i) := by
  obtain ⟨F,hF,hApart⟩ := exists_permutation_factorization_of_regular H r hReg
  have hEdge (i : Fin r) (v : V) : H.Adj v (F i v) := by
    rw [←hF]
    exact ⟨i,rfl⟩
  have hLocal (i : Fin r) := kuhn_osthus_lemma_8_1_with_support
    (C i) (F i) (fun v he => hLoop v (by simpa only [he] using hEdge i v))
    (fun v hv hw => hIndependent v (F i v) hv hw (hEdge i v))
    (fun j x y hc he => (disjoint_iff_inf_le.mp (hDisH i)) (show (H ⊓ (C i).digraph).Adj x y from
      ⟨he ▸ hEdge i x,Digraph.iSup_adj.mpr ⟨j,hc⟩⟩)) hL hN hZ
  choose Q hOwner hProperties _ hLocalSupport using hLocal
  let e : (Fin r × Option (Fin 50 × Fin l)) ≃ Fin (r*(50*l+1)) :=
    Fintype.equivFinOfCardEq (by rw [Fintype.card_prod,Fintype.card_fin,card_kuhn_osthus_path_slots])
  have hSupport (j : Fin r) (q : Option (Fin 50 × Fin l)) {x y : V}
      (h : (Q j q).Adj x y) : F j x = y ∨ (C j).digraph.Adj x y := by
    exact (hLocalSupport j q x y h).imp_right Digraph.iSup_adj.mpr
  refine ⟨fun i => Q (e.symm i).1 (e.symm i).2,?_,?_,fun i => hProperties _ _⟩
  · ext x y
    rw [Digraph.iSup_adj,Digraph.sup_adj,Digraph.iSup_adj]
    constructor
    · rintro ⟨i,hi⟩
      rcases hSupport _ _ hi with he | hc
      · exact Or.inl (he ▸ hEdge (e.symm i).1 x)
      · exact Or.inr ⟨(e.symm i).1,hc⟩
    · intro h
      obtain ⟨j,hj⟩ : ∃ j, F j x = y ∨ ∃ q, ((C j).path q).Adj x y := by
        rcases h with hh | ⟨j,hj⟩
        · rw [←hF] at hh
          obtain ⟨j,hj⟩ := hh
          exact ⟨j,Or.inl hj⟩
        · exact ⟨j,Or.inr (Digraph.iSup_adj.mp hj)⟩
      obtain ⟨q,hq,_⟩ := (hOwner j x y).mp hj
      exact ⟨e (j,q),by simpa only [Equiv.symm_apply_apply] using hq⟩
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro x y ⟨hi,hj⟩
    have hs := hSupport _ _ hi
    have ht := hSupport _ _ hj
    by_cases he : (e.symm i).1 = (e.symm j).1
    · have ht' : (Q (e.symm i).1 (e.symm j).2).Adj x y := he.symm ▸ hj
      obtain ⟨q,_,hq⟩ :=
        (hOwner (e.symm i).1 x y).mp (hs.imp_right Digraph.iSup_adj.mp)
      have hSecond := (hq _ hi).trans (hq _ ht').symm
      exact hij (e.symm.injective (Prod.ext he hSecond))
    · rcases hs with hFi | hCi <;> rcases ht with hFj | hCj
      · exact hApart _ _ he x (hFi.trans hFj.symm)
      · exact (disjoint_iff_inf_le.mp (hDisH _)) (show (H ⊓ _).Adj x y from
          ⟨hFi ▸ hEdge (e.symm i).1 x,hCj⟩)
      · exact (disjoint_iff_inf_le.mp (hDisH _)) (show (H ⊓ _).Adj x y from
          ⟨hFj ▸ hEdge (e.symm j).1 x,hCi⟩)
      · exact (disjoint_iff_inf_le.mp (hDisC _ _ he)) (show (_ ⊓ _ : Digraph V).Adj x y from
          ⟨hCi,hCj⟩)

/-- Kühn–Osthus Lemma 8.4 from an extender that tolerates the full
semidegree budget. Every arc of the residue and the original
exceptional factors is used. -/
theorem kuhn_osthus_preprocessing_cycles_of_extender
    {r l : ℕ} {label : V → Fin 50} {Z : Finset V}
    (H R : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l)
    (hReg : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hLoop : ∀ v, ¬ H.Adj v v)
    (hIndependent : ∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y)
    (hDisH : ∀ j, Disjoint H (C j).digraph)
    (hDisC : ∀ i j, i ≠ j → Disjoint (C i).digraph (C j).digraph)
    (hDisR : Disjoint (H ⊔ (⨆ j, (C j).digraph)) R)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1))
    (hExtend : ∀ Q L : Digraph V, Q ≤ H ⊔ (⨆ j, (C j).digraph) →
      IsDirectedPathSystem Q → CoversExceptional Q Z →
      (Fintype.card (Arc Q) : ℝ) ≤ 1230 * Fintype.card V / (50*l+1) →
      (∃ S : Finset (Fin 50), S.card ≤ 5 ∧ SupportedByStyles label Z S Q) →
      L ≤ R →
      (∀ v, inDegree L v ≤ r*(50*l+1) ∧ outDegree L v ≤ r*(50*l+1)) →
      ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, Q.Adj x y → ρ x = y) ∧
        ∀ x, (Q ⊔ (R \ L)).Adj x (ρ x)) :
    ∃ F : Fin (r*(50*l+1)) → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      H ⊔ (⨆ j, (C j).digraph) ≤ matchingUnion F ∧
      matchingUnion F ≤ (H ⊔ (⨆ j, (C j).digraph)) ⊔ R := by
  obtain ⟨Q,hAll,hDis,hQ⟩ :=
    kuhn_osthus_preprocessing_path_partition H C hReg hLoop hIndependent hDisH hDisC hL hN hZ
  have hQSub (i : Fin (r*(50*l+1))) : Q i ≤ H ⊔ (⨆ j, (C j).digraph) := by
    rw [←hAll]
    exact le_iSup Q i
  obtain ⟨F,hCycles,_,hEdge,hPack,hCover⟩ := exists_iterated_path_extensions R Q hDis
    (fun i => hDisR.mono_left (hQSub i)) (fun i L hLR hBound =>
      hExtend (Q i) L (hQSub i) (hQ i).1 (hQ i).2.1 (hQ i).2.2.1 (hQ i).2.2.2 hLR
        (fun v => ⟨(hBound v).1.trans i.isLt.le,(hBound v).2.trans i.isLt.le⟩))
  refine ⟨F,hCycles,hPack,hAll ▸ hCover,?_⟩
  rintro x y ⟨i,rfl⟩
  exact sup_le_sup_right (hQSub i) R (hEdge i x)

/-- Kühn–Osthus Corollary 8.5 for a prepared preprocessing graph.
The degree calculation leaves exactly the input required by the
absorber on the complement of the exceptional set. -/
theorem kuhn_osthus_preprocessing_assembly
    {r l t : ℕ} {label : V → Fin 50} {Z : Finset V}
    (P H R : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l)
    (hRegH : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hRegP : ∀ v, let a := if v ∈ Z then r*(50*l+1) else r*(50*l+1)+t
      inDegree P v+r = a ∧ outDegree P v+r = a)
    (hLoop : ∀ v, ¬ H.Adj v v)
    (hIndependent : ∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y)
    (hDisPH : Disjoint P H)
    (hCSub : ∀ j, (C j).digraph ≤ P)
    (hRSub : R ≤ P)
    (hDisRC : ∀ j, Disjoint (C j).digraph R)
    (hDisC : ∀ i j, i ≠ j → Disjoint (C i).digraph (C j).digraph)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1))
    (hExtend : ∀ Q L : Digraph V, Q ≤ H ⊔ (⨆ j, (C j).digraph) →
      IsDirectedPathSystem Q → CoversExceptional Q Z →
      (Fintype.card (Arc Q) : ℝ) ≤ 1230 * Fintype.card V / (50*l+1) →
      (∃ S : Finset (Fin 50), S.card ≤ 5 ∧ SupportedByStyles label Z S Q) →
      L ≤ R →
      (∀ v, inDegree L v ≤ r*(50*l+1) ∧ outDegree L v ≤ r*(50*l+1)) →
      ∃ ρ : Equiv.Perm V, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, Q.Adj x y → ρ x = y) ∧
        ∀ x, (Q ⊔ (R \ L)).Adj x (ρ x)) :
    ∃ F : Fin (r*(50*l+1)) → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      H ⊔ (⨆ j, (C j).digraph) ≤ matchingUnion F ∧
      matchingUnion F ≤ P ⊔ H ∧
      let D := (P ⊔ H) \ matchingUnion F
      (∀ x y, D.Adj x y → x ∉ Z ∧ y ∉ Z) ∧
      ∀ v : ↥Zᶜ, inDegree (InducedDigraphSampling.induced D Zᶜ) v = t ∧
        outDegree (InducedDigraphSampling.induced D Zᶜ) v = t := by
  have hDisR : Disjoint (H ⊔ (⨆ j, (C j).digraph)) R := by
    apply disjoint_sup_left.mpr
    refine ⟨hDisPH.symm.mono_right hRSub,?_⟩
    apply disjoint_iff_inf_le.mpr
    intro x y ⟨h,hR⟩
    obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp h
    exact (disjoint_iff_inf_le.mp (hDisRC j)) ⟨hj,hR⟩
  obtain ⟨F,hCycles,hPack,hCover,hSub⟩ := kuhn_osthus_preprocessing_cycles_of_extender H R C
    hRegH hLoop hIndependent (fun j => hDisPH.symm.mono_right (hCSub j))
    hDisC hDisR hL hN hZ hExtend
  have hInPH : matchingUnion F ≤ P ⊔ H := hSub.trans
    (sup_le (sup_le le_sup_right ((iSup_le hCSub).trans le_sup_left)) (hRSub.trans le_sup_left))
  obtain ⟨hEq,hDegrees,hFree⟩ := preprocessing_residue_degrees P H Z r (r*(50*l+1)) t F
    hDisPH hRegH hRegP (fun i v => hInPH ⟨i,rfl⟩) hPack (le_sup_left.trans hCover)
  refine ⟨F,hCycles,hPack,hCover,hInPH,?_⟩
  dsimp only
  rw [←hEq]
  exact ⟨hFree,preprocessing_complement_factor _ Z t hFree (fun v hv => by
    simpa only [hv,if_false] using hDegrees v)⟩

/-- Lemma 8.4 with its local extension on the ordinary vertices.
Contract the covered exceptional vertices separately in each path
system and restore them in its Hamilton cycle. -/
theorem kuhn_osthus_preprocessing_cycles_of_basic_extender
    {r l : ℕ} {label : V → Fin 50} {Z : Finset V}
    (H R : Digraph V) (C : Fin r → OriginalExceptionalFactor label Z l)
    (hReg : ∀ v, inDegree H v = r ∧ outDegree H v = r)
    (hLoop : ∀ v, ¬ H.Adj v v)
    (hIndependent : ∀ x y, x ∈ Z → y ∈ Z → ¬ H.Adj x y)
    (hDisH : ∀ j, Disjoint H (C j).digraph)
    (hDisC : ∀ i j, i ≠ j → Disjoint (C i).digraph (C j).digraph)
    (hDisR : Disjoint (H ⊔ (⨆ j, (C j).digraph)) R)
    (hL : 2452 ≤ (50*l)/1226)
    (hN : 50*l+1 ≤ Fintype.card V)
    (hZ : 2 * (Z.card : ℝ) ≤ (Fintype.card V : ℝ) / (50*l+1))
    (hExtend : ∀ (B : Digraph ↥Zᶜ) (L : Digraph V),
      B ≤ basicExceptionalPathSystem (H ⊔ (⨆ j, (C j).digraph)) Z →
      IsDirectedPathSystem B →
      (Fintype.card (Arc B) : ℝ) ≤ 1230 * Fintype.card V / (50*l+1) →
      (∃ S : Finset (Fin 50), S.card ≤ 5 ∧
        SupportedByStyles (fun v : ↥Zᶜ => label v.val) ∅ S B) →
      L ≤ R →
      (∀ v, inDegree L v ≤ r*(50*l+1) ∧ outDegree L v ≤ r*(50*l+1)) →
      ∃ σ : Equiv.Perm ↥Zᶜ, HasSpanningCycle (fun x y => σ x = y) ∧
        (∀ x y, B.Adj x y → σ x = y) ∧
        ∀ x, (B ⊔ InducedDigraphSampling.induced (R \ L) Zᶜ).Adj x (σ x)) :
    ∃ F : Fin (r*(50*l+1)) → Equiv.Perm V,
      (∀ i, HasSpanningCycle (fun x y => F i x = y)) ∧
      (∀ i j, i ≠ j → ∀ v, F i v ≠ F j v) ∧
      H ⊔ (⨆ j, (C j).digraph) ≤ matchingUnion F ∧
      matchingUnion F ≤ (H ⊔ (⨆ j, (C j).digraph)) ⊔ R := by
  apply kuhn_osthus_preprocessing_cycles_of_extender H R C hReg hLoop hIndependent
    hDisH hDisC hDisR hL hN hZ
  intro Q L hSub hQ hCover hSize hStyles hLR hBudget
  let B := basicExceptionalPathSystem Q Z
  have hBasicSupport : B ≤ basicExceptionalPathSystem (H ⊔ (⨆ j, (C j).digraph)) Z := by
    rintro x y (hq | ⟨z,hz,hxz,hzy⟩)
    · exact Or.inl (hSub hq)
    · exact Or.inr ⟨z,hz,hSub hxz,hSub hzy⟩
  have hNo (x y : V) (h : Q.Adj x y) (hx : x ∈ Z) : y ∉ Z := by
    rcases (Digraph.sup_adj _ _ _ _).mp (hSub h) with hH | hE
    · exact fun hy => hIndependent x y hx hy hH
    · obtain ⟨j,hj⟩ := Digraph.iSup_adj.mp hE
      obtain ⟨i,hi⟩ := Digraph.iSup_adj.mp hj
      exact (C j).no_internal i hi hx
  obtain ⟨S,hS,hSupport⟩ := hStyles
  obtain ⟨hStyle,hCard⟩ := basicExceptionalPathSystem.bounds hQ hSupport
  have hCard' : (Fintype.card (Arc B) : ℝ) ≤ Fintype.card (Arc Q) := by exact_mod_cast hCard
  obtain ⟨σ,hHamilton,hKeep,hEdges⟩ := hExtend B L hBasicSupport
    (basicExceptionalPathSystem.isDirectedPathSystem hQ) (hCard'.trans hSize) ⟨S,hS,hStyle⟩ hLR hBudget
  exact expand_basic_exceptional_cycle Q (R \ L) Z hQ hCover hNo σ hHamilton hKeep hEdges

end OverfullWork.DirectedRobustExpansion
