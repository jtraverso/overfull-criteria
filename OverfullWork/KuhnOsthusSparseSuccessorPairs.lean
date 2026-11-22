module

public import OverfullWork.KuhnOsthusSparseReserveMerge
public import OverfullWork.DirectedRobustCycleFactor

@[expose] public section


/-! Complete and merge all successor pairs in the sparse case of
Kühn–Osthus Lemma 6.4. An arbitrary initial target labeling suffices. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
universe u
variable {V : Type u} [Fintype V]

/-- Sparse-superregular estimates used by Lemma 4.11. -/
structure SparseSuccessorPairBounds (D : Digraph V) (d ε μ ζ : ℝ) : Prop where
  in_degree : ∀ v, ζ*d*(Fintype.card V:ℝ) ≤ (inDegree D v:ℝ)
  out_degree : ∀ v, ζ*d*(Fintype.card V:ℝ) ≤ (outDegree D v:ℝ)
  in_codegree : ∀ x y, x ≠ y → (commonInNeighbours D x y:ℝ) ≤ (d/μ)^2*Fintype.card V
  out_codegree : ∀ x y, x ≠ y →
    (commonInNeighbours (reverseArcs D) x y:ℝ) ≤ (d/μ)^2*Fintype.card V
  rectangle : ∀ A B : Finset V, ε*(Fintype.card V:ℝ) ≤ (A.card:ℝ) →
    ε*(Fintype.card V:ℝ) ≤ (B.card:ℝ) →
    (1-ε)*d*(A.card:ℝ)*(B.card:ℝ) ≤ (incidences D A B:ℝ)

omit [Fintype V] in
/-- Identify the targets of a physical pair with the source labels. -/
def pairOnSources (R : Digraph V) (S T : Finset V) (e : S ≃ T) : Digraph S :=
  ⟨fun x y => R.Adj x (e y)⟩

private theorem card_filter_target_perm (e : Equiv.Perm V) (p : V → Prop) :
    (univ.filter (fun y => p (e y))).card = (univ.filter p).card := by
  classical
  have h := filter_map (f := e.toEmbedding) (s := (univ : Finset V)) (p := p)
  rw [univ_map_equiv_to_embedding] at h
  exact (card_map (f := e.toEmbedding)).symm.trans (congrArg Finset.card h).symm

/-- The estimates are independent of the chosen target labels. -/
theorem SparseSuccessorPairBounds.reindex_targets
    {D : Digraph V} {d ε μ ζ : ℝ} (h : SparseSuccessorPairBounds D d ε μ ζ)
    (e : Equiv.Perm V) :
    SparseSuccessorPairBounds ⟨fun x y => D.Adj x (e y)⟩ d ε μ ζ := by
  let B : Digraph V := ⟨fun x y => D.Adj x (e y)⟩
  have hOut (v : V) : outDegree B v = outDegree D v :=
    card_filter_target_perm e (D.Adj v)
  have hCommon (x y : V) :
      commonInNeighbours (reverseArcs B) x y = commonInNeighbours (reverseArcs D) x y := by
    unfold commonInNeighbours
    convert card_filter_target_perm e (fun u => D.Adj x u ∧ D.Adj y u) using 2 <;>
      ext u <;> simp only [mem_filter,mem_univ,true_and] <;> rfl
  have hRect (X Y : Finset V) : incidences B X Y = incidences D X (Y.image e) := by
    rw [←Nat.cast_inj (R := ℝ),incidences_eq_sum,incidences_eq_sum]
    rw [sum_image e.injective.injOn]
  refine ⟨fun v => h.in_degree (e v),fun v => hOut v ▸ h.out_degree v,
    fun x y hxy => h.in_codegree _ _ (e.injective.ne hxy),?_,?_⟩
  · intro x y hxy
    change (commonInNeighbours (reverseArcs B) x y:ℝ) ≤ _
    rw [hCommon]
    exact h.out_codegree x y hxy
  · intro X Y hX hY
    change _ ≤ (incidences B X Y:ℝ)
    rw [hRect]
    have hSize : (Y.image e).card = Y.card := card_image_of_injective _ e.injective
    have hk := h.rectangle X (Y.image e) hX (by rwa [hSize])
    rwa [hSize] at hk

/-- Complete a balanced basic system and merge all cycles using the
sparse successor reserves. The same sparse bounds serve both Hall
and the local replacement, regardless of the initial identification. -/
theorem exists_hamilton_completion_of_sparse_successor_pairs
    (d ε μ ζ ν τ γ : ℝ) (hd : 0 < d) (hε : 0 < ε) (hε1 : ε < 1)
    (hμ : 0 < μ) (hζ : 0 < ζ) (hν : 0 < ν) (hτ : 2*ν ≤ τ)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hGamma : γ ≤ ζ*d)
    (hScale : 160*ε ≤ (ζ*μ)^2) (hDiscard : 8*ν ≤ τ*(ζ*d)^2)
    (hνDensity : ν < (1-ε)*d*ε) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {n : ℕ} (D R : Digraph W)
      (cluster : W → Fin (n+1)),
      let s := finRotate (n+1)
      let S := freeOut D cluster
      let T i := freeIn D cluster (s i)
      IsDirectedPathSystem D →
      (∀ i, ∃ x, x ∈ freeIn D cluster i ∧ x ∈ S i) →
      (∀ i, N ≤ (S i).card) →
      (∀ i, (16:ℝ)*(S i).card ≤ (ζ*d*(S i).card)^2) →
      (∀ i, ∃ e : S i ≃ T i, SparseSuccessorPairBounds (pairOnSources R (S i) (T i) e) d ε μ ζ) →
      ∃ ρ : Equiv.Perm W, HasSpanningCycle (fun x y => ρ x = y) ∧
        (∀ x y, D.Adj x y → ρ x = y) ∧ (∀ x, (D ⊔ R).Adj x (ρ x)) := by
  have hντ : ν ≤ τ := by linarith
  obtain ⟨N₀,hLocal⟩ := exists_cut_merge_of_sparse_superregular_pair.{u} d ε μ ζ ν τ γ
    hd hε hε1 hμ hζ hν hτ hτγ hγ hGamma hScale hDiscard hνDensity
  obtain ⟨N₁,hHam⟩ := DirectedAbsorbingLadder.exists_hamilton_threshold.{u} ν τ γ
    hν hντ hτγ hγ
  refine ⟨max 1 (max N₀ N₁),?_⟩
  intro W _ n D R cluster s S T hD hOverlap hSize hDiagonal hPair
  choose e he using hPair
  have hN₀ (i : Fin (n+1)) : N₀ ≤ (S i).card :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hSize i)
  have hN₁ (i : Fin (n+1)) : N₁ ≤ (S i).card :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (hSize i)
  have hPositive (i : Fin (n+1)) : 0 < Fintype.card (S i) := by
    rw [Fintype.card_coe]
    exact Nat.succ_le_iff.mp ((le_max_left 1 _).trans (hSize i))
  have hMatch (i : Fin (n+1)) : ∃ f : S i ≃ T i, ∀ x : S i, R.Adj x (f x) := by
    let B := pairOnSources R (S i) (T i) (e i)
    have hB := he i
    have hRob : IsRealRobust B ν τ := kuhn_osthus_sparse_pair_expansion B d ε μ ζ ν τ
      (hPositive i) hd hε hε1 hμ hζ hν hτ hScale
      (by simpa only [Fintype.card_coe] using hDiagonal i) hDiscard hνDensity
      hB.in_degree hB.out_degree hB.in_codegree hB.out_codegree hB.rectangle
    have hDeg := mul_le_mul_of_nonneg_right hGamma (Nat.cast_nonneg (Fintype.card (S i)) : (0:ℝ) ≤ _)
    have hCycle := hHam B (by simpa only [Fintype.card_coe] using hN₁ i) hRob
      (fun v => hDeg.trans (hB.in_degree v)) (fun v => hDeg.trans (hB.out_degree v))
    obtain ⟨a,ha,_⟩ := exists_spanning_successor hCycle
    exact ⟨a.trans (e i),ha⟩
  obtain ⟨σ,hKeep,hNew,_⟩ := exists_factor_completion_of_successor_matchings D R cluster s hD hMatch
  apply hamilton_completion_of_successor_cut_merges D R cluster σ hD.acyclic hKeep hNew hOverlap
  intro i ρ
  let f := freeSuccessorEquiv D R cluster s σ hKeep hNew i
  let B := successorReserve R σ (S i)
  let g := f.trans (e i).symm
  have hB : SparseSuccessorPairBounds B d ε μ ζ := by
    have hh := (he i).reindex_targets g
    have heq : (⟨fun x y => (pairOnSources R (S i) (T i) (e i)).Adj x (g y)⟩ : Digraph (S i)) = B := by
      ext x y
      change R.Adj x ((e i) ((e i).symm (f y))) ↔ R.Adj x (σ y)
      rw [(e i).apply_symm_apply]
      rfl
    exact heq ▸ hh
  apply hLocal ρ (S i) B (hN₀ i) (hDiagonal i)
  · simpa only [Fintype.card_coe] using hB.in_degree
  · simpa only [Fintype.card_coe] using hB.out_degree
  · simpa only [Fintype.card_coe] using hB.in_codegree
  · simpa only [Fintype.card_coe] using hB.out_codegree
  · simpa only [Fintype.card_coe] using hB.rectangle


/-- Certify the identified pair directly on its two physical sides.
The codegrees count common neighbours in the opposite physical side. -/
theorem sparse_pair_bounds_of_physical (R : Digraph V) (S T : Finset V) (e : S ≃ T)
    (d ε μ ζ : ℝ)
    (hIn : ∀ y ∈ T, ζ*d*(S.card:ℝ) ≤ (inNeighbours R S y:ℝ))
    (hOut : ∀ x ∈ S, ζ*d*(S.card:ℝ) ≤ (outTo R T x:ℝ))
    (hCI : ∀ x ∈ T, ∀ y ∈ T, x ≠ y →
      (((S.filter fun u => R.Adj u x ∧ R.Adj u y).card):ℝ) ≤ (d/μ)^2*S.card)
    (hCO : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (((T.filter fun u => R.Adj x u ∧ R.Adj y u).card):ℝ) ≤ (d/μ)^2*S.card)
    (hRect : ∀ X ⊆ S, ∀ Y ⊆ T, ε*(S.card:ℝ) ≤ (X.card:ℝ) → ε*(S.card:ℝ) ≤ (Y.card:ℝ) →
      (1-ε)*d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences R X Y:ℝ)) :
    SparseSuccessorPairBounds (pairOnSources R S T e) d ε μ ζ := by
  classical
  let B := pairOnSources R S T e
  let f : S → V := fun x => x.val
  let g : S → V := fun x => (e x).val
  have hf : Function.Injective f := Subtype.coe_injective
  have hg : Function.Injective g := Subtype.coe_injective.comp e.injective
  have hT (p : V → Prop) :
      ((univ : Finset S).filter (fun v => p (e v))).card = (T.filter p).card := by
    have h := filter_map (s := (univ : Finset S)) (f := e.toEmbedding) (p := fun v : T => p v)
    rw [univ_map_equiv_to_embedding] at h
    exact ((card_map (f := e.toEmbedding)).symm.trans (congrArg Finset.card h).symm).trans
      (DenseHall.subtype_filter_card T p)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro y
    have h := hIn (e y) (e y).prop
    change _ ≤ (((S.filter (fun x => R.Adj x (e y))).card):ℝ) at h
    rw [←DenseHall.subtype_filter_card S (fun x => R.Adj x (e y))] at h
    simp only [Fintype.card_coe,inDegree,inNeighbours]
    convert h using 3 <;> ext x <;> simp only [mem_filter,mem_univ,true_and] <;> rfl
  · intro x
    have h := hOut x x.prop
    unfold outTo at h
    rw [←hT (R.Adj x)] at h
    simp only [Fintype.card_coe,outDegree]
    convert h using 3 <;> ext y <;> simp only [mem_filter,mem_univ,true_and] <;> rfl
  · intro x y hxy
    have hne : (e x).val ≠ (e y).val := hg.ne hxy
    have h := hCI (e x) (e x).prop (e y) (e y).prop hne
    have he : commonInNeighbours B x y = (S.filter (fun u => R.Adj u (e x) ∧ R.Adj u (e y))).card := by
      unfold commonInNeighbours
      convert DenseHall.subtype_filter_card S (fun u => R.Adj u (e x) ∧ R.Adj u (e y)) using 2 <;>
        ext u <;> simp only [mem_filter,mem_univ,true_and] <;> rfl
    have he' : ((S.filter (fun u => R.Adj u (e x) ∧ R.Adj u (e y))).card:ℝ) ≤ (d/μ)^2*S.card := by
      convert h using 3 <;> ext u <;> simp only [mem_filter] <;> rfl
    rw [Fintype.card_coe]
    change (commonInNeighbours B x y:ℝ) ≤ _
    rw [he]
    exact he'
  · intro x y hxy
    have h := hCO x x.prop y y.prop (hf.ne hxy)
    have he : commonInNeighbours (reverseArcs B) x y =
        (T.filter (fun u => R.Adj x u ∧ R.Adj y u)).card := by
      unfold commonInNeighbours
      convert hT (fun u => R.Adj x u ∧ R.Adj y u) using 2 <;>
        ext u <;> simp only [mem_filter,mem_univ,true_and] <;> rfl
    have he' : ((T.filter (fun u => R.Adj x u ∧ R.Adj y u)).card:ℝ) ≤ (d/μ)^2*S.card := by
      convert h using 3 <;> ext u <;> simp only [mem_filter] <;> rfl
    rw [Fintype.card_coe]
    change (commonInNeighbours (reverseArcs B) x y:ℝ) ≤ _
    rw [he]
    exact he'
  · intro X Y hx hy
    have hX : X.image f ⊆ S := by
      intro x hx
      obtain ⟨v,_,rfl⟩ := mem_image.mp hx
      exact v.prop
    have hY : Y.image g ⊆ T := by
      intro y hy
      obtain ⟨v,_,rfl⟩ := mem_image.mp hy
      exact (e v).prop
    have hCX := card_image_of_injective X hf
    have hCY := card_image_of_injective Y hg
    simp only [Fintype.card_coe] at hx hy
    have h := hRect _ hX _ hY (by rwa [hCX]) (by rwa [hCY])
    have heq : (incidences B X Y:ℝ) = (incidences R (X.image f) (Y.image g):ℝ) := by
      rw [incidences_eq_sum,incidences_eq_sum,sum_image hg.injOn]
      apply sum_congr rfl
      intro y _
      rw [sum_image hf.injOn]
      rfl
    rw [hCX,hCY,←heq] at h
    simpa only [Fintype.card_coe] using h

end OverfullWork.DirectedRobustExpansion
