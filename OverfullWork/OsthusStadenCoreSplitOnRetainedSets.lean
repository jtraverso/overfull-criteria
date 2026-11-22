module

public import OverfullWork.OsthusStadenCoreExceptionTrimmedPieces

@[expose] public section


/-! Split simultaneously for the actual target sets in §5.6. Each
base half may retain a different subset in each of its requests. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset DirectedRegularPairs
open scoped Classical
universe u

set_option maxHeartbeats 2200000 in
/-- All the possible memberships in the retained sets form a bounded
number of disjoint parts. Split each such part by Claim 5.3. Thus the
degree lower bound after trimming loses only a (1/k) share of the
omitted target profile. A target vertex is in just one part, so the
ordinary-endpoint cap is inherited directly. -/
theorem exists_exceptional_pair_split_on_retained_sets (η : ℝ) (hη : 0 < η) (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] (G : Digraph V) (Z B : Finset V)
      (targets : Fin k → Finset V), N ≤ Fintype.card V →
      (∀ i, targets i ⊆ B) →
      ∃ pieces : Fin k → Digraph V,
        (∀ i x y, (pieces i).Adj x y → G.Adj x y ∧ x ∈ Z ∧ y ∈ targets i) ∧
        (∀ i j, i ≠ j → Disjoint (pieces i) (pieces j)) ∧
        (∀ i x, x ∈ Z → profileCount (targets i) (outProfile G x)/(k:ℝ)-η*(Fintype.card V:ℝ) ≤
          (outDegree (pieces i) x:ℝ)) ∧
        ∀ i y, y ∈ targets i → (inDegree (pieces i) y:ℝ) ≤
          profileCount Z (inProfile G y)/(k:ℝ)+η*(Fintype.card V:ℝ) := by
  let P := Fin k → Bool
  let l := Fintype.card P
  have hl : 0 < (l:ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (⟨fun _ => false⟩ : Nonempty P))
  have hl₁ : 1 ≤ (l:ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (⟨fun _ => false⟩ : Nonempty P))
  let ε := η/(l:ℝ)
  have hε : 0 < ε := div_pos hη hl
  obtain ⟨N,hSplit⟩ := exists_exceptional_pair_split.{u} ε hε k hk
  refine ⟨N,?_⟩
  intro V _ G Z B targets hN hSub
  let pattern (v : V) : P := fun i => decide (v ∈ targets i)
  let atom (p : P) := B.filter (fun v => pattern v = p)
  let good (i : Fin k) := (univ : Finset P).filter (fun p => p i = true)
  have hAtom (p : P) (v : V) : v ∈ atom p ↔ v ∈ B ∧ pattern v = p := mem_filter
  have hGood (i : Fin k) (p : P) : p ∈ good i ↔ p i = true := by simp [good]
  have hCover (i : Fin k) : (good i).biUnion atom = targets i := by
    ext v
    constructor
    · intro h
      obtain ⟨p,hp,hv⟩ := mem_biUnion.mp h
      have hAt := congrFun ((hAtom p v).mp hv).2 i
      exact of_decide_eq_true (hAt.trans ((hGood i p).mp hp))
    · intro h
      exact mem_biUnion.mpr ⟨pattern v,(hGood i _).mpr (decide_eq_true h),(hAtom _ _).mpr ⟨hSub i h,rfl⟩⟩
  have hAtomDis {p p' : P} (hne : p ≠ p') : Disjoint (atom p) (atom p') :=
    disjoint_left.mpr (fun v hv hv' => hne (((hAtom _ _).mp hv).2.symm.trans ((hAtom _ _).mp hv').2))
  choose bank hArcs hDis hOut hIn using fun p : P => hSplit G Z (atom p) hN
  let pieces (i : Fin k) := indexedArcUnion (good i) (fun p => bank p i)
  have hLe (i : Fin k) (x y : V) (h : (pieces i).Adj x y) : G.Adj x y ∧ x ∈ Z ∧ y ∈ targets i := by
    obtain ⟨p,hp,h⟩ := h
    obtain ⟨he,hz,hy⟩ := hArcs p i x y h
    exact ⟨he,hz,by rw [←hCover i]; exact mem_biUnion.mpr ⟨p,hp,hy⟩⟩
  have hAtomsDis (i j : Fin k) (p p' : P) (hne : p ≠ p') : Disjoint (bank p i) (bank p' j) := by
    rw [disjoint_iff_inf_le]
    rintro x y ⟨h,h'⟩
    exact disjoint_left.mp (hAtomDis hne) (hArcs p i x y h).2.2 (hArcs p' j x y h').2.2
  have hPair (i : Fin k) := indexedArcUnion_semidegrees (good i) (fun p => bank p i)
    (fun p _ p' _ hne => hAtomsDis i i p p' hne)
  refine ⟨pieces,hLe,?_,?_,?_⟩
  · intro i j hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨⟨p,_,h⟩,⟨p',_,h'⟩⟩
    by_cases hp : p = p'
    · subst p'
      exact disjoint_iff_inf_le.mp (hDis p i j hne) ⟨h,h'⟩
    · exact disjoint_iff_inf_le.mp (hAtomsDis i j p p' hp) ⟨h,h'⟩
  · intro i x hx
    have hSum := sum_le_sum (s := good i) (fun p _ => hOut p i x hx)
    have hCount : ((good i).card:ℝ) ≤ (l:ℝ) := by exact_mod_cast card_le_univ (good i)
    have hLoss : ((good i).card:ℝ)*(ε*(Fintype.card V:ℝ)) ≤ η*(Fintype.card V:ℝ) := by
      calc
        _ ≤ (l:ℝ)*(ε*(Fintype.card V:ℝ)) := mul_le_mul_of_nonneg_right hCount (by positivity)
        _ = _ := by dsimp only [ε]; field_simp
    have hProfiles : ∑ p ∈ good i, profileCount (atom p) (outProfile G x) =
        profileCount (targets i) (outProfile G x) := by
      rw [←profile_count_disjoint_union (good i) atom _ (fun _ _ _ _ hne => hAtomDis hne),hCover]
    simp_rw [div_eq_mul_inv] at hSum
    rw [sum_sub_distrib,←sum_mul,hProfiles,sum_const,nsmul_eq_mul,←Nat.cast_sum] at hSum
    rw [div_eq_mul_inv]
    exact (sub_le_sub_left hLoss _).trans (hSum.trans_eq (by rw [(hPair i x).1]))
  · intro i y hy
    have hyGood : pattern y ∈ good i := (hGood i _).mpr (decide_eq_true hy)
    have hyAtom : y ∈ atom (pattern y) := (hAtom _ _).mpr ⟨hSub i hy,rfl⟩
    have hZero {p : P} (hne : p ≠ pattern y) : inDegree (bank p i) y = 0 := by
      unfold inDegree inNeighbours
      apply card_eq_zero.mpr
      apply filter_eq_empty_iff.mpr
      intro x _ h
      exact hne (((hAtom p y).mp (hArcs p i x y h).2.2).2.symm)
    have hDegree : inDegree (pieces i) y = inDegree (bank (pattern y) i) y := by
      rw [(hPair i y).2]
      exact sum_eq_single_of_mem _ hyGood (fun _ _ hne => hZero hne)
    rw [hDegree]
    exact (hIn _ i y hyAtom).trans (add_le_add_right (mul_le_mul_of_nonneg_right
      (div_le_self hη.le hl₁) (Nat.cast_nonneg _)) _)

/-- Assign the distinct requests for each base half to distinct slots,
tracking the actual target subset of each request. -/
theorem exists_core_exception_phase_pieces_on_retained_sets (η : ℝ) (hη : 0 < η)
    (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ {V : Type u} [Fintype V] {J L : Type*}
      (G : Digraph V) (Z : Finset V) (half : J → Finset V) (requests : J → Finset L)
      (retained : L → J → Finset V), N ≤ Fintype.card V →
      (∀ i j, i ≠ j → Disjoint (half i) (half j)) →
      (∀ i, Nonempty (↥(requests i) ↪ Fin k)) →
      ∃ pieces : L → J → Digraph V,
        (∀ l i x y, (pieces l i).Adj x y →
          l ∈ requests i ∧ G.Adj x y ∧ x ∈ Z ∧ y ∈ half i ∩ retained l i) ∧
        (∀ l i l' i', (l,i) ≠ (l',i') → Disjoint (pieces l i) (pieces l' i')) ∧
        (∀ l i, l ∈ requests i → ∀ x ∈ Z,
          profileCount (half i ∩ retained l i) (outProfile G x)/(k:ℝ)-η*(Fintype.card V:ℝ) ≤
            (outDegree (pieces l i) x:ℝ)) ∧
        ∀ l i, l ∈ requests i → ∀ y ∈ half i ∩ retained l i,
          (inDegree (pieces l i) y:ℝ) ≤ profileCount Z (inProfile G y)/(k:ℝ)+η*(Fintype.card V:ℝ) := by
  obtain ⟨N,hSplit⟩ := exists_exceptional_pair_split_on_retained_sets.{u} η hη k hk
  refine ⟨N,?_⟩
  intro V _ J L G Z half requests retained hN hHalf hSlots
  let slot (i : J) := Classical.choice (hSlots i)
  let target (i : J) (j : Fin k) : Finset V :=
    if h : ∃ l : ↥(requests i), slot i l = j then half i ∩ retained h.choose.val i else ∅
  have hTarget (i : J) (l : ↥(requests i)) : target i (slot i l) = half i ∩ retained l.val i := by
    have h : ∃ l' : ↥(requests i), slot i l' = slot i l := ⟨l,rfl⟩
    unfold target
    rw [dif_pos h,(slot i).injective h.choose_spec]
  have hSubset (i : J) (j : Fin k) : target i j ⊆ half i := by
    unfold target
    split
    · exact inter_subset_left
    · exact empty_subset _
  choose bank hBank hDis hOut hIn using fun i => hSplit G Z (half i) (target i) hN (hSubset i)
  let pieces (l : L) (i : J) := if h : l ∈ requests i then bank i (slot i ⟨l,h⟩) else ⊥
  have hAdj (l : L) (i : J) (x y : V) (h : (pieces l i).Adj x y) :
      ∃ hReq : l ∈ requests i, (bank i (slot i ⟨l,hReq⟩)).Adj x y := by
    by_cases hl : l ∈ requests i
    · exact ⟨hl,by simpa only [pieces,dif_pos hl] using h⟩
    · have he : pieces l i = ⊥ := dif_neg hl
      rw [he] at h
      exact h.elim
  have hArc (i : J) (l : ↥(requests i)) (x y : V) (h : (bank i (slot i l)).Adj x y) :
      G.Adj x y ∧ x ∈ Z ∧ y ∈ half i ∩ retained l.val i := by
    simpa only [hTarget i l] using hBank i (slot i l) x y h
  refine ⟨pieces,?_,?_,?_,?_⟩
  · intro l i x y h
    obtain ⟨hr,ha⟩ := hAdj l i x y h
    exact ⟨hr,hArc i ⟨l,hr⟩ x y ha⟩
  · intro l i l' i' hne
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hl,hl'⟩
    obtain ⟨hr,ha⟩ := hAdj l i x y hl
    obtain ⟨hr',ha'⟩ := hAdj l' i' x y hl'
    by_cases hi : i = i'
    · subst i'
      have hs : slot i ⟨l,hr⟩ ≠ slot i ⟨l',hr'⟩ :=
        fun he => hne (Prod.ext (congrArg Subtype.val ((slot i).injective he)) rfl)
      exact disjoint_iff_inf_le.mp (hDis i _ _ hs) ⟨ha,ha'⟩
    · exact disjoint_left.mp (hHalf i i' hi)
        (mem_inter.mp (hArc i ⟨l,hr⟩ x y ha).2.2).1
        (mem_inter.mp (hArc i' ⟨l',hr'⟩ x y ha').2.2).1
  · intro l i hr x hx
    simpa only [pieces,dif_pos hr,hTarget i ⟨l,hr⟩] using hOut i (slot i ⟨l,hr⟩) x hx
  · intro l i hr y hy
    exact (by
      simpa only [pieces,dif_pos hr] using hIn i (slot i ⟨l,hr⟩) y
        (by rwa [hTarget i ⟨l,hr⟩]))

end OverfullWork.DirectedRobustExpansion
