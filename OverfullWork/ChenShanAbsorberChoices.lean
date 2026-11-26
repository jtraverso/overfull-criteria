module

public import OverfullWork.ChenShanCycleAbsorber
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Sum
public import Mathlib.Tactic

@[expose] public section

namespace OverfullWork.ChenShan

open Finset
open scoped Classical

private theorem injective_update_on_insert {I X : Type*} (T : Finset I)
    (i : I) (_hi : i ∉ T) (z : I → X) (v : X) (hz : Set.InjOn z (↑T : Set I))
    (hv : v ∉ T.image z) : Set.InjOn (Function.update z i v) (↑(insert i T) : Set I) := by
  intro j hj₀ k hk₀ eq
  have hj : j ∈ insert i T := hj₀
  have hk : k ∈ insert i T := hk₀
  by_cases hj' : j = i
  · by_cases hk' : k = i
    · exact hj'.trans hk'.symm
    · have hkT := (mem_insert.mp hk).resolve_left hk'
      rw [hj',Function.update_self,Function.update_of_ne hk'] at eq
      exact (hv (mem_image.mpr ⟨k,hkT,eq.symm⟩)).elim
  · by_cases hk' : k = i
    · have hjT := (mem_insert.mp hj).resolve_left hj'
      rw [hk',Function.update_of_ne hj',Function.update_self] at eq
      exact (hv (mem_image.mpr ⟨j,hjT,eq⟩)).elim
    · exact hz ((mem_insert.mp hj).resolve_left hj') ((mem_insert.mp hk).resolve_left hk')
        (by simpa only [Function.update_of_ne hj',Function.update_of_ne hk'] using eq)

/-- Choose one compatible pair at each index; every new choice can
exclude all coordinates used at earlier indices. -/
theorem choose_distinct_pairs {I A B : Type*} [Nonempty A] [Nonempty B]
    (S : Finset I) (R : I → A → B → Prop)
    (hChoose : ∀ i ∈ S, ∀ P : Finset A, ∀ Q : Finset B,
      P.card < S.card → Q.card < S.card → ∃ a ∉ P, ∃ b ∉ Q, R i a b) :
    ∃ f : I → A, ∃ g : I → B, Set.InjOn f (↑S : Set I) ∧
      Set.InjOn g (↑S : Set I) ∧ ∀ i ∈ S, R i (f i) (g i) := by
  classical
  suffices h : ∀ T : Finset I, T ⊆ S → ∃ f : I → A, ∃ g : I → B,
      Set.InjOn f (↑T : Set I) ∧ Set.InjOn g (↑T : Set I) ∧ ∀ i ∈ T, R i (f i) (g i) from
    h S Subset.rfl
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => Classical.arbitrary A,fun _ => Classical.arbitrary B,
      by simp,by simp,by simp⟩
  | @insert i T hi ih =>
    intro hSub
    have hTS : T ⊆ S := (subset_insert i T).trans hSub
    have hIS : i ∈ S := hSub (mem_insert_self _ _)
    obtain ⟨f,g,hF,hG,hR⟩ := ih hTS
    have hCard : T.card < S.card := by
      have h := card_le_card hSub
      rw [card_insert_of_notMem hi] at h
      omega
    obtain ⟨a,ha,b,hb,hPair⟩ := hChoose i hIS (T.image f) (T.image g)
      (card_image_le.trans_lt hCard) (card_image_le.trans_lt hCard)
    refine ⟨Function.update f i a,Function.update g i b,
      injective_update_on_insert T i hi f a hF ha,
      injective_update_on_insert T i hi g b hG hb,?_⟩
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · simpa only [Function.update_self] using hPair
    · have hne : j ≠ i := fun h => hi (h ▸ hj)
      simpa only [Function.update_of_ne hne] using hR j hj

private theorem card_sdiff_real_lower {A : Type*} (S T : Finset A) :
    (S.card : ℝ) - T.card ≤ ((S \ T).card : ℝ) := by
  have h : (S.card : ℝ) ≤ ((S \ T).card : ℝ) + T.card := by
    exact_mod_cast (card_le_card_sdiff_add_card (s := S) (t := T))
  linarith only [h]

/-- A neighborhood remains large after imposing two color requirements
and excluding the two sets of already unavailable vertices. -/
theorem dense_candidates_card {A : Type*} [Fintype A]
    (E L R : A → Prop) (Z P : Finset A) (m η ε : ℝ)
    (hDegree : (1/2+η)*m ≤ ((univ.filter E : Finset A).card : ℝ))
    (hL : ((univ.filter fun a => ¬ L a : Finset A).card : ℝ) ≤ ε*m)
    (hR : ((univ.filter fun a => ¬ R a : Finset A).card : ℝ) ≤ ε*m)
    (hLoss : (Z.card : ℝ) + P.card + 2*ε*m ≤ η*m/2) :
    (1/2+η/2)*m ≤ ((univ.filter (fun a => E a ∧ L a ∧ R a ∧ a ∉ Z ∧ a ∉ P) : Finset A).card : ℝ) := by
  let BL : Finset A := univ.filter (fun a => ¬ L a)
  let BR : Finset A := univ.filter (fun a => ¬ R a)
  let T := (BL ∪ BR) ∪ (Z ∪ P)
  have hEq : (univ.filter E : Finset A) \ T =
      univ.filter (fun a => E a ∧ L a ∧ R a ∧ a ∉ Z ∧ a ∉ P) := by
    ext a
    simp [T,BL,BR]
  have h1 : (((BL ∪ BR).card : ℕ) : ℝ) ≤ BL.card + BR.card := by exact_mod_cast card_union_le BL BR
  have h2 : (((Z ∪ P).card : ℕ) : ℝ) ≤ Z.card + P.card := by exact_mod_cast card_union_le Z P
  have h3 : (T.card : ℝ) ≤ (BL ∪ BR).card + (Z ∪ P).card := by exact_mod_cast card_union_le (BL ∪ BR) (Z ∪ P)
  have h := card_sdiff_real_lower (univ.filter E : Finset A) T
  rw [hEq] at h
  change (BL.card : ℝ) ≤ ε*m at hL
  change (BR.card : ℝ) ≤ ε*m at hR
  linarith only [hDegree,hL,hR,hLoss,h1,h2,h3,h]


/-- Each cycle can find a single common auxiliary color after excluding
the forbidden colors and the missing incidences of its vertices. -/
theorem choose_common_auxiliary_color {I A B W : Type*} [Fintype I] [Fintype W]
    (x : I → A) (y : I → B) (AW : A → W → Prop) (BW : B → W → Prop)
    (Z : Finset W) (D : ℝ)
    (hA : ∀ a, ((univ.filter (fun w => ¬ AW a w) : Finset W).card : ℝ) ≤ D)
    (hB : ∀ b, ((univ.filter (fun w => ¬ BW b w) : Finset W).card : ℝ) ≤ D)
    (hRoom : (Z.card : ℝ) + (Fintype.card I : ℝ)*(2*D) < (Fintype.card W : ℝ)) :
    ∃ w ∉ Z, (∀ i, AW (x i) w) ∧ ∀ i, BW (y i) w := by
  let F (i : I) : Finset W := univ.filter (fun w => ¬ AW (x i) w) ∪
    univ.filter (fun w => ¬ BW (y i) w)
  let T : Finset W := univ.biUnion F
  have hF (i : I) : ((F i).card : ℝ) ≤ 2*D := by
    have h := hA (x i)
    have h' := hB (y i)
    have hU : ((F i).card : ℝ) ≤ ((univ.filter (fun w => ¬ AW (x i) w) : Finset W).card : ℝ) +
        ((univ.filter (fun w => ¬ BW (y i) w) : Finset W).card : ℝ) := by
      exact_mod_cast card_union_le (univ.filter (fun w => ¬ AW (x i) w) : Finset W)
        (univ.filter (fun w => ¬ BW (y i) w))
    linarith only [h,h',hU]
  have hT : (T.card : ℝ) ≤ (Fintype.card I : ℝ)*(2*D) := by
    calc
      _ ≤ ∑ i : I, ((F i).card : ℝ) := by
        exact_mod_cast (card_biUnion_le (s := (univ : Finset I)) (t := F))
      _ ≤ ∑ _ : I, 2*D := sum_le_sum fun i _ => hF i
      _ = _ := by simp
  have hUnion : ((Z ∪ T).card : ℝ) ≤ Z.card + T.card := by exact_mod_cast card_union_le Z T
  have hLoss := card_sdiff_real_lower (univ : Finset W) (Z ∪ T)
  rw [card_univ] at hLoss
  have hPos : 0 < (((univ : Finset W) \ (Z ∪ T)).card : ℝ) := by
    linarith only [hRoom,hT,hUnion,hLoss]
  have hp : 0 < ((univ : Finset W) \ (Z ∪ T)).card := by exact_mod_cast hPos
  obtain ⟨w,hw⟩ := card_pos.mp hp
  have hNot := (mem_sdiff.mp hw).2
  refine ⟨w,fun h => hNot (mem_union_left _ h),?_,?_⟩
  · intro i
    by_contra hn
    exact hNot (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hn⟩)⟩))
  · intro i
    by_contra hn
    exact hNot (mem_union_right _ (mem_biUnion.mpr ⟨i,mem_univ _,mem_union_right _ (mem_filter.mpr ⟨mem_univ _,hn⟩)⟩))

private theorem exists_edge_between_candidates {A B : Type*} [Fintype A]
    (AB : A → B → Prop) (X : Finset A) (Y : Finset B)
    (hX : (Fintype.card A : ℝ)/2 < X.card) (hY : Y.Nonempty)
    (hDeg : ∀ y ∈ Y, (Fintype.card A : ℝ)/2 ≤ ((univ.filter (fun a => AB a y) : Finset A).card : ℝ)) :
    ∃ a ∈ X, ∃ b ∈ Y, AB a b := by
  obtain ⟨b,hb⟩ := hY
  let N : Finset A := univ.filter (fun a => AB a b)
  have hD : (Fintype.card A : ℝ)/2 ≤ (N.card : ℝ) := hDeg b hb
  by_contra! hBad
  have hDis : Disjoint X N := Finset.disjoint_left.mpr fun a ha hn => hBad a ha b hb (mem_filter.mp hn).2
  have hc : (X.card : ℝ) + N.card ≤ (Fintype.card A : ℝ) := by
    exact_mod_cast ((card_union_of_disjoint hDis).symm.trans_le (card_le_univ (X ∪ N)))
  linarith only [hX,hD,hc]


/-- The local greedy embedding in Lemma 4.6. The three forbidden sets
may already contain auxiliary vertices used by earlier copies. -/
theorem exists_cycle_absorber_vertices {I A B W : Type*}
    [Fintype I] [Fintype A] [Fintype B] [Fintype W]
    (AB : A → B → Prop) (AW : A → W → Prop) (BW : B → W → Prop)
    (s : Equiv.Perm I) (x : I → A) (y : I → B) (w : I → W)
    (ZA : Finset A) (ZB : Finset B) (ZW : Finset W)
    (m η ε : ℝ) (hm : 0 < m) (hη : 0 < η) (hSizeA : (Fintype.card A : ℝ) = m)
    (hDegreeA : ∀ a, (1/2+η)*m ≤ ((univ.filter (AB a) : Finset B).card : ℝ))
    (hDegreeB : ∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => AB a b) : Finset A).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun z => ¬ AW a z) : Finset W).card : ℝ) ≤ ε*m)
    (hBW : ∀ b, ((univ.filter (fun z => ¬ BW b z) : Finset W).card : ℝ) ≤ ε*m)
    (hWA : ∀ z, ((univ.filter (fun a => ¬ AW a z) : Finset A).card : ℝ) ≤ ε*m)
    (hWB : ∀ z, ((univ.filter (fun b => ¬ BW b z) : Finset B).card : ℝ) ≤ ε*m)
    (hRoomW : (ZW.card : ℝ) + (Fintype.card I : ℝ)*(2*(ε*m)) < (Fintype.card W : ℝ))
    (hRoomA : (ZA.card : ℝ) + (Fintype.card I : ℝ) + 2*ε*m ≤ η*m/2)
    (hRoomB : (ZB.card : ℝ) + (Fintype.card I : ℝ) + 2*ε*m ≤ η*m/2) :
    ∃ z ∉ ZW, (∀ i, AW (x i) z ∧ BW (y i) z) ∧
      ∃ a : I ↪ A, ∃ b : I ↪ B, ∀ i,
        a i ∉ ZA ∧ b i ∉ ZB ∧ AB (x (s i)) (b i) ∧ AB (a i) (y i) ∧ AB (a i) (b i) ∧
        AW (a i) (w i) ∧ AW (a i) z ∧ BW (b i) (w i) ∧ BW (b i) z := by
  have hNonemptyA : Nonempty A := by
    apply Fintype.card_pos_iff.mp
    have h : 0 < (Fintype.card A : ℝ) := hSizeA.symm ▸ hm
    exact_mod_cast h
  let _ : Nonempty A := hNonemptyA
  let a₀ := Classical.choice hNonemptyA
  have hPositive : 0 < (1/2+η/2)*m := by positivity
  have hNonemptyB : Nonempty B := by
    apply Fintype.card_pos_iff.mp
    have h := hDegreeA a₀
    have hBound : ((univ.filter (AB a₀) : Finset B).card : ℝ) ≤ (Fintype.card B : ℝ) := by
      exact_mod_cast card_le_univ (univ.filter (AB a₀) : Finset B)
    have hPosB : 0 < (Fintype.card B : ℝ) :=
      (show 0 < (1/2+η)*m by positivity).trans_le (h.trans hBound)
    exact_mod_cast hPosB
  let _ : Nonempty B := hNonemptyB
  obtain ⟨z,hz,hzx,hzy⟩ := choose_common_auxiliary_color x y AW BW ZW (ε*m) hAW hBW hRoomW
  let R (i : I) (a : A) (b : B) : Prop :=
    a ∉ ZA ∧ b ∉ ZB ∧ AB (x (s i)) b ∧ AB a (y i) ∧ AB a b ∧
      AW a (w i) ∧ AW a z ∧ BW b (w i) ∧ BW b z
  have hChoose (i : I) (_ : i ∈ (univ : Finset I)) (P : Finset A) (Q : Finset B)
      (hP : P.card < (univ : Finset I).card) (hQ : Q.card < (univ : Finset I).card) :
      ∃ a ∉ P, ∃ b ∉ Q, R i a b := by
    let X := (univ : Finset A).filter
      (fun a => AB a (y i) ∧ AW a (w i) ∧ AW a z ∧ a ∉ ZA ∧ a ∉ P)
    let Y := (univ : Finset B).filter
      (fun b => AB (x (s i)) b ∧ BW b (w i) ∧ BW b z ∧ b ∉ ZB ∧ b ∉ Q)
    have hp : (P.card : ℝ) ≤ (Fintype.card I : ℝ) := by rw [card_univ] at hP; exact_mod_cast hP.le
    have hq : (Q.card : ℝ) ≤ (Fintype.card I : ℝ) := by rw [card_univ] at hQ; exact_mod_cast hQ.le
    have hX : (1/2+η/2)*m ≤ (X.card : ℝ) :=
      dense_candidates_card (fun a => AB a (y i)) (fun a => AW a (w i)) (fun a => AW a z)
        ZA P m η ε (hDegreeB (y i)) (hWA (w i)) (hWA z) (by linarith only [hp,hRoomA])
    have hY : (1/2+η/2)*m ≤ (Y.card : ℝ) :=
      dense_candidates_card (AB (x (s i))) (fun b => BW b (w i)) (fun b => BW b z)
        ZB Q m η ε (hDegreeA (x (s i))) (hWB (w i)) (hWB z) (by linarith only [hq,hRoomB])
    have hPosY : 0 < Y.card := by exact_mod_cast hPositive.trans_le hY
    have hGain := mul_pos hη hm
    obtain ⟨a,ha,b,hb,hab⟩ := exists_edge_between_candidates AB X Y
      (by rw [hSizeA]; nlinarith only [hX,hGain]) (card_pos.mp hPosY)
      (fun b _ => by rw [hSizeA]; have h := hDegreeB b; nlinarith only [h,hGain])
    obtain ⟨ha₁,ha₂,ha₃,ha₄,ha₅⟩ := (mem_filter.mp ha).2
    obtain ⟨hb₁,hb₂,hb₃,hb₄,hb₅⟩ := (mem_filter.mp hb).2
    exact ⟨a,ha₅,b,hb₅,ha₄,hb₄,hb₁,ha₁,hab,ha₂,ha₃,hb₂,hb₃⟩
  obtain ⟨a,b,ha,hb,hRows⟩ := choose_distinct_pairs (univ : Finset I) R hChoose
  exact ⟨z,hz,fun i => ⟨hzx i,hzy i⟩,
    ⟨a,fun {i j} h => ha (mem_univ i) (mem_univ j) h⟩,
    ⟨b,fun {i j} h => hb (mem_univ i) (mem_univ j) h⟩,fun i => hRows i (mem_univ _)⟩


/-- Successive choices with a global vertex budget. The step reserves
space for the current copy in addition to all vertices already used. -/
theorem choose_pairwise_disjoint_bounded_sets {I V : Type*} (S : Finset I)
    (size : I → ℕ) (Good : I → Finset V → Prop)
    (hChoose : ∀ i ∈ S, ∀ used : Finset V, used.card + size i ≤ ∑ j ∈ S, size j →
      ∃ A : Finset V, Good i A ∧ A.card ≤ size i ∧ Disjoint A used) :
    ∃ A : I → Finset V, (↑S : Set I).PairwiseDisjoint A ∧
      ∀ i ∈ S, Good i (A i) ∧ (A i).card ≤ size i := by
  classical
  suffices h : ∀ T : Finset I, T ⊆ S → ∃ A : I → Finset V,
      (↑T : Set I).PairwiseDisjoint A ∧ ∀ i ∈ T, Good i (A i) ∧ (A i).card ≤ size i from
    h S Subset.rfl
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => ∅,by simp [Set.PairwiseDisjoint, Set.Pairwise],by simp⟩
  | @insert i T hi ih =>
    intro hSub
    have hTS : T ⊆ S := (subset_insert i T).trans hSub
    have hIS : i ∈ S := hSub (mem_insert_self _ _)
    obtain ⟨A,hDis,hA⟩ := ih hTS
    let used := T.biUnion A
    have hL : used.card ≤ ∑ j ∈ T, size j :=
      (card_biUnion_le (s := T) (t := A)).trans (sum_le_sum fun j hj => (hA j hj).2)
    have hRoom : used.card + size i ≤ ∑ j ∈ S, size j := by
      have h := sum_le_sum_of_subset_of_nonneg hSub (fun j _ _ => Nat.zero_le (size j))
      rw [sum_insert hi] at h
      omega
    obtain ⟨Q,hQ,hSize,hFresh⟩ := hChoose i hIS used hRoom
    refine ⟨Function.update A i Q,?_,?_⟩
    · intro j hj₀ k hk₀ hjk
      change Disjoint (Function.update A i Q j) (Function.update A i Q k)
      have hj : j ∈ insert i T := hj₀
      have hk : k ∈ insert i T := hk₀
      by_cases hji : j = i
      · have hki : k ≠ i := fun h => hjk (hji.trans h.symm)
        have hkT := (mem_insert.mp hk).resolve_left hki
        rw [hji,Function.update_self,Function.update_of_ne hki]
        exact hFresh.mono_right (fun _ hu => mem_biUnion.mpr ⟨k,hkT,hu⟩)
      · by_cases hki : k = i
        · have hjT := (mem_insert.mp hj).resolve_left hji
          rw [hki,Function.update_self,Function.update_of_ne hji]
          exact hFresh.symm.mono_left (fun _ hu => mem_biUnion.mpr ⟨j,hjT,hu⟩)
        · rw [Function.update_of_ne hji,Function.update_of_ne hki]
          exact hDis ((mem_insert.mp hj).resolve_left hji) ((mem_insert.mp hk).resolve_left hki) hjk
    · intro j hj
      by_cases h : j = i
      · subst j
        simpa only [Function.update_self] using And.intro hQ hSize
      · simpa only [Function.update_of_ne h] using hA j ((mem_insert.mp hj).resolve_left h)


/-- An embedded absorber on the nine edges per cycle index of Lemma 4.5,
together with its auxiliary vertices in the three ambient classes. -/
def CycleAbsorberFootprint {I A B W : Type*} [Fintype I]
    (AB : A → B → Prop) (AW : A → W → Prop) (BW : B → W → Prop)
    (s : Equiv.Perm I) (x : I → A) (y : I → B) (w : I → W)
    (S : Finset (A ⊕ (B ⊕ W))) : Prop :=
  ∃ z : W, ∃ a : I ↪ A, ∃ b : I ↪ B,
    S = (univ.map a).disjSum ((univ.map b).disjSum {z}) ∧
    ∀ i, AW (x (s i)) z ∧ BW (y i) z ∧ AB (x (s i)) (b i) ∧ AB (a i) (y i) ∧
      AB (a i) (b i) ∧ AW (a i) (w i) ∧ AW (a i) z ∧ BW (b i) (w i) ∧ BW (b i) z

/-- The successive embeddings in Lemma 4.6. The cover list carries
one index for each requested cycle; every copy avoids the fixed set
and all auxiliary vertices in every other copy. -/
theorem exists_disjoint_cycle_absorber_footprints {J A B W : Type*}
    [Fintype A] [Fintype B] [Fintype W]
    (S : Finset J) (length : J → ℕ)
    (AB : A → B → Prop) (AW : A → W → Prop) (BW : B → W → Prop)
    (s : ∀ j, Equiv.Perm (Fin (length j))) (x : ∀ j, Fin (length j) → A)
    (y : ∀ j, Fin (length j) → B) (w : ∀ j, Fin (length j) → W)
    (Z : Finset (A ⊕ (B ⊕ W)))
    (m η γ ε : ℝ) (hm : 0 < m) (hη : 0 < η) (hγ : 0 < γ)
    (hSizeA : (Fintype.card A : ℝ) = m) (hSizeW : γ*m ≤ (Fintype.card W : ℝ))
    (hDegreeA : ∀ a, (1/2+η)*m ≤ ((univ.filter (AB a) : Finset B).card : ℝ))
    (hDegreeB : ∀ b, (1/2+η)*m ≤ ((univ.filter (fun a => AB a b) : Finset A).card : ℝ))
    (hAW : ∀ a, ((univ.filter (fun z => ¬ AW a z) : Finset W).card : ℝ) ≤ ε*m)
    (hBW : ∀ b, ((univ.filter (fun z => ¬ BW b z) : Finset W).card : ℝ) ≤ ε*m)
    (hWA : ∀ z, ((univ.filter (fun a => ¬ AW a z) : Finset A).card : ℝ) ≤ ε*m)
    (hWB : ∀ z, ((univ.filter (fun b => ¬ BW b z) : Finset B).card : ℝ) ≤ ε*m)
    (hEps : ε ≤ η/32)
    (hCycle : ∀ j ∈ S, 2*(length j : ℝ)*ε ≤ γ/16)
    (hZ : (Z.card : ℝ) ≤ min η γ * m/16)
    (hTotal : (↑(∑ j ∈ S, (2*length j+1)) : ℝ) ≤ min η γ * m/16) :
    ∃ Q : J → Finset (A ⊕ (B ⊕ W)), (↑S : Set J).PairwiseDisjoint Q ∧
      ∀ j ∈ S, CycleAbsorberFootprint AB AW BW (s j) (x j) (y j) (w j) (Q j) ∧
        Disjoint (Q j) Z ∧ (Q j).card ≤ 2*length j+1 := by
  let Good (j : J) (F : Finset (A ⊕ (B ⊕ W))) :=
    CycleAbsorberFootprint AB AW BW (s j) (x j) (y j) (w j) F ∧ Disjoint F Z
  suffices hPick : ∀ j ∈ S, ∀ used : Finset (A ⊕ (B ⊕ W)),
      used.card + (2*length j+1) ≤ ∑ k ∈ S, (2*length k+1) →
      ∃ Q : Finset (A ⊕ (B ⊕ W)), Good j Q ∧ Q.card ≤ 2*length j+1 ∧ Disjoint Q used by
    obtain ⟨Q,hDis,hQ⟩ := choose_pairwise_disjoint_bounded_sets S (fun j => 2*length j+1) Good hPick
    exact ⟨Q,hDis,fun j hj => ⟨(hQ j hj).1.1,(hQ j hj).1.2,(hQ j hj).2⟩⟩
  intro j hj used hRoom
  let F := Z ∪ used
  have hF : F.card ≤ Z.card + used.card := card_union_le Z used
  have hFA : (F.toLeft.card : ℝ) ≤ (Z.card : ℝ) + used.card := by
    exact_mod_cast (card_toLeft_le.trans hF : F.toLeft.card ≤ Z.card+used.card)
  have hFB : (F.toRight.toLeft.card : ℝ) ≤ (Z.card : ℝ) + used.card := by
    exact_mod_cast (card_toLeft_le.trans (card_toRight_le.trans hF) :
      F.toRight.toLeft.card ≤ Z.card+used.card)
  have hFW : (F.toRight.toRight.card : ℝ) ≤ (Z.card : ℝ) + used.card := by
    exact_mod_cast (card_toRight_le.trans (card_toRight_le.trans hF) :
      F.toRight.toRight.card ≤ Z.card+used.card)
  let K : ℕ := ∑ j' ∈ S, (2*length j'+1)
  have hu : (used.card : ℝ) + (length j : ℝ) ≤ (K : ℝ) := by
    change used.card + (2*length j+1) ≤ K at hRoom
    exact_mod_cast (show used.card + length j ≤ K by omega)
  have hηLoss : min η γ*m/16 ≤ η*m/16 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hm.le) (by norm_num)
  have hγLoss : min η γ*m/16 ≤ γ*m/16 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hm.le) (by norm_num)
  have hE := mul_le_mul_of_nonneg_right hEps hm.le
  have hW := mul_le_mul_of_nonneg_right (hCycle j hj) hm.le
  have hγm := mul_pos hγ hm
  have hηm := mul_pos hη hm
  change (K : ℝ) ≤ _ at hTotal
  obtain ⟨z,hz,hCommon,a,b,hRows⟩ := exists_cycle_absorber_vertices AB AW BW (s j) (x j) (y j) (w j)
    F.toLeft F.toRight.toLeft F.toRight.toRight m η ε hm hη hSizeA hDegreeA hDegreeB
    hAW hBW hWA hWB
    (by rw [Fintype.card_fin]; nlinarith only [hFW,hu,hZ,hTotal,hγLoss,hW,hSizeW,hγm])
    (by rw [Fintype.card_fin]; nlinarith only [hFA,hu,hZ,hTotal,hηLoss,hE,hηm])
    (by rw [Fintype.card_fin]; nlinarith only [hFB,hu,hZ,hTotal,hηLoss,hE,hηm])
  let Q : Finset (A ⊕ (B ⊕ W)) := (univ.map a).disjSum ((univ.map b).disjSum {z})
  have hFresh : Disjoint Q F := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    rcases v with v | (v | v)
    · have hv' : v ∈ univ.map a := by simpa [Q] using hv
      obtain ⟨i,_,rfl⟩ := mem_map.mp hv'
      exact (hRows i).1 (mem_toLeft.mpr hf)
    · have hv' : v ∈ univ.map b := by simpa [Q] using hv
      obtain ⟨i,_,rfl⟩ := mem_map.mp hv'
      exact (hRows i).2.1 (mem_toLeft.mpr (mem_toRight.mpr hf))
    · have hv' : v = z := by simpa [Q] using hv
      subst v
      exact hz (mem_toRight.mpr (mem_toRight.mpr hf))
  have hFoot : CycleAbsorberFootprint AB AW BW (s j) (x j) (y j) (w j) Q := by
    refine ⟨z,a,b,rfl,?_⟩
    intro i
    exact ⟨(hCommon (s j i)).1,(hCommon i).2,(hRows i).2.2⟩
  exact ⟨Q,⟨hFoot,hFresh.mono_right subset_union_left⟩,
    by simp [Q,card_disjSum,two_mul,Nat.add_assoc],hFresh.mono_right subset_union_right⟩


/-- The sum of the edge and auxiliary-vertex budgets across all
remainders is bounded by the paper's `4 h² 2^(h²)`. -/
theorem cycle_absorber_total_budget {I J : Type*} (L : Finset I) (cycles : I → Finset J)
    (length : I → J → ℕ) (h : ℕ)
    (hL : L.card ≤ 2^(h^2))
    (hPositive : ∀ i ∈ L, ∀ j ∈ cycles i, 0 < length i j)
    (hEdges : ∀ i ∈ L, (∑ j ∈ cycles i, 3*length i j) ≤ h^2) :
    (∑ i ∈ L, ∑ j ∈ cycles i, (9*length i j + (2*length i j+1))) ≤ 4*(h^2)*(2^(h^2)) := by
  calc
    _ ≤ ∑ i ∈ L, ∑ j ∈ cycles i, 4*(3*length i j) := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro j hj
      have hP := hPositive i hi j hj
      omega
    _ ≤ ∑ _ ∈ L, 4*(h^2) := by
      apply sum_le_sum
      intro i hi
      rw [← mul_sum]
      exact Nat.mul_le_mul_left _ (hEdges i hi)
    _ = L.card * (4*h^2) := by simp
    _ ≤ 2^(h^2)*(4*h^2) := Nat.mul_le_mul_right _ hL
    _ = _ := by ring


/-- Two copies with disjoint fresh footprints share no edge when every
edge has a fresh endpoint and its other endpoint is fixed or fresh
in that same copy. -/
theorem no_shared_absorber_edge {V : Type*} (Z P Q : Finset V)
    (hP : Disjoint P Z) (hPQ : Disjoint P Q) (u v : V)
    (huQ : u ∈ Z ∪ Q) (hvQ : v ∈ Z ∪ Q) :
    ¬ (u ∈ P ∨ v ∈ P) := by
  intro h
  have noP (a : V) (ha : a ∈ P) (hb : a ∈ Z ∪ Q) : False := by
    rcases mem_union.mp hb with hZ | hQ
    · exact Finset.disjoint_left.mp hP ha hZ
    · exact Finset.disjoint_left.mp hPQ ha hQ
  exact h.elim (fun hu => noP u hu huQ) (fun hv => noP v hv hvQ)

end OverfullWork.ChenShan
