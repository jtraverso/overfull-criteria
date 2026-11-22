module

public import OverfullWork.OsthusStadenH1RedProfiles
public import OverfullWork.KuhnOsthusCodegreeCount

@[expose] public section


/-! Choose the two physical endpoints of each exceptional edge in
Kühn–Osthus Lemma 7.5(i), keeping every cluster below its capacity. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset
open scoped Classical
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J]

/-- A choice excludes all previously used vertices and all vertices in
saturated clusters. Distinctness is maintained across all requests. -/
theorem exists_distinct_representatives_with_cluster_cap [Inhabited V]
    (cluster : V → I) (A : J → Finset V) (m cap budget : ℕ)
    (hSize : ∀ i, ((univ : Finset V).filter (fun x => cluster x = i)).card ≤ m)
    (hBudget : Fintype.card J < cap*(budget+1))
    (hLarge : ∀ j, Fintype.card J + budget*m < (A j).card) :
    ∃ f : J → V, Function.Injective f ∧ (∀ j, f j ∈ A j) ∧
      ∀ i, ((univ.filter (fun j => cluster (f j) = i) : Finset J)).card ≤ cap := by
  classical
  have hStep (P : Finset J) :
      ∃ f : J → V, Set.InjOn f (↑P : Set J) ∧ (∀ j ∈ P, f j ∈ A j) ∧
        ∀ i, ((P.image f).filter (fun x => cluster x = i)).card ≤ cap := by
    induction P using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => default,by simp,by simp,by simp⟩
    | @insert j P hj ih =>
      obtain ⟨f,hInj,hf,hLoad⟩ := ih
      let U := P.image f
      let B := (univ : Finset I).filter (fun i => cap ≤ (U.filter (fun x => cluster x = i)).card)
      have hMass : cap*B.card ≤ U.card := by
        calc
          _ = ∑ _i ∈ B,cap := by simp [Nat.mul_comm]
          _ ≤ ∑ i ∈ B,(U.filter (fun x => cluster x = i)).card :=
            sum_le_sum (fun _ hi => (mem_filter.mp hi).2)
          _ = (U.filter (fun x => cluster x ∈ B)).card :=
            sum_card_fiberwise_eq_card_filter U B cluster
          _ ≤ _ := card_filter_le _ _
      have hU : U.card ≤ Fintype.card J :=
        (card_image_le (s := P) (f := f)).trans (card_le_univ P)
      have hB : B.card ≤ budget := by
        by_contra! h
        have hs := Nat.mul_le_mul_left cap (show budget+1 ≤ B.card by omega)
        omega
      let T := (univ : Finset V).filter (fun x => cluster x ∈ B)
      have hT : T.card ≤ budget*m := by
        calc
          _ = ∑ i ∈ B,((univ : Finset V).filter (fun x => cluster x = i)).card :=
            (sum_card_fiberwise_eq_card_filter univ B cluster).symm
          _ ≤ ∑ _i ∈ B,m := sum_le_sum fun i _ => hSize i
          _ ≤ _ := by simpa only [sum_const,Nat.nsmul_eq_mul] using Nat.mul_le_mul_right m hB
      have hNot : ¬ A j ⊆ U ∪ T := by
        intro h
        have hh := (card_le_card h).trans (card_union_le U T)
        have ha := hLarge j
        omega
      obtain ⟨x,hAx,hFree⟩ := not_subset.mp hNot
      have hxU : x ∉ U := fun h => hFree (mem_union_left _ h)
      have hxB : cluster x ∉ B := fun h => hFree (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h⟩))
      let g := Function.update f j x
      have hgj : g j = x := Function.update_self _ _ _
      have hSame (p : J) (hp : p ∈ P) : g p = f p := by
        have hne : p ≠ j := fun h => hj (h ▸ hp)
        exact Function.update_of_ne hne _ _
      have hImage : (insert j P).image g = insert x U := by
        rw [image_insert,hgj]
        exact congrArg (insert x) (image_congr (fun p hp => hSame p hp))
      refine ⟨g,?_,?_,?_⟩
      · intro a ha b hb hab
        rcases mem_insert.mp ha with haj | hap
        · rcases mem_insert.mp hb with hbj | hbp
          · exact haj.trans hbj.symm
          · rw [haj,hgj,hSame b hbp] at hab
            exact (hxU (mem_image.mpr ⟨b,hbp,hab.symm⟩)).elim
        · rcases mem_insert.mp hb with hbj | hbp
          · rw [hbj,hSame a hap,hgj] at hab
            exact (hxU (mem_image.mpr ⟨a,hap,hab⟩)).elim
          · exact hInj hap hbp (by rwa [hSame a hap,hSame b hbp] at hab)
      · intro p hp
        rcases mem_insert.mp hp with rfl | hp
        · rwa [hgj]
        · rw [hSame p hp]
          exact hf p hp
      · intro i
        rw [hImage,filter_insert]
        split
        · rename_i hi
          have hOld : (U.filter (fun y => cluster y = i)).card < cap := by
            by_contra! h
            exact hxB (mem_filter.mpr ⟨mem_univ _,by rwa [hi]⟩)
          rw [card_insert_of_notMem (notMem_mono (filter_subset _ _) hxU)]
          omega
        · exact hLoad i
  obtain ⟨f,hInj,hf,hCap⟩ := hStep (univ : Finset J)
  have hFull : Function.Injective f := fun _ _ h => hInj (mem_univ _) (mem_univ _) h
  refine ⟨f,hFull,fun j => hf j (mem_univ _),fun i => ?_⟩
  rw [← card_image_of_injective _ hFull]
  apply (card_le_card ?_).trans (hCap i)
  intro x hx
  obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
  exact mem_filter.mpr ⟨mem_image.mpr ⟨j,mem_univ _,rfl⟩,(mem_filter.mp hj).2⟩

omit [Fintype J] in
/-- Both sides of every exceptional vertex receive distinct endpoints
in the prescribed interior style. The load counts both directions. -/
theorem exists_exceptional_endpoints_in_style [Inhabited V]
    (G : Digraph V) (Z S : Finset V) (cluster : V → I) (m cap budget : ℕ)
    (hSize : ∀ i, ((univ : Finset V).filter (fun x => cluster x = i)).card ≤ m)
    (hBudget : 2*Z.card < cap*(budget+1))
    (hIn : ∀ z ∈ Z, 2*Z.card + budget*m < inNeighbours G S z)
    (hOut : ∀ z ∈ Z, 2*Z.card + budget*m < outTo G S z) :
    ∃ endpoint : Bool × Z → V, Function.Injective endpoint ∧
      (∀ z : Z, endpoint (false,z) ∈ S ∧ endpoint (true,z) ∈ S ∧
        G.Adj (endpoint (false,z)) z ∧ G.Adj z (endpoint (true,z))) ∧
      ∀ i, ((univ : Finset (Bool × Z)).filter (fun p => cluster (endpoint p) = i)).card ≤ cap := by
  let A (p : Bool × Z) :=
    S.filter (fun v => if p.1 then G.Adj p.2 v else G.Adj v p.2)
  have hCard : Fintype.card (Bool × Z) = 2*Z.card := by simp
  have hLarge (p : Bool × Z) : Fintype.card (Bool × Z)+budget*m < (A p).card := by
    rw [hCard]
    rcases p with ⟨p,z⟩
    cases p
    · simpa only [A,Bool.false_eq_true,ite_false,inNeighbours] using hIn z z.prop
    · simpa only [A,ite_true,outTo] using hOut z z.prop
  obtain ⟨f,hf,hMem,hCap⟩ := exists_distinct_representatives_with_cluster_cap cluster A
    m cap budget hSize (by rwa [hCard]) hLarge
  refine ⟨f,hf,fun z => ?_,hCap⟩
  have hin : f (false,z) ∈ S ∧ G.Adj (f (false,z)) z := by
    simpa only [A,mem_filter,Bool.false_eq_true,ite_false] using hMem (false,z)
  have hout : f (true,z) ∈ S ∧ G.Adj z (f (true,z)) := by
    simpa only [A,mem_filter,ite_true] using hMem (true,z)
  exact ⟨hin.1,hout.1,hin.2,hout.2⟩

/-- Many coarse clusters are friendly when the total neighbourhood
is large. Every nonfriendly cluster contributes below the threshold. -/
theorem friendly_cluster_mass {U V : Type*} [Fintype U]
    (P : U → Finset V) (Q : Finset V) (m t : ℝ) (ht : 0 ≤ t)
    (hSize : ∀ u, ((P u).card:ℝ) ≤ m)
    (hDis : ∀ u v, u ≠ v → Disjoint (P u) (P v)) :
    let F := (univ : Finset U).filter (fun u => t ≤ profileCount (P u) Q)
    profileCount (univ.biUnion P) Q ≤ (F.card:ℝ)*m + (Fintype.card U:ℝ)*t := by
  classical
  dsimp only
  let F := (univ : Finset U).filter (fun u => t ≤ profileCount (P u) Q)
  have h : ∀ u : U, profileCount (P u) Q ≤ (if u ∈ F then m else 0) + t := by
    intro u
    by_cases hu : u ∈ F
    · rw [if_pos hu]
      have hm : profileCount (P u) Q ≤ ((P u).card:ℝ) := by
        unfold profileCount
        exact_mod_cast card_le_card (inter_subset_left : P u ∩ Q ⊆ P u)
      linarith only [hm,hSize u,ht]
    · rw [if_neg hu,zero_add]
      have hlt : profileCount (P u) Q < t :=
        lt_of_not_ge (fun hh => hu (mem_filter.mpr ⟨mem_univ _,hh⟩))
      exact hlt.le
  have hMass := sum_le_sum (s := (univ : Finset U)) fun u _ => h u
  rw [sum_add_distrib,←sum_filter] at hMass
  have he : (univ : Finset U).filter (fun u => u ∈ F) = F := by simp
  rw [he, sum_const,sum_const,card_univ,nsmul_eq_mul,nsmul_eq_mul] at hMass
  rw [profile_count_disjoint_union _ _ _ (fun u _ v _ huv => hDis u v huv)]
  exact hMass

/-- Count the retained neighbours across the interval in (7.1).
Each friendly coarse cluster provides at least `D` fine clusters
in the interior, and uniform refinement preserves its neighbourhood
in the chosen style of each such fine cluster. -/
theorem exceptional_interval_profile_lower {U I V : Type*}
    (base : I → U) (F : Finset U) (T : Finset I) (C A : I → Finset V)
    (Q : Finset V) (K D : ℕ) (ε b : ℝ) (hε : ε ≤ 1) (hb : 0 ≤ b)
    (hDis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → Disjoint (A i) (A j))
    (hCopies : ∀ u ∈ F, D ≤ (T.filter (fun i => base i = u)).card)
    (hFine : ∀ i ∈ T, base i ∈ F →
      ε*((C i).card:ℝ) ≤ profileCount (C i) Q ∧ b ≤ profileCount (C i) Q)
    (hStyle : ∀ i ∈ T, UniformProfileCell (fun _ : Unit => Q) (C i) (A i) K ε) :
    ((F.card*D:ℕ):ℝ)*((1-ε)*(b/(K:ℝ))) ≤ profileCount (T.biUnion A) Q := by
  classical
  let M := T.filter (fun i => base i ∈ F)
  let q : ℝ := (1-ε)*(b/(K:ℝ))
  have hq : 0 ≤ q := mul_nonneg (sub_nonneg.mpr hε) (div_nonneg hb (Nat.cast_nonneg K))
  have hCard : F.card*D ≤ M.card := by
    calc
      _ = ∑ _u ∈ F,D := by rw [sum_const,Nat.nsmul_eq_mul]
      _ ≤ ∑ u ∈ F,(T.filter (fun i => base i = u)).card := sum_le_sum hCopies
      _ = _ := sum_card_fiberwise_eq_card_filter T F base
  have hPer (i : I) (hi : i ∈ M) : q ≤ profileCount (A i) Q := by
    obtain ⟨hi,hBase⟩ := mem_filter.mp hi
    obtain ⟨hThresh,hB⟩ := hFine i hi hBase
    have h := (abs_le.mp (hStyle i hi () hThresh)).1
    have hre : (1-ε)*(profileCount (C i) Q/(K:ℝ)) ≤ profileCount (A i) Q := by
      linarith only [h]
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB (Nat.cast_nonneg K))
      (sub_nonneg.mpr hε)).trans hre
  rw [profile_count_disjoint_union _ _ _ hDis]
  calc
    _ ≤ (M.card:ℝ)*q := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hq
    _ = ∑ _i ∈ M,q := by rw [sum_const,nsmul_eq_mul]
    _ ≤ ∑ i ∈ M, profileCount (A i) Q := sum_le_sum hPer
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)

/-- In any fixed set of vertices, deleting arcs reduces the
neighbourhood by at most the loss at the exceptional vertex. -/
theorem exceptional_style_neighbourhood_after_deletion
    (G H : Digraph V) (S : Finset V) (z : V) (k : ℕ)
    (hH : H ≤ G) (hIn : inDegree (G \ H) z ≤ k) (hOut : outDegree (G \ H) z ≤ k) :
    inNeighbours G S z ≤ inNeighbours H S z+k ∧ outTo G S z ≤ outTo H S z+k := by
  classical
  have hLoss (p r : V → Prop) (hSub : ∀ x, r x → p x)
      (hB : (univ.filter (fun x => p x ∧ ¬r x)).card ≤ k) :
      (S.filter p).card ≤ (S.filter r).card+k := by
    have he : S.filter p = (S.filter r) ∪ (S.filter (fun x => p x ∧ ¬r x)) := by
      ext x
      simp only [mem_filter,mem_union]
      by_cases hx : r x
      · simp [hx,hSub x hx]
      · simp [hx]
    rw [he]
    exact (card_union_le _ _).trans (Nat.add_le_add_left
      ((card_le_card (filter_subset_filter _ (subset_univ _))).trans hB) _)
  constructor
  · apply hLoss (fun x => G.Adj x z) (fun x => H.Adj x z) (fun _ h => hH h)
    unfold inDegree inNeighbours at hIn
    convert hIn using 2
    ext x
    simp only [mem_filter,Digraph.sdiff_adj]
  · apply hLoss (G.Adj z) (H.Adj z) (fun _ h => hH h)
    unfold outDegree at hOut
    convert hOut using 2
    ext x
    simp only [mem_filter,Digraph.sdiff_adj]

/-- Whole winding rounds have exactly one position per coarse
cluster and per round. -/
theorem card_winding_interval_fibre {U I : Type*} [Fintype U]
    (D : ℕ) (e : Fin D × U ↪ I) (base : I → U)
    (hBase : ∀ x, base (e x) = x.2) (u : U) :
    (((univ : Finset (Fin D × U)).map e).filter (fun i => base i = u)).card = D := by
  classical
  let f : Fin D ↪ I := ⟨fun d => e (d,u),fun d d' h => congrArg Prod.fst (e.injective h)⟩
  have he : ((univ : Finset (Fin D × U)).map e).filter (fun i => base i = u) =
      (univ : Finset (Fin D)).map f := by
    ext i
    constructor
    · intro hi
      obtain ⟨hm,hEq⟩ := mem_filter.mp hi
      obtain ⟨⟨d,v⟩,_,rfl⟩ := mem_map.mp hm
      have hv : v = u := (hBase (d,v)).symm.trans hEq
      subst v
      exact mem_map.mpr ⟨d,mem_univ _,rfl⟩
    · intro hi
      obtain ⟨d,_,rfl⟩ := mem_map.mp hi
      exact mem_filter.mpr ⟨mem_map.mpr ⟨(d,u),mem_univ _,rfl⟩,hBase (d,u)⟩
  rw [he,card_map,card_univ,Fintype.card_fin]

/-- Deleting the boundary positions loses at most the total boundary
size from any given fibre, as used in (7.1). -/
theorem winding_interval_copies {U I : Type*} [Fintype U]
    (D loss : ℕ) (e : Fin D × U ↪ I) (base : I → U)
    (hBase : ∀ x, base (e x) = x.2) (S : Finset I)
    (hLoss : (((univ : Finset (Fin D × U)).map e) \ S).card ≤ loss) :
    ∀ u, D-loss ≤ (S.filter (fun i => base i = u)).card := by
  classical
  intro u
  let T := (univ : Finset (Fin D × U)).map e
  let A := T.filter (fun i => base i = u)
  have hA : A.card = D := card_winding_interval_fibre D e base hBase u
  have hBad : (A \ S).card ≤ loss :=
    (card_le_card (sdiff_subset_sdiff_left S (filter_subset _ _))).trans hLoss
  have hGood : A ∩ S ⊆ S.filter (fun i => base i = u) := by
    intro x hx
    obtain ⟨ha,hs⟩ := mem_inter.mp hx
    exact mem_filter.mpr ⟨hs,(mem_filter.mp ha).2⟩
  have hCount := card_sdiff_add_card_inter A S
  have hCard := card_le_card hGood
  omega

/-- Build the endpoint matching in the residual host once the two
neighbourhood counts in the original host clear the stated loss budget. -/
theorem exists_exceptional_endpoints_after_deletion [Inhabited V]
    (G H : Digraph V) (Z S : Finset V) (cluster : V → I) (m cap budget loss : ℕ)
    (hH : H ≤ G)
    (hSize : ∀ i, ((univ : Finset V).filter (fun x => cluster x = i)).card ≤ m)
    (hBudget : 2*Z.card < cap*(budget+1))
    (hIn : ∀ z ∈ Z, 2*Z.card + budget*m+loss < inNeighbours G S z)
    (hOut : ∀ z ∈ Z, 2*Z.card + budget*m+loss < outTo G S z)
    (hLoss : ∀ z ∈ Z, inDegree (G \ H) z ≤ loss ∧ outDegree (G \ H) z ≤ loss) :
    ∃ endpoint : Bool × Z → V, Function.Injective endpoint ∧
      (∀ z : Z, endpoint (false,z) ∈ S ∧ endpoint (true,z) ∈ S ∧
        H.Adj (endpoint (false,z)) z ∧ H.Adj z (endpoint (true,z))) ∧
      ∀ i, ((univ : Finset (Bool × Z)).filter (fun p => cluster (endpoint p) = i)).card ≤ cap := by
  apply exists_exceptional_endpoints_in_style H Z S cluster m cap budget hSize hBudget
  · intro z hz
    have h := (exceptional_style_neighbourhood_after_deletion G H S z loss hH
      (hLoss z hz).1 (hLoss z hz).2).1
    have hg := hIn z hz
    omega
  · intro z hz
    have h := (exceptional_style_neighbourhood_after_deletion G H S z loss hH
      (hLoss z hz).1 (hLoss z hz).2).2
    have hg := hOut z hz
    omega

end OverfullWork.DirectedRobustExpansion
