module

public import OverfullWork.OsthusStadenPrimaryPairProfiles
public import OverfullWork.OsthusStadenSliceRegularity
public import OverfullWork.OsthusStadenControlledPrimaryPairs

@[expose] public section


/-! Two-sided superregular trimming on the primary factors of §5.3. -/
namespace OverfullWork.DirectedRegularPairs

open Finset DirectedRobustExpansion DirectedClusterQuotient
open scoped Classical

variable {V I : Type*} [Fintype V] [Fintype I]

/-- Remove atypical vertices from both sides of every successor pair.
A common deletion count works for all cycles of the permutation. -/
theorem exists_two_sided_trimmed_cycle_pairs (s : Equiv.Perm I) (D : I → Digraph V)
    (t m : ℕ) (ε δ d : ℝ) (hD : ∀ i, IsCentredRegular (D i) ε d)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hn : 0 < Fintype.card V)
    (hd : 0 ≤ d) (hd₁ : d ≤ 1) (ht : t+m = Fintype.card V)
    (hBudget : 8*ε*(Fintype.card V:ℝ) ≤ (t:ℝ))
    (hReg : 2*ε ≤ δ) (hLarge : (Fintype.card V:ℝ)*ε ≤ (m:ℝ))
    (hScale : (Fintype.card V:ℝ)*ε ≤ (m:ℝ)*δ)
    (hDegree : 2*ε*(Fintype.card V:ℝ)+(t:ℝ) ≤ δ*(m:ℝ)) :
    ∃ A : I → Fin m ↪ V, ∀ i,
      let P := pullDirectedPair (A i) (A (s i)) (D i)
      IsCentredRegular P δ d ∧
      ∀ b x, |(pairSemidegree b P x:ℝ)-d*(m:ℝ)| ≤ δ*(m:ℝ) := by
  let endpoint (b : Bool) (i : I) := if b then i else s i
  have hBud : 4*ε*(Fintype.card V:ℝ) ≤ ((1:ℝ)/2)*(t:ℝ) := by linarith only [hBudget]
  obtain ⟨K,hK,hGood⟩ := exists_retained_good_copy_profiles endpoint D d ε (1/2) t hD
    hε hε₁ (by norm_num) hn hBud
  have hCard (i : I) : Fintype.card (K i) = m := by rw [Fintype.card_coe,hK]; omega
  let A (i : I) : Fin m ↪ V :=
    (Fintype.equivFinOfCardEq (hCard i)).symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hMem (i : I) (x : Fin m) : A i x ∈ K i :=
    ((Fintype.equivFinOfCardEq (hCard i)).symm x).property
  have hSingle (b : Bool) (i : I) :
      ((univ : Finset I).filter (fun j => endpoint b j = endpoint b i)) = {i} := by
    ext j
    cases b
    · simp [endpoint,s.injective.eq_iff]
    · simp [endpoint]
  refine ⟨A,fun i => ⟨centred_regular_pull_of_trim _ _ _ _ _ _ (hD i) hReg
    (by simpa only [Fintype.card_fin] using hLarge) (by simpa only [Fintype.card_fin] using hScale),?_⟩⟩
  intro b x
  have hOld :
      |(pairSemidegree b (D i) (A (endpoint b i) x):ℝ)-d*(Fintype.card V:ℝ)| ≤
        2*ε*(Fintype.card V:ℝ) := by
    have h := hGood b (endpoint b i) _ (hMem (endpoint b i) x)
    rw [hSingle] at h
    by_contra! hb
    have he : ({i} : Finset I).filter (fun j =>
        2*ε*(Fintype.card V:ℝ) < |(pairSemidegree b (D j) (A (endpoint b i) x):ℝ)-d*(Fintype.card V:ℝ)|) = {i} := by
      ext j
      simp only [mem_filter,mem_singleton]
      exact ⟨And.left,fun hij => ⟨hij,by subst j; exact hb⟩⟩
    rw [he] at h
    norm_num at h
  have hOld' :
      |(pairSemidegree b (D i) (if b then A i x else A (s i) x):ℝ)-d*(Fintype.card V:ℝ)| ≤
        2*ε*(Fintype.card V:ℝ) := by cases b <;> exact hOld
  have hSize : Fintype.card (Fin m) ≤ Fintype.card V := by simp only [Fintype.card_fin]; omega
  have hLoss : Fintype.card V - m = t := by omega
  have h := typical_semidegree_pull_of_trim (A i) (A (s i)) (D i) b x d (2*ε) δ hd hd₁ hSize hOld'
    (by simpa only [Fintype.card_fin,hLoss] using hDegree)
  simpa only [Fintype.card_fin] using h

/-- Re-encode a regular pair and its two degree profiles on the
physical image of its two embeddings. -/
theorem lift_isSuperregularPair (a b : I ↪ V) (D : Digraph I) (ε d : ℝ)
    (hD : IsCentredRegular D ε d)
    (hProfile : ∀ s x, |(pairSemidegree s D x:ℝ)-d*(Fintype.card I:ℝ)| ≤ ε*(Fintype.card I:ℝ)) :
    IsSuperregularPair (liftDirectedPair a b D) ε d (univ.map a) (univ.map b) := by
  let H := liftDirectedPair a b D
  have hPull : pullDirectedPair a b H = D := by
    ext x y
    exact liftDirectedPair_adj a b D x y
  have hDensity (X Y : Finset I) : density H (X.map a) (Y.map b) = density D X Y := by
    rw [←density_pullDirectedPair,hPull]
  have hMap (e : I ↪ V) (A : Finset V) (hA : A ⊆ univ.map e) :
      ∃ X : Finset I, X.map e = A := by
    refine ⟨univ.filter (fun x => e x ∈ A),?_⟩
    ext v
    constructor
    · rintro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp h
      exact (mem_filter.mp hx).2
    · intro h
      obtain ⟨x,hx,rfl⟩ := mem_map.mp (hA h)
      exact mem_map.mpr ⟨x,mem_filter.mpr ⟨hx,h⟩,rfl⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro X hX Y hY hLX hLY
    obtain ⟨X,rfl⟩ := hMap a X hX
    obtain ⟨Y,rfl⟩ := hMap b Y hY
    rw [hDensity,hDensity]
    simp only [card_map] at hLX hLY
    exact hD.1 X (subset_univ _) Y (subset_univ _) hLX hLY
  · rw [hDensity]
    exact hD.2
  · intro x hx
    obtain ⟨p,_,rfl⟩ := mem_map.mp hx
    change |profileCount (univ.map b) (outProfile H (a p))-d*((univ.map b : Finset V).card:ℝ)| ≤ _
    have hSub : outProfile H (a p) ⊆ univ.map b := by
      intro y hy
      obtain ⟨x,z,_,rfl,_⟩ := (mem_filter.mp hy).2
      exact mem_map.mpr ⟨z,mem_univ _,rfl⟩
    have hEq : profileCount (univ.map b) (outProfile H (a p)) = (outDegree H (a p):ℝ) := by
      rw [profileCount,inter_eq_right.mpr hSub]
      rfl
    rw [hEq,card_map,card_univ]
    have he : outDegree H (a p) = outDegree D p := lift_pair_semidegree a b D true p
    rw [he]
    exact hProfile true p
  · intro y hy
    obtain ⟨p,_,rfl⟩ := mem_map.mp hy
    change |profileCount (univ.map a) (inProfile H (b p))-d*((univ.map a : Finset V).card:ℝ)| ≤ _
    have hSub : inProfile H (b p) ⊆ univ.map a := by
      intro x hx
      obtain ⟨z,y,rfl,_,_⟩ := (mem_filter.mp hx).2
      exact mem_map.mpr ⟨z,mem_univ _,rfl⟩
    have hEq : profileCount (univ.map a) (inProfile H (b p)) = (inDegree H (b p):ℝ) := by
      rw [profileCount,inter_eq_right.mpr hSub]
      rfl
    rw [hEq,card_map,card_univ]
    have he : inDegree H (b p) = inDegree D p := lift_pair_semidegree a b D false p
    rw [he]
    exact hProfile false p

set_option maxHeartbeats 1200000 in
/-- Realize the factor-specific adapted cells of §5.3 on the original
vertices. All of their successor pairs retain disjoint physical arcs. -/
theorem exists_adapted_primary_factors_with_incidence_bound
    (η σ δ : ℝ) (b : ℕ)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/4)
    (hb : 0 < b) (hGood : 8*η ≤ σ) (hTrim : 4*(η+σ) ≤ δ) (hδ₁ : δ ≤ 1) :
    ∃ N : ℕ, ∀ {V I : Type*} [Fintype V] [Fintype I]
      {H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {m₀ : ℕ} {β γ a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc),
      N ≤ B.size → 0 ≤ (1-5*γ)*β → (1-5*γ)*β ≤ 1 →
      ∀ {k : ℕ} (F : Fin k → Equiv.Perm I) (pick : Fin k → I → ReducedCopy M),
        (∀ t i, (pick t i).1 = (i,F t i)) →
        Function.Injective (fun q : Fin k × I => pick q.1 q.2) →
        ∀ (fillCap : ℕ) (badBound : ℝ), 0 < fillCap → 4*σ*(k:ℝ) ≤ (fillCap:ℝ) →
        B.MainCopyIncidenceBound badBound →
        ∃ m : ℕ, 0 < m ∧ b ∣ m ∧ m ≤ B.size ∧ B.size ≤ 2*m ∧
          ((B.size-m:ℕ):ℝ) ≤ 2*σ*(B.size:ℝ) ∧
          ∃ g : Fin k → V → Option I, ∃ E : Fin k → I → Digraph V,
            (∀ t i, (cluster (g t) i).card = m ∧ cluster (g t) i ⊆ cluster B.partition i) ∧
            (∀ t, (exceptional (g t)).card =
              (exceptional B.partition).card+(B.size-m)*Fintype.card I) ∧
            (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*σ)*(Fintype.card V:ℝ)) ∧
            (∀ t i, E t i ≤ H) ∧
            (∀ t i s j, (t,i) ≠ (s,j) → Disjoint (E t i) (E s j)) ∧
            (∀ t i j,
              let src := fun e : ReducedCopy M => (B.kept e.1.1).trans (B.base e.1.1)
              let dst := fun e : ReducedCopy M => (B.kept e.1.2).trans (B.base e.1.2)
              Disjoint (E t i) (directedPairUnion src dst (B.thin j))) ∧
            (∀ t i, IsSuperregularPair (E t i) δ ((1-5*γ)*β)
              (cluster (g t) i) (cluster (g t) (F t i))) ∧
            ∀ x, B.partition x ≠ none →
              (((univ : Finset (Fin k)).filter (fun t => g t x = none)).card:ℝ) ≤ 2*badBound+fillCap := by
  obtain ⟨N,hN⟩ := exists_primary_copy_trim σ b hσ hσ₁ hb
  refine ⟨N,?_⟩
  intro V I _ _ H f M m₀ β γ a exc P hSize hd hd₁ k F pick hPick hInj fillCap badBound hCap hCapSize hBadMain
  obtain ⟨lost,m,hSizeEq,hDiv,hHalf,hLossLo,hLossHi⟩ := hN P.size hSize
  have hmPos : 0 < m := by have := P.size_pos; omega
  have hLoss : P.size-m = lost := by omega
  have hHalfR : (P.size:ℝ) ≤ 2*(m:ℝ) := by exact_mod_cast hHalf
  have hM : (0:ℝ) ≤ P.size := Nat.cast_nonneg _
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg _
  have hDel : 8*η*(P.size:ℝ) ≤ (lost:ℝ) :=
    (mul_le_mul_of_nonneg_right hGood hM).trans hLossLo
  have hDegree : 2*η*(P.size:ℝ)+(lost:ℝ) ≤ δ*(m:ℝ) := by
    calc
      _ ≤ 2*(η+σ)*(P.size:ℝ) := by linarith only [hLossHi]
      _ ≤ 2*(η+σ)*(2*(m:ℝ)) := mul_le_mul_of_nonneg_left hHalfR (by positivity)
      _ = (4*(η+σ))*(m:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hTrim hm
  have hReg : 2*η ≤ δ := by linarith only [hTrim,hσ,hη]
  have hScale : (P.size:ℝ)*η ≤ (m:ℝ)*δ := by
    have h1 := mul_le_mul_of_nonneg_right hHalfR hη.le
    have h2 := mul_le_mul_of_nonneg_right hReg hm
    linarith only [h1,h2]
  have hLarge : (P.size:ℝ)*η ≤ (m:ℝ) :=
    hScale.trans (mul_le_of_le_one_right hm hδ₁)
  have hRoom : k*lost ≤ fillCap*m := by
    have hSizeR : (lost:ℝ) ≤ 4*σ*(m:ℝ) := by
      calc
        _ ≤ 2*σ*(P.size:ℝ) := hLossHi
        _ ≤ 2*σ*(2*(m:ℝ)) := mul_le_mul_of_nonneg_left hHalfR (by positivity)
        _ = _ := by ring
    have h := mul_le_mul_of_nonneg_left hSizeR (Nat.cast_nonneg k : (0:ℝ) ≤ _)
    have hc := mul_le_mul_of_nonneg_right hCapSize hm
    exact_mod_cast (show (k:ℝ)*(lost:ℝ) ≤ (fillCap:ℝ)*(m:ℝ) by nlinarith only [h,hc])
  obtain ⟨A,hA,hCount⟩ := exists_controlled_two_sided_factor_trim F (fun t i => P.main (pick t i))
    lost m fillCap η δ ((1-5*γ)*β) (fun t i => P.main_regular (pick t i)) hη hη₁
    (by simpa using P.size_pos) hd hd₁ (by simpa using hSizeEq)
    (by
      have hNonneg : 0 ≤ η*(P.size:ℝ) := by positivity
      simpa using (show 4*η*(P.size:ℝ) ≤ (lost:ℝ) by linarith only [hNonneg,hDel]))
    hReg (by simpa using hLarge) (by simpa using hScale) (by simpa using hDegree) hCap
    (by simpa using hRoom)
  let coords (t : Fin k) (i : I) := (A t i).trans ((P.kept i).trans (P.base i))
  let cells (t : Fin k) (i : I) := (univ : Finset (Fin m)).map (coords t i)
  have hCells (t : Fin k) (i : I) : cells t i ⊆ cluster P.partition i := by
    rw [←P.retained_cells i]
    intro x hx
    obtain ⟨y,_,rfl⟩ := mem_map.mp hx
    exact mem_map.mpr ⟨A t i y,mem_univ _,rfl⟩
  let g (t : Fin k) := equalize P.partition (cells t)
  have hg (t : Fin k) (i : I) : cluster (g t) i = cells t i :=
    cluster_equalize _ _ (hCells t) i
  have hgCard (t : Fin k) (i : I) : (cluster (g t) i).card = m := by
    simp only [hg,cells,card_map,card_univ,Fintype.card_fin]
  have hOld := order_eq P.partition P.size (fun i => by
    rw [←P.retained_cells i,card_map,card_univ,Fintype.card_fin])
  have hExc (t : Fin k) : (exceptional (g t)).card =
      (exceptional P.partition).card+(P.size-m)*Fintype.card I := by
    have hOld' := hOld
    have hNew := order_eq (g t) m (hgCard t)
    rw [←hSizeEq,add_mul] at hOld'
    rw [hLoss]
    omega
  have hExcBound (t : Fin k) : ((exceptional (g t)).card:ℝ) ≤ (exc+2*σ)*(Fintype.card V:ℝ) := by
    have hOldLe : (P.size:ℝ)*(Fintype.card I:ℝ) ≤ (Fintype.card V:ℝ) := by
      exact_mod_cast (show P.size*Fintype.card I ≤ Fintype.card V by omega)
    have hScale := mul_le_mul_of_nonneg_right hLossHi (Nat.cast_nonneg (Fintype.card I) : (0:ℝ) ≤ _)
    rw [mul_assoc] at hScale
    have hAdd := hScale.trans (mul_le_mul_of_nonneg_left hOldLe (by positivity))
    rw [hExc t,Nat.cast_add,Nat.cast_mul,hLoss,add_mul]
    exact add_le_add P.exceptional_le hAdd
  let Q (t : Fin k) (i : I) :=
    pullDirectedPair (A t i) (A t (F t i)) (P.main (pick t i))
  let E (t : Fin k) (i : I) := liftDirectedPair (coords t i) (coords t (F t i)) (Q t i)
  have hMono (t : Fin k) (i : I) :
      let e := pick t i
      E t i ≤ liftDirectedPair ((P.kept e.1.1).trans (P.base e.1.1))
        ((P.kept e.1.2).trans (P.base e.1.2)) (P.main e) := by
    intro e
    have hSrc : e.1.1 = i := congrArg Prod.fst (hPick t i)
    have hDst : e.1.2 = F t i := congrArg Prod.snd (hPick t i)
    rw [hSrc,hDst]
    rintro x y ⟨p,q,hx,hy,he⟩
    exact ⟨A t i p,A t (F t i) q,hx,hy,he⟩
  refine ⟨m,hmPos,hDiv,by omega,hHalf,by simpa only [hLoss] using hLossHi,g,E,
    fun t i => ⟨hgCard t i,(hg t i).symm ▸ hCells t i⟩,hExc,hExcBound,?_,?_,?_,?_,?_⟩
  · intro t i
    exact (hMono t i).trans ((P.lift_main_le (pick t i)).trans (P.copy_le (pick t i)))
  · intro t i s j hne
    have hPickNe : pick t i ≠ pick s j := fun h => hne (hInj h)
    exact (P.lift_main_disjoint _ _ hPickNe).mono (hMono t i) (hMono s j)
  · intro t i j
    have hSub : E t i ≤ directedPairUnion
        (fun e : ReducedCopy M => (P.kept e.1.1).trans (P.base e.1.1))
        (fun e : ReducedCopy M => (P.kept e.1.2).trans (P.base e.1.2)) P.main :=
      fun x y h => ⟨pick t i,hMono t i h⟩
    exact (P.main_thin_disjoint j).symm.mono hSub le_rfl
  · intro t i
    rw [hg,hg]
    exact lift_isSuperregularPair _ _ (Q t i) δ _ (hA t i).1
      (fun b x => by simpa only [Fintype.card_fin] using (hA t i).2 b x)
  · intro x hx
    cases hTag : P.partition x with
    | none => exact (hx hTag).elim
    | some i =>
      have hPhys := (mem_cluster P.partition i x).mpr hTag
      rw [←P.retained_cells i] at hPhys
      obtain ⟨w,_,rfl⟩ := mem_map.mp hPhys
      let emb := (P.kept i).trans (P.base i)
      have hDelete (t : Fin k) : g t (emb w) = none ↔ w ∉ univ.map (A t i) := by
        have hMem : emb w ∈ cells t i ↔ w ∈ univ.map (A t i) := by
          simp only [cells,coords,mem_map,mem_univ,true_and]
          exact ⟨fun ⟨z,hz⟩ => ⟨z,emb.injective hz⟩,fun ⟨z,hz⟩ => ⟨z,congrArg emb hz⟩⟩
        change equalize P.partition (cells t) (emb w) = none ↔ _
        rw [equalize,show P.partition (emb w) = some i from hTag]
        simpa only [hMem,ite_eq_right_iff,Option.some_ne_none,imp_false]
      have hFilter : ((univ : Finset (Fin k)).filter (fun t => g t (emb w) = none)) =
          univ.filter (fun t => w ∉ univ.map (A t i)) := by
        ext t
        simpa only [mem_filter,mem_univ,true_and] using hDelete t
      rw [hFilter]
      have hAtypical := atypical_primary_types_le_incident_copies F
        (fun e : ReducedCopy M => e.1.1) (fun e => e.1.2) P.main pick
        (fun t j => congrArg Prod.fst (hPick t j)) (fun t j => congrArg Prod.snd (hPick t j))
        hInj η ((1-5*γ)*β) i w
      have hCountR : _ ≤ _ := (Nat.cast_le (α := ℝ)).mpr (hCount i w)
      have hAtypicalR : _ ≤ _ := (Nat.cast_le (α := ℝ)).mpr hAtypical
      push_cast at hCountR hAtypicalR
      have hBoth (s : Bool) : ((atypicalIncidentCopies (fun e : ReducedCopy M => e.1.1)
          (fun e => e.1.2) P.main η ((1-5*γ)*β) s i w).card:ℝ) ≤ badBound := hBadMain s i w
      have hSum := add_le_add_right (hAtypicalR.trans (add_le_add (hBoth true) (hBoth false))) (fillCap:ℝ)
      rw [add_comm (fillCap:ℝ) _,add_comm (fillCap:ℝ) _,←two_mul] at hSum
      have hAll := hCountR.trans hSum
      convert hAll using 1 <;> congr 2 <;> ext t <;> simp only [mem_filter]


/-- Factor-specific adapted cells of the common divisible size. -/
theorem exists_adapted_primary_factors_with_size
    (η σ δ : ℝ) (b : ℕ)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/4)
    (hb : 0 < b) (hGood : 8*η ≤ σ) (hTrim : 4*(η+σ) ≤ δ) (hδ₁ : δ ≤ 1) :
    ∃ N : ℕ, ∀ {V I : Type*} [Fintype V] [Fintype I]
      {H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {m₀ : ℕ} {β γ a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc),
      N ≤ B.size → 0 ≤ (1-5*γ)*β → (1-5*γ)*β ≤ 1 →
      ∀ {k : ℕ} (F : Fin k → Equiv.Perm I) (pick : Fin k → I → ReducedCopy M),
        (∀ t i, (pick t i).1 = (i,F t i)) →
        Function.Injective (fun q : Fin k × I => pick q.1 q.2) →
        ∃ m : ℕ, 0 < m ∧ b ∣ m ∧ m ≤ B.size ∧ B.size ≤ 2*m ∧
          ((B.size-m:ℕ):ℝ) ≤ 2*σ*(B.size:ℝ) ∧
          ∃ g : Fin k → V → Option I, ∃ E : Fin k → I → Digraph V,
            (∀ t i, (cluster (g t) i).card = m ∧ cluster (g t) i ⊆ cluster B.partition i) ∧
            (∀ t, (exceptional (g t)).card =
              (exceptional B.partition).card+(B.size-m)*Fintype.card I) ∧
            (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*σ)*(Fintype.card V:ℝ)) ∧
            (∀ t i, E t i ≤ H) ∧
            (∀ t i s j, (t,i) ≠ (s,j) → Disjoint (E t i) (E s j)) ∧
            (∀ t i j,
              let src := fun e : ReducedCopy M => (B.kept e.1.1).trans (B.base e.1.1)
              let dst := fun e : ReducedCopy M => (B.kept e.1.2).trans (B.base e.1.2)
              Disjoint (E t i) (directedPairUnion src dst (B.thin j))) ∧
            ∀ t i, IsSuperregularPair (E t i) δ ((1-5*γ)*β)
              (cluster (g t) i) (cluster (g t) (F t i)) := by
  obtain ⟨N,hN⟩ := exists_adapted_primary_factors_with_incidence_bound η σ δ b
    hη hη₁ hσ hσ₁ hb hGood hTrim hδ₁
  refine ⟨N,?_⟩
  intro V I _ _ H f M m₀ β γ a exc B hSize hd hd₁ k F pick hPick hInj
  let cap := max 1 k
  have hCap : 0 < cap := (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)
  have hCapSize : 4*σ*(k:ℝ) ≤ (cap:ℝ) :=
    (mul_le_of_le_one_left (Nat.cast_nonneg k) (by linarith only [hσ₁])).trans
      (by exact_mod_cast (le_max_right 1 k))
  have hBadMain : B.MainCopyIncidenceBound (Fintype.card (ReducedCopy M):ℝ) := by
    intro s i x
    exact_mod_cast card_le_univ _
  obtain ⟨m,hm,hDiv,hLe,hHalf,hLoss,g,E,hCells,hExc,hBound,hSub,hDis,hThin,hReg,_⟩ :=
    hN B hSize hd hd₁ F pick hPick hInj cap _ hCap hCapSize hBadMain
  exact ⟨m,hm,hDiv,hLe,hHalf,hLoss,g,E,hCells,hExc,hBound,hSub,hDis,hThin,hReg⟩


/-- Factor-specific adapted cells and their pairwise disjoint superregular pairs. -/
theorem exists_adapted_primary_factors
    (η σ δ : ℝ) (b : ℕ)
    (hη : 0 < η) (hη₁ : η ≤ 1) (hσ : 0 < σ) (hσ₁ : σ ≤ 1/4)
    (hb : 0 < b) (hGood : 8*η ≤ σ) (hTrim : 4*(η+σ) ≤ δ) (hδ₁ : δ ≤ 1) :
    ∃ N : ℕ, ∀ {V I : Type*} [Fintype V] [Fintype I]
      {H : Digraph V} {f : V → Option I} {M : I → I → ℕ}
      {m₀ : ℕ} {β γ a exc : ℝ}
      (B : OsthusStadenPrimaryReserveData H f M m₀ b β γ η a exc),
      N ≤ B.size → 0 ≤ (1-5*γ)*β → (1-5*γ)*β ≤ 1 →
      ∀ {k : ℕ} (F : Fin k → Equiv.Perm I) (pick : Fin k → I → ReducedCopy M),
        (∀ t i, (pick t i).1 = (i,F t i)) →
        Function.Injective (fun q : Fin k × I => pick q.1 q.2) →
        ∃ m : ℕ, 0 < m ∧ b ∣ m ∧ B.size ≤ 2*m ∧
          ((B.size-m:ℕ):ℝ) ≤ 2*σ*(B.size:ℝ) ∧
          ∃ g : Fin k → V → Option I, ∃ E : Fin k → I → Digraph V,
            (∀ t i, (cluster (g t) i).card = m ∧ cluster (g t) i ⊆ cluster B.partition i) ∧
            (∀ t, (exceptional (g t)).card =
              (exceptional B.partition).card+(B.size-m)*Fintype.card I) ∧
            (∀ t, ((exceptional (g t)).card:ℝ) ≤ (exc+2*σ)*(Fintype.card V:ℝ)) ∧
            (∀ t i, E t i ≤ H) ∧
            (∀ t i s j, (t,i) ≠ (s,j) → Disjoint (E t i) (E s j)) ∧
            (∀ t i j,
              let src := fun e : ReducedCopy M => (B.kept e.1.1).trans (B.base e.1.1)
              let dst := fun e : ReducedCopy M => (B.kept e.1.2).trans (B.base e.1.2)
              Disjoint (E t i) (directedPairUnion src dst (B.thin j))) ∧
            ∀ t i, IsSuperregularPair (E t i) δ ((1-5*γ)*β)
              (cluster (g t) i) (cluster (g t) (F t i)) := by
  obtain ⟨N,hN⟩ := exists_adapted_primary_factors_with_size η σ δ b
    hη hη₁ hσ hσ₁ hb hGood hTrim hδ₁
  refine ⟨N,?_⟩
  intro V I _ _ H f M m₀ β γ a exc B hSize hd hd₁ k F pick hPick hInj
  obtain ⟨m,hm,hDiv,_,hHalf,hLoss,g,E,hCells,hExc,hBound,hSub,hDis,hThin,hReg⟩ :=
    hN B hSize hd hd₁ F pick hPick hInj
  exact ⟨m,hm,hDiv,hHalf,hLoss,g,E,hCells,hExc,hBound,hSub,hDis,hThin,hReg⟩

end OverfullWork.DirectedRegularPairs
