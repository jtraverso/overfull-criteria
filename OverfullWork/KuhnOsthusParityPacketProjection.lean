module

public import OverfullWork.KuhnOsthusOriginalIntervalProjection
public import OverfullWork.KuhnOsthusLemma105
public import OverfullWork.KuhnOsthusWindingExceptionalDegrees
public import OverfullWork.KuhnOsthusParityReserveDegrees

@[expose] public section


/-! A seven-interval exceptional factor produced by Lemma 7.6 retains
exactly the seven projected systems used by Lemma 10.5. -/
namespace OverfullWork.DirectedRobustExpansion

open Finset Function DirectedRegularPairs
open scoped Classical

/-- Read the half-open block and its terminal cell in cyclic cluster
coordinates, including the wrap of the final interval. -/
theorem winding_closed_interval_cells {V : Type*} [DecidableEq V] {l q : ℕ}
    (X : Fin (l*q) → Finset V) (hk : 0 < l*q) (hq : 0 < q) (i : Fin l) :
    let A := cyclicCluster X hk
    let U := (univ : Finset (Fin q)).biUnion (fun j => X (intervalPosition i j))
    let S (j : Fin l) := X (intervalPosition j ⟨0,hq⟩)
    U ∪ S (finRotate l i) = clusterIntervalVertices A (q*i.val) (q*(i.val+1)) ∧
      S i = A (q*i.val) ∧ S (finRotate l i) = A (q*(i.val+1)) := by
  intro A U S
  have hPos (j : Fin q) : X (intervalPosition i j) = A (q*i.val+j.val) := by
    have h := (intervalPosition i j).isLt
    rw [intervalPosition_val,Nat.add_comm] at h
    apply congrArg X
    apply Fin.ext
    change (intervalPosition i j).val = (q*i.val+j.val)%(l*q)
    rw [Nat.mod_eq_of_lt h,intervalPosition_val,Nat.add_comm]
  have hS : S i = A (q*i.val) := by simpa only [Nat.add_zero] using hPos ⟨0,hq⟩
  have hT : S (finRotate l i) = A (q*(i.val+1)) := by
    apply congrArg X
    apply Fin.ext
    change (intervalPosition (finRotate l i) ⟨0,hq⟩).val = (q*(i.val+1))%(l*q)
    rw [intervalPosition_val,finRotate_val_modulo,Nat.mul_comm l q,Nat.mul_mod_mul_left]
    exact Nat.zero_add _
  refine ⟨?_,hS,hT⟩
  ext v
  simp only [U,mem_union,mem_biUnion,mem_univ,true_and,mem_clusterIntervalVertices]
  rw [hT,Nat.mul_add,Nat.mul_one]
  constructor
  · rintro (⟨j,hj⟩ | h)
    · exact ⟨q*i.val+j.val,by omega,by have := j.isLt; omega,hPos j ▸ hj⟩
    · exact ⟨q*i.val+q,by omega,le_rfl,h⟩
  · rintro ⟨j,hj,hj',hv⟩
    by_cases h : j = q*i.val+q
    · exact .inr (h ▸ hv)
    · let t : Fin q := ⟨j-q*i.val,by omega⟩
      have ht : q*i.val+t.val = j := by dsimp [t]; omega
      exact .inl ⟨t,(hPos t).symm ▸ (ht.symm ▸ hv)⟩

/-- The seven complete original intervals give the actual parity
packet. Its original arc union is the pullback of the supplied factor. -/
theorem exists_parity_packet_of_original_intervals {W : Type*} [Fintype W]
    {G : Digraph W} (Z : Finset W) [Nonempty ↥Zᶜ] {q : ℕ}
    (X : Fin (14*q) → Finset ↥Zᶜ) (hq : 0 < q) :
    let A := cyclicCluster X (by omega)
    let a : ↥Zᶜ ↪ W := Embedding.subtype _
    let e := (exceptionalCoordinates Z).toEmbedding
    ∀ (F : ∀ i : Fin 7, OriginalInterval G Z
      ((clusterIntervalVertices A (2*q*i.val) (2*q*(i.val+1))).map a)
      ((A (2*q*i.val)).map a) ((A (2*q*(i.val+1))).map a)),
    ∃ E : ParityExceptionalPacket (pullDirectedPair e e G) A q,
      E.original = pullDirectedPair e e (⨆ i, (F i).digraph) := by
  intro A a e F
  have get (i : Fin 7) (b c : ℕ) (hb : 2*q*i.val = b) (hc : 2*q*(i.val+1) = c) :
      ∃ (P : IntervalPathCover ⊤ (clusterIntervalVertices A b c) (A b) (A c))
        (K : ProjectedExceptionalArcs (pullDirectedPair e e G) P.digraph (id : ↥Z → ↥Z)),
        K.original = pullDirectedPair e e (F i).digraph := by
    subst b
    subst c
    obtain ⟨H,P,K,hK⟩ := (F i).exists_projected_exceptional_arcs
    exact ⟨P.rehost le_top,K,hK⟩
  obtain ⟨P₁,K₁,h₁⟩ := get 0 0 (2*q) (by simp) (by simp)
  obtain ⟨P₂,K₂,h₂⟩ := get 1 (2*q) (4*q) (by simp) (by change 2*q*2 = 4*q; omega)
  obtain ⟨P₃,K₃,h₃⟩ := get 2 (4*q) (6*q) (by change 2*q*2 = 4*q; omega)
    (by change 2*q*3 = 6*q; omega)
  obtain ⟨P₄,K₄,h₄⟩ := get 3 (6*q) (8*q) (by change 2*q*3 = 6*q; omega)
    (by change 2*q*4 = 8*q; omega)
  obtain ⟨P₅,K₅,h₅⟩ := get 4 (8*q) (10*q) (by change 2*q*4 = 8*q; omega)
    (by change 2*q*5 = 10*q; omega)
  obtain ⟨P₆,K₆,h₆⟩ := get 5 (10*q) (12*q) (by change 2*q*5 = 10*q; omega)
    (by change 2*q*6 = 12*q; omega)
  obtain ⟨P₇,K₇,h₇⟩ := get 6 (12*q) (14*q) (by change 2*q*6 = 12*q; omega)
    (by change 2*q*7 = 14*q; omega)
  let E : ParityExceptionalPacket (pullDirectedPair e e G) A q :=
    ⟨⊤,⟨P₂,P₃,P₄,P₅⟩,P₁,P₆,P₇,K₁,K₂,K₃,K₄,K₅,K₆,K₇⟩
  refine ⟨E,?_⟩
  have hE : E.original = (((K₃.original ⊔ K₅.original) ⊔ K₄.original) ⊔ K₂.original) ⊔
      (K₆.original ⊔ K₇.original ⊔ K₁.original) := rfl
  rw [hE,h₁,h₂,h₃,h₄,h₅,h₆,h₇]
  ext x y
  change (((((F 2).digraph.Adj _ _ ∨ (F 4).digraph.Adj _ _) ∨ (F 3).digraph.Adj _ _) ∨
    (F 1).digraph.Adj _ _) ∨ (((F 5).digraph.Adj _ _ ∨ (F 6).digraph.Adj _ _) ∨
    (F 0).digraph.Adj _ _)) ↔ (⨆ i, (F i).digraph).Adj (e x) (e y)
  rw [Digraph.iSup_adj]
  constructor
  · rintro ((((h | h) | h) | h) | ((h | h) | h))
    · exact ⟨2,h⟩
    · exact ⟨4,h⟩
    · exact ⟨3,h⟩
    · exact ⟨1,h⟩
    · exact ⟨5,h⟩
    · exact ⟨6,h⟩
    · exact ⟨0,h⟩
  · rintro ⟨i,h⟩
    fin_cases i
    · exact .inr (.inr h)
    · exact .inl (.inr h)
    · exact .inl (.inl (.inl (.inl h)))
    · exact .inl (.inl (.inr h))
    · exact .inl (.inl (.inl (.inr h)))
    · exact .inr (.inl (.inl h))
    · exact .inr (.inl (.inr h))

/-- Put one already constructed, unrefined seven-interval factor
into the parity coordinates. Its physical arcs are preserved. -/
theorem project_wound_intervals_to_parity_packet {W : Type*} [Fintype W]
    {G : Digraph W} (Z : Finset W) [Nonempty ↥Zᶜ] {q : ℕ}
    (X : Fin (14*q) → Finset ↥Zᶜ) (hq : 0 < q) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let emb : ↥Zᶜ ↪ W := Embedding.subtype _
    let q' := 2*q
    let hq' : 0 < q' := by dsimp [q']; omega
    let idx : Fin (7*q') ≃ Fin (14*q) := finCongr (by dsimp [q']; omega)
    let P (i : Fin (7*q')) := (X (idx i)).map emb
    let U (j : Fin 1 × Fin 7) :=
      (univ : Finset (Fin q')).biUnion (fun i => P (intervalPosition j.2 i))
    let S (j : Fin 1 × Fin 7) := P (intervalPosition j.2 ⟨0,hq'⟩)
    let next := (Equiv.refl (Fin 1)).prodCongr (finRotate 7)
    let coord := (exceptionalCoordinates Z).toEmbedding
    let D := pullDirectedPair coord coord G
    ∀ F : ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
      ∃ E : ParityExceptionalPacket D A q,
        E.original = pullDirectedPair coord coord (⨆ j, (F j).digraph) := by
  intro hk A emb q' hq' idx P U' S' next coord D F
  let Y (i : Fin (7*q')) := X (idx i)
  have hk' : 0 < 7*q' := Nat.mul_pos (by decide) hq'
  have hA (i : ℕ) : cyclicCluster Y hk' i = A i := by
    apply congrArg X
    apply Fin.ext
    change i%(7*q') = i%(14*q)
    congr 1
    dsimp [q']
    omega
  let B (i : Fin 7) := (univ : Finset (Fin q')).biUnion (fun j => Y (intervalPosition i j))
  let S (i : Fin 7) := Y (intervalPosition i ⟨0,hq'⟩)
  have hCells (i : Fin 7) :
      B i ∪ S (finRotate 7 i) = clusterIntervalVertices A (q'*i.val) (q'*(i.val+1)) ∧
        S i = A (q'*i.val) ∧ S (finRotate 7 i) = A (q'*(i.val+1)) := by
    rw [← show cyclicCluster Y hk' = A from funext hA]
    simpa only [B,S] using winding_closed_interval_cells Y hk' hq' i
  have hMap (i : Fin 7) :
      ((univ : Finset (Fin q')).biUnion (fun j => P (intervalPosition i j))) = (B i).map emb := by
    ext x
    simp only [B,P,Y,mem_biUnion,mem_map,mem_univ,true_and]
    exact ⟨fun ⟨j,v,hv,he⟩ => ⟨v,⟨j,hv⟩,he⟩,fun ⟨v,⟨j,hv⟩,he⟩ => ⟨j,v,hv,he⟩⟩
  have hSupport (i : Fin 7) :
      (((univ : Finset (Fin q')).biUnion (fun j => P (intervalPosition i j))) ∪
        (S (finRotate 7 i)).map emb) =
      (clusterIntervalVertices A (q'*i.val) (q'*(i.val+1))).map emb := by
    rw [hMap,← map_union]
    exact congrArg (Finset.map emb) (hCells i).1
  let I (i : Fin 7) : OriginalInterval G Z
      ((clusterIntervalVertices A (2*q*i.val) (2*q*(i.val+1))).map emb)
      ((A (2*q*i.val)).map emb) ((A (2*q*(i.val+1))).map emb) :=
    (F (0,i)).castSets (hSupport i) (congrArg (Finset.map emb) (hCells i).2.1)
      (congrArg (Finset.map emb) (hCells i).2.2)
  have hI (i : Fin 7) : (I i).digraph = (F (0,i)).digraph :=
    OriginalInterval.castSets_digraph _ _ _ _
  obtain ⟨E,hE⟩ := exists_parity_packet_of_original_intervals Z X hq I
  refine ⟨E,hE.trans ?_⟩
  ext x y
  change (⨆ i, (I i).digraph).Adj (coord x) (coord y) ↔ (⨆ j, (F j).digraph).Adj (coord x) (coord y)
  simp only [Digraph.iSup_adj,hI]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨(0,i),hi⟩
  · rintro ⟨⟨i,j⟩,hj⟩
    have he : i = 0 := Subsingleton.elim _ _
    subst i
    exact ⟨j,hj⟩

/-- Transfer a whole family to the parity host. Both separation and
the exact degree accounting come from the same original arcs. -/
theorem project_wound_interval_family_to_parity_packets {W : Type*} [Fintype W]
    {G : Digraph W} (Z : Finset W) [Nonempty ↥Zᶜ] {q r : ℕ}
    (X : Fin (14*q) → Finset ↥Zᶜ) (hq : 0 < q) :
    let hk : 0 < 14*q := by omega
    let A := cyclicCluster X hk
    let emb : ↥Zᶜ ↪ W := Embedding.subtype _
    let q' := 2*q
    let hq' : 0 < q' := by dsimp [q']; omega
    let idx : Fin (7*q') ≃ Fin (14*q) := finCongr (by dsimp [q']; omega)
    let P (i : Fin (7*q')) := (X (idx i)).map emb
    let U (j : Fin 1 × Fin 7) :=
      (univ : Finset (Fin q')).biUnion (fun i => P (intervalPosition j.2 i))
    let S (j : Fin 1 × Fin 7) := P (intervalPosition j.2 ⟨0,hq'⟩)
    let next := (Equiv.refl (Fin 1)).prodCongr (finRotate 7)
    let coord := (exceptionalCoordinates Z).toEmbedding
    let D := pullDirectedPair coord coord G
    ∀ F : Fin r → ∀ j, OriginalInterval G Z (U j ∪ S (next j)) (S j) (S (next j)),
      let C (i : Fin r) := ⨆ j, (F i j).digraph
      Pairwise (fun i j => Disjoint (C i) (C j)) →
      (∀ v, let d := if v ∈ Z then 7*r else r
        inDegree (⨆ i, C i) v = d ∧ outDegree (⨆ i, C i) v = d) →
      ∃ E : Fin r → ParityExceptionalPacket D A q,
        (∀ i, (E i).original = pullDirectedPair coord coord (C i)) ∧
        Pairwise (fun i j => Disjoint (E i).original (E j).original) ∧
        ∀ v : ↥Zᶜ ⊕ ↥Z, let k := match v with | .inl _ => r | .inr _ => 7*r
          inDegree (⨆ i, (E i).original) v = k ∧ outDegree (⨆ i, (E i).original) v = k := by
  intro hk A emb q' hq' idx P U' S' next coord D F C hApart hDegree
  have hGet (t : Fin r) :
      ∃ E : ParityExceptionalPacket D A q,
        E.original = pullDirectedPair coord coord (⨆ j, (F t j).digraph) :=
    project_wound_intervals_to_parity_packet Z X hq (F t)
  choose E hE using hGet
  refine ⟨E,hE,?_,?_⟩
  · intro i j hij
    rw [hE i,hE j,disjoint_iff_inf_le]
    rintro x y ⟨hx,hy⟩
    exact (disjoint_iff_inf_le.mp (hApart hij)) ⟨hx,hy⟩
  · let U : Digraph W := ⨆ i, ⨆ j, (F i j).digraph
    let D₀ : Digraph (↥Zᶜ ⊕ ↥Z) := ⨆ i, (E i).original
    have he : liftDirectedPair coord coord D₀ = U := by
      ext x y
      obtain ⟨a,rfl⟩ := (exceptionalCoordinates Z).surjective x
      obtain ⟨b,rfl⟩ := (exceptionalCoordinates Z).surjective y
      change (liftDirectedPair coord coord D₀).Adj (coord a) (coord b) ↔ _
      rw [liftDirectedPair_adj]
      change (⨆ i, (E i).original).Adj a b ↔ (⨆ i, ⨆ j, (F i j).digraph).Adj (coord a) (coord b)
      rw [Digraph.iSup_adj, Digraph.iSup_adj]
      simp only [hE]
      rfl
    intro v k
    have hi : inDegree D₀ v = inDegree U (coord v) :=
      (lift_pair_semidegree coord coord D₀ false v).symm.trans (congrArg (inDegree · (coord v)) he)
    have ho : outDegree D₀ v = outDegree U (coord v) :=
      (lift_pair_semidegree coord coord D₀ true v).symm.trans (congrArg (outDegree · (coord v)) he)
    change inDegree D₀ v = k ∧ outDegree D₀ v = k
    rw [hi,ho]
    cases v with
    | inl v =>
      have hv := mem_compl.mp v.prop
      simpa only [coord,Function.Embedding.coe_subtype,Equiv.coe_toEmbedding,
        exceptionalCoordinates_inl,if_neg hv,k] using hDegree v.val
    | inr v =>
      simpa only [coord,Equiv.coe_toEmbedding,exceptionalCoordinates_inr,if_pos v.prop,
        k] using hDegree v.val

universe u

/-- The unrefined seven-interval case of Lemma 7.6 supplies a packet
family for Lemma 10.5, including its exact physical degrees. -/
theorem pack_parity_packets_with_exact_semidegrees
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {q : ℕ}
      (G : Digraph W) (Z : Finset W) [Nonempty ↥Zᶜ]
      (X : Fin (14*q) → Finset ↥Zᶜ) (hq : 0 < q)
      (R : Fin 7 → Digraph (Fin (2*q)))
      (m r e endpointCap endpointBudget routeCap : ℕ) (ε₀ a η : ℝ),
      let hk : 0 < 14*q := by omega
      let A := cyclicCluster X hk
      let emb : ↥Zᶜ ↪ W := Embedding.subtype _
      let q' := 2*q
      let idx : Fin (7*q') ≃ Fin (14*q) := finCongr (by dsimp [q']; omega)
      let P (i : Fin (7*q')) := (X (idx i)).map emb
      let E (j : Fin 7) := (windingEndpointPositions (⟨0,by dsimp [q']; omega⟩ : Fin q')).biUnion
        (fun i => P (intervalPosition j i))
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) →
      (∀ x, ∃ i, x ∈ X i) →
      (∀ i, (X i).card = m) →
      2*Z.card < endpointCap*(endpointBudget+1) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+7*r < inNeighbours G (E j) z) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+7*r < outTo G (E j) z) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      (∀ j i, ¬(R j).Adj i i) →
      (∀ j, ∃ radius growth cutoff budget : ℕ, IsRobustAt (R j) radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree (R j) i) ∧ (∀ i, cutoff ≤ inDegree (R j) i) ∧
        Z.card*(2*(q'/growth+3)) < routeCap*(budget+1)) →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      0 ≤ ε₀ → 0 ≤ a → 0 < η → η ≤ 1 →
      ε₀ ≤ η → 2*(ε₀+a) ≤ η → (r:ℝ) ≤ a*((m:ℝ)*η) →
      η < d-ε₀-a → (m:ℝ)*η ≤ (e:ℝ)+1 →
      0 < δ → δ ≤ 1 → 2*ε₀ ≤ d →
      2*(2*ε₀+a) ≤ δ → (r:ℝ) ≤ a*((m:ℝ)*δ) →
      (∀ j i h, (R j).Adj i h →
        IsUniform G ε₀ (P (intervalPosition j i)) (P (intervalPosition j h)) ∧
          d ≤ density G (P (intervalPosition j i)) (P (intervalPosition j h))) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (P i) (P (finRotate (7*q') i))) →
      let coord := (exceptionalCoordinates Z).toEmbedding
      let D := pullDirectedPair coord coord G
      ∃ F : Fin r → ParityExceptionalPacket D A q,
        Pairwise (fun i j => Disjoint (F i).original (F j).original) ∧
        ∀ v : ↥Zᶜ ⊕ ↥Z, let k := match v with | .inl _ => r | .inr _ => 7*r
          inDegree (⨆ i, (F i).original) v = k ∧ outDegree (⨆ i, (F i).original) v = k := by
  obtain ⟨N,hN⟩ := pack_original_intervals_on_winding_intervals.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro W _ q G Z _ X hq R m r e endpointCap endpointBudget routeCap ε₀ a η
    hk A emb q' idx P E loss hDis hCover hSize hBudget hIn hOut hRoom hLoop hRoutes hm hNmin
    hHall hPay hε₀ ha hη hη1 hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor hSTol hSLoss
    hReg hSup coord D
  have hq' : 0 < q' := by dsimp [q']; omega
  have hDSize (i : Fin (7*q')) : (P i).card = m := by
    change ((X (idx i)).map emb).card = m
    rw [card_map,hSize]
  have hDZ (i : Fin (7*q')) : Disjoint (P i) Z := by
    apply disjoint_left.mpr
    intro v hv hz
    obtain ⟨w,_,rfl⟩ := mem_map.mp hv
    exact (mem_compl.mp w.prop) hz
  have hDP (i j : Fin 1 × Fin (7*q')) (hne : i ≠ j) : Disjoint (P i.2) (P j.2) := by
    rw [disjoint_left]
    intro v hv hw
    obtain ⟨x,hx,hxv⟩ := mem_map.mp hv
    obtain ⟨y,hy,hyv⟩ := mem_map.mp hw
    have he : x = y := emb.injective (hxv.trans hyv.symm)
    have hIndices : idx i.2 ≠ idx j.2 := fun h => hne (Prod.ext (Subsingleton.elim _ _) (idx.injective h))
    exact disjoint_left.mp (hDis _ _ hIndices) hx (he.symm ▸ hy)
  have hDCover (v : W) (hv : v ∉ Z) : ∃ i : Fin 1 × Fin (7*q'), v ∈ P i.2 := by
    let w : ↥Zᶜ := ⟨v,mem_compl.mpr hv⟩
    obtain ⟨i,hi⟩ := hCover w
    exact ⟨(0,idx.symm i),mem_map.mpr ⟨w,by rwa [idx.apply_symm_apply],rfl⟩⟩
  have hU (profiles : W → Finset W) (i : Fin 1 × Fin (7*q')) :
      UniformProfileCell profiles (P i.2) (P i.2) 1 ε₀ := by
    intro j _
    simp only [Nat.cast_one,div_one,sub_self,abs_zero]
    exact mul_nonneg hε₀ (Nat.cast_nonneg _)
  obtain ⟨F,hApart,_⟩ := hN (K := 1) (l := 7) (q := q') G Z R P (fun i => P i.2)
    m r e endpointCap endpointBudget routeCap ε₀ a η hq' (by decide) (by decide) hDP hDCover
    (fun i => hDSize i.2) (fun i => by rw [one_mul,hDSize]) (fun _ => Subset.rfl)
    hDZ (hU (inProfile G)) (hU (outProfile G)) hBudget
    (fun j => by simpa using hIn j.2) (fun j => by simpa using hOut j.2)
    hRoom hLoop hRoutes hm hNmin hHall hPay hε₀ ha hη hη1 (by simpa using hScale) hCTol hCLoss
    hGap hCut hδ hδ1 hFloor (by simpa using hSTol) hSLoss hReg hSup
  have hDegree := winding_exceptional_reserve_exact_semidegrees (fun (j : Fin 1 × Fin (7*q')) => P j.2)
    hq' (by decide : 2 ≤ 7) m (fun i => hDSize i.2) hDP hDCover F hApart
  have hDExact (v : W) : let d := if v ∈ Z then 7*r else r
      inDegree (⨆ i, ⨆ j, (F i j).digraph) v = d ∧
        outDegree (⨆ i, ⨆ j, (F i j).digraph) v = d := by
    simpa only [Fintype.card_fin,one_mul] using hDegree v
  obtain ⟨E,_,hApartE,hExact⟩ := project_wound_interval_family_to_parity_packets Z X hq F hApart hDExact
  exact ⟨E,hApartE,hExact⟩

/-- The unrefined seven-interval case of Lemma 7.6 supplies a packet
family for Lemma 10.5, with the ordinary deletion budget. -/
theorem pack_parity_packets_on_winding_intervals
    (d δ ε ν τ γ : ℝ) (hν : 0 < ν) (hWidth : ε+ν ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 2*ε < d)
    (hCost : ν ≤ (d-2*ε)*τ) (hDegrees : γ ≤ d-2*ε) (hTol : 2*δ ≤ ε) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {q : ℕ}
      (G : Digraph W) (Z : Finset W) [Nonempty ↥Zᶜ]
      (X : Fin (14*q) → Finset ↥Zᶜ) (hq : 0 < q)
      (R : Fin 7 → Digraph (Fin (2*q)))
      (m r e endpointCap endpointBudget routeCap : ℕ) (ε₀ a η : ℝ),
      let hk : 0 < 14*q := by omega
      let A := cyclicCluster X hk
      let emb : ↥Zᶜ ↪ W := Embedding.subtype _
      let q' := 2*q
      let idx : Fin (7*q') ≃ Fin (14*q) := finCongr (by dsimp [q']; omega)
      let P (i : Fin (7*q')) := (X (idx i)).map emb
      let E (j : Fin 7) := (windingEndpointPositions (⟨0,by dsimp [q']; omega⟩ : Fin q')).biUnion
        (fun i => P (intervalPosition j i))
      let loss := endpointCap+(routeCap+2)+2*endpointCap
      (∀ i j, i ≠ j → Disjoint (X i) (X j)) →
      (∀ x, ∃ i, x ∈ X i) →
      (∀ i, (X i).card = m) →
      2*Z.card < endpointCap*(endpointBudget+1) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+7*r < inNeighbours G (E j) z) →
      (∀ j z, z ∈ Z → 2*Z.card+endpointBudget*m+7*r < outTo G (E j) z) →
      2*(routeCap+2+2*endpointCap)+e < m-endpointCap →
      (∀ j i, ¬(R j).Adj i i) →
      (∀ j, ∃ radius growth cutoff budget : ℕ, IsRobustAt (R j) radius cutoff ∧ 0 < growth ∧
        2*(budget+1)+growth ≤ radius ∧
        (∀ i, cutoff+2*(budget+1) ≤ outDegree (R j) i) ∧ (∀ i, cutoff ≤ inDegree (R j) i) ∧
        Z.card*(2*(q'/growth+3)) < routeCap*(budget+1)) →
      loss < m → N ≤ m-loss →
      ε*(m:ℝ)+1 ≤ (d-2*ε)*((m-loss:ℕ):ℝ) →
      (m:ℝ)*δ+loss ≤ ((m-loss:ℕ):ℝ)*ε →
      0 ≤ ε₀ → 0 ≤ a → 0 < η → η ≤ 1 →
      ε₀ ≤ η → 2*(ε₀+a) ≤ η → (r:ℝ) ≤ a*((m:ℝ)*η) →
      η < d-ε₀-a → (m:ℝ)*η ≤ (e:ℝ)+1 →
      0 < δ → δ ≤ 1 → 2*ε₀ ≤ d →
      2*(2*ε₀+a) ≤ δ → (r:ℝ) ≤ a*((m:ℝ)*δ) →
      (∀ j i h, (R j).Adj i h →
        IsUniform G ε₀ (P (intervalPosition j i)) (P (intervalPosition j h)) ∧
          d ≤ density G (P (intervalPosition j i)) (P (intervalPosition j h))) →
      (∀ i, IsLowerSuperregularPair G ε₀ d (P i) (P (finRotate (7*q') i))) →
      let coord := (exceptionalCoordinates Z).toEmbedding
      let D := pullDirectedPair coord coord G
      ∃ F : Fin r → ParityExceptionalPacket D A q,
        Pairwise (fun i j => Disjoint (F i).original (F j).original) ∧
        ∀ v, inDegree (ordinaryCycleHost (⨆ i, (F i).original)) v ≤ r ∧
          outDegree (ordinaryCycleHost (⨆ i, (F i).original)) v ≤ r := by
  obtain ⟨N,hN⟩ := pack_parity_packets_with_exact_semidegrees.{u}
    d δ ε ν τ γ hν hWidth hε hε1 hτγ hγ hd hCost hDegrees hTol
  refine ⟨N,?_⟩
  intro W _ q G Z _ X hq R m r e endpointCap endpointBudget routeCap ε₀ a η
    hk A emb q' idx P E loss hDis hCover hSize hBudget hIn hOut hRoom hLoop hRoutes hm hNmin
    hHall hPay hε₀ ha hη hη1 hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor hSTol hSLoss
    hReg hSup coord D
  obtain ⟨F,hF,hDegree⟩ := hN G Z X hq R m r e endpointCap endpointBudget routeCap ε₀ a η
    hDis hCover hSize hBudget hIn hOut hRoom hLoop hRoutes hm hNmin hHall hPay hε₀ ha hη hη1
    hScale hCTol hCLoss hGap hCut hδ hδ1 hFloor hSTol hSLoss hReg hSup
  refine ⟨F,hF,?_⟩
  intro v
  obtain ⟨hi,ho⟩ := ordinaryCycleHost_semidegrees_le (⨆ i, (F i).original) v
  exact ⟨hi.trans_eq (hDegree (.inl v)).1,ho.trans_eq (hDegree (.inl v)).2⟩

/-- Remove the prepared exceptional factors before routing the parity
blocks. Their ordinary degree bound pays for the deletion on every pair. -/
theorem parity_routing_host_after_packet_deletion {V Z : Type*} [Fintype V] {k q r m : ℕ}
    (D : Digraph (V ⊕ Z)) (A : ℕ → Finset V) (E : Fin r → ParityExceptionalPacket D A q)
    (X : Fin k → Finset V) (hm : 0 < m) (hSize : ∀ i, (X i).card = m)
    (ε η d a : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hTol : 2*(ε+a) ≤ η) (hPay : (r:ℝ) ≤ a*((m:ℝ)*η))
    (hPair : ∀ i, IsLowerSuperregularPair (ordinaryCycleHost D) ε d (X i) (X (finRotate k i)))
    (hDegree : ∀ v, inDegree (ordinaryCycleHost (⨆ i, (E i).original)) v ≤ r ∧
      outDegree (ordinaryCycleHost (⨆ i, (E i).original)) v ≤ r) :
    let R := ordinaryCycleHost (D \ (⨆ i, (E i).original))
    liftOrdinaryCycleArcs Z R ≤ D ∧
      (∀ i, Disjoint (liftOrdinaryCycleArcs Z R) (E i).original) ∧
      ∀ i, IsLowerSuperregularPair R η d (X i) (X (finRotate k i)) := by
  intro R
  have hLe (i : Fin r) : (E i).original ≤ D := by
    unfold ParityExceptionalPacket.original
    exact sup_le (sup_le (sup_le (sup_le (E i).paths₃.original_le (E i).paths₅.original_le)
      (E i).paths₄.original_le) (E i).paths₂.original_le)
      (sup_le (sup_le (E i).paths₆.original_le (E i).paths₇.original_le) (E i).paths₁.original_le)
  have hLift : liftOrdinaryCycleArcs Z R ≤ D \ (⨆ i, (E i).original) :=
    liftOrdinaryCycleArcs_le_original_host le_rfl
  refine ⟨fun _ _ h => (hLift h).1,?_,?_⟩
  · intro i
    rw [disjoint_iff_inf_le]
    rintro x y ⟨hr,he⟩
    exact (hLift hr).2 (Digraph.iSup_adj.mpr ⟨i,he⟩)
  · intro i
    change IsLowerSuperregularPair (ordinaryCycleHost D \ ordinaryCycleHost (⨆ i, (E i).original))
      η d (X i) (X (finRotate k i))
    have hOrdLe : ordinaryCycleHost (⨆ i, (E i).original) ≤ ordinaryCycleHost D :=
      fun _ _ h => (iSup_le hLe : (⨆ i, (E i).original) ≤ D) h
    have hPos (j : Fin k) : (X j).Nonempty := card_pos.mp ((hSize j).symm ▸ hm)
    exact IsLowerSuperregularPair.after_bounded_arc_deletion
      hOrdLe r hDegree (X i) (X (finRotate k i)) (hPos i) (hPos (finRotate k i)) m
      (hSize i) (hSize _) ε η d a hη hη1 ha hd hTol hPay (hPair i)

end OverfullWork.DirectedRobustExpansion
