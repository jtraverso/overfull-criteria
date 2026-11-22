module

public import OverfullWork.DirectedPathCoverAbsorption
public import OverfullWork.DirectedRungCycleEmbedding
public import OverfullWork.DirectedLadderPartition

@[expose] public section


/-! Assembly of the absorbing cycle in Lo–Patel Theorem 4.11 from a
covering family of disjoint ladders. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Finset DirectedRungCycle DirectedRobustExpansion
open scoped Classical
variable {V J : Type*} [Fintype V]

/-- An actual small cycle that can incorporate any bounded family of
mutually disjoint paths outside it. -/
structure AbsorbingCycle (D : Digraph V) (d : ℕ) where
  root : V
  vertices : List V
  head : vertices.head? = some root
  simple : vertices.Nodup
  closed : (vertices ++ [root]).IsChain D.Adj
  absorbs : ∀ requests : List (PathRequest D), requests.length ≤ d →
    requests.Pairwise (fun P Q => List.Disjoint P.vertices Q.vertices) →
    (∀ P ∈ requests, List.Disjoint vertices P.vertices) →
    ∃ result : List V, result.Perm (vertices ++ requests.flatMap PathRequest.vertices) ∧
      result.Nodup ∧ result.head? = some root ∧ (result ++ [root]).IsChain D.Adj

theorem exists_absorbing_cycle_of_ladders [Fintype J] [Nonempty J] (D : Digraph V)
    {d r r' t L : ℕ} (hRobust : IsRobustAt D r t) (hr' : 0 < r')
    (hL : Fintype.card V/r'+4 ≤ L)
    (s z : J → V) (q : J → ℕ) (A : ∀ j, Ladder D (s j) (z j) (q j))
    (hDisjoint : ∀ j k, j ≠ k → Disjoint (A j).vertices (A k).vertices)
    (hCover : ∀ x y, d ≤ (covering D s z x y).card)
    (M : Finset V) (hM : ∀ j, (A j).vertices ⊆ M)
    (hBudget : M.card+(∑ j, (q j+1))*L+r' ≤ r)
    (hIn : ∀ v, t ≤ inDegree D v)
    (hOut : ∀ v, t+M.card+(∑ j, (q j+1))*L ≤ outDegree D v) :
    ∃ C : AbsorbingCycle D d, C.vertices.length ≤ M.card+(∑ j, (q j+1))*L := by
  classical
  let K := Σ j : J, Fin (q j+1)
  let _ : Nonempty K := ⟨⟨Classical.choice ‹Nonempty J›, 0⟩⟩
  have hCard : Fintype.card K = ∑ j, (q j+1) := by simp [K]
  let m := Fintype.card K-1
  have hm : Fintype.card K = m+1 := by
    have h := Fintype.card_pos (α := K)
    dsimp [m]
    omega
  let e := Fintype.equivFinOfCardEq hm
  let a : Fin (m+1) → V := fun i => (A (e.symm i).1).spine (evenLeft (e.symm i).2)
  let b : Fin (m+1) → V := fun i => (A (e.symm i).1).spine (evenRight (e.symm i).2)
  let body : Fin (m+1) → List V := fun i => (A (e.symm i).1).middle (e.symm i).2
  let piece : Fin (m+1) → List V := fun i => a i :: (body i ++ [b i])
  have hPiece : ∀ i, piece i = (A (e.symm i).1).ordinaryVertices (e.symm i).2 := fun _ => rfl
  have hRoutes : ∀ i, DirectedListRoutes.Route D (a i) (b i) (body i ++ [b i]) :=
    fun i => (A (e.symm i).1).ordinary_middle_route _
  have hSimple : ∀ i, (piece i).Nodup := by
    intro i
    rw [hPiece]
    exact (A _).ordinaryVertices_nodup _
  have hApart : ∀ k l : K, k ≠ l → List.Disjoint
      ((A k.1).ordinaryVertices k.2) ((A l.1).ordinaryVertices l.2) := by
    rintro ⟨j,i⟩ ⟨k,f⟩ h
    by_cases hjk : j = k
    · subst k
      exact (A j).ordinaryVertices_disjoint i f (fun hi => h (by cases hi; rfl))
    · intro v hv hv'
      exact Finset.disjoint_left.mp (hDisjoint j k hjk)
        ((A j).ordinaryVertices_mem i hv) ((A k).ordinaryVertices_mem f hv')
  have hDisj : ∀ i j, i ≠ j → List.Disjoint (piece i) (piece j) := by
    intro i j hij
    rw [hPiece, hPiece]
    exact hApart _ _ (fun h => hij (e.symm.injective h))
  have hMarks : ∀ i w, w ∈ piece i → w ∈ M := by
    intro i w hw
    rw [hPiece] at hw
    exact hM _ ((A _).ordinaryVertices_mem _ hw)
  have haMem : ∀ i, a i ∈ piece i := by intro i; simp [piece]
  have hbMem : ∀ i, b i ∈ piece i := by intro i; simp [piece]
  have ha : Function.Injective a := by
    intro i j h
    by_contra hn
    exact hDisj i j hn (haMem i) (h ▸ haMem j)
  have hb : Function.Injective b := by
    intro i j h
    by_contra hn
    exact hDisj i j hn (hbMem i) (h ▸ hbMem j)
  have hab : ∀ i j, a i ≠ b j := by
    intro i j he
    by_cases h : i = j
    · subst j
      exact (List.nodup_cons.mp (hSimple i)).1 (he ▸ (by simp : b i ∈ body i ++ [b i]))
    · exact hDisj i j h (haMem i) (he ▸ hbMem j)
  have hSize : m+1 = ∑ j, (q j+1) := hm.symm.trans hCard
  obtain ⟨link, hOrder, hWord, hLength⟩ :=
    exists_embedded_rung_cycle D hRobust hr' hL a b body M ha hb hab hSimple
      hDisj hMarks (by rwa [hSize]) hIn (fun v => by rw [hSize]; exact hOut v)
  let rest := List.ofFn (fun i : Fin m => i.succ)
  have hEq : List.ofFn (id : Fin (m+1) → Fin (m+1)) = 0 :: rest := List.ofFn_succ
  rw [hEq] at hOrder hWord hLength
  have hDistinct : (0 :: rest).Nodup := by rw [← hEq]; exact List.nodup_ofFn.mpr Function.injective_id
  have hAll : ∀ i, i ∈ 0 :: rest := by
    intro i
    rw [← hEq]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  let index : ∀ j, Fin (q j+1) ↪ Fin (m+1) := fun j =>
    ⟨fun i => e ⟨j,i⟩, fun _ _ he => by exact eq_of_heq (Sigma.mk.inj (e.injective he)).2⟩
  have hIndices : ∀ j k, j ≠ k → Disjoint (Set.range (index j)) (Set.range (index k)) := by
    intro j k h
    apply Set.disjoint_left.mpr
    rintro _ ⟨i, rfl⟩ ⟨l, he⟩
    exact h (congrArg Sigma.fst (e.injective he)).symm
  have hIndex : ∀ j i, e.symm (index j i) = (⟨j,i⟩ : K) := fun j i => e.symm_apply_apply ⟨j,i⟩
  have hA : ∀ j i, a (index j i) = (A j).spine (evenLeft i) := by intro j i; dsimp only [a]; rw [hIndex]
  have hB : ∀ j i, b (index j i) = (A j).spine (evenRight i) := by intro j i; dsimp only [b]; rw [hIndex]
  have hBody : ∀ j i, body (index j i) = (A j).middle i := by intro j i; dsimp only [body]; rw [hIndex]
  obtain ⟨hHead, hClose⟩ := closed_word D a b link body 0 rest hRoutes hOrder
  let C : AbsorbingCycle D d := {
    root := a 0
    vertices := word a b link body (0 :: rest)
    head := hHead
    simple := hWord
    closed := hClose
    absorbs := fun requests hReq hP hOutside => by
      obtain ⟨final, hPerm, hFinal⟩ :=
        absorb_path_cover D d s z q A index hIndices a b link 0 rest hDistinct hAll
          hOrder hA hB hCover body hBody hRoutes hWord requests hReq hP hOutside
      exact ⟨word a b link final (0 :: rest), hPerm, hFinal⟩ }
  exact ⟨C, by simpa only [C, ← hSize] using hLength⟩

end OverfullWork.DirectedAbsorbingLadder
