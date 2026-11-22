module

public import OverfullWork.DirectedLadderAbsorption

@[expose] public section


/-! Greedy use of the disjoint embedded ladders in Lo–Patel Corollary 4.7.
The cover condition belongs to the absorbing cycle. The paths to be
absorbed are allowed to be singletons. -/
namespace OverfullWork.DirectedAbsorbingLadder

open Finset DirectedListRoutes DirectedRungCycle
open scoped Classical
variable {V I J : Type*}

structure PathRequest (D : Digraph V) where
  source : V
  target : V
  tail : List V
  route : Route D source target tail
  simple : (source :: tail).Nodup

def PathRequest.vertices {D : Digraph V} (P : PathRequest D) : List V :=
  P.source :: P.tail

/-- Pairs that can attach a path with ends `x,y` to a chosen ladder. -/
noncomputable def covering [Fintype J] (D : Digraph V) (s t : J → V) (x y : V) : Finset J :=
  univ.filter fun j => D.Adj (s j) x ∧ D.Adj y (t j)

private theorem PathRequest.extended_route {D : Digraph V} (P : PathRequest D) {a b : V}
    (ha : D.Adj a P.source) (hb : D.Adj P.target b) :
    Route D a b (P.vertices ++ [b]) := by
  have h : Route D a P.target P.vertices :=
    ⟨.cons_cons ha P.route.1, by simpa only [PathRequest.vertices, List.getLast?_cons_cons]
      using P.route.2⟩
  exact snoc_route D h hb

/-- Absorb a family of pairwise disjoint external paths. The only
matching selection is to avoid the previously used ladder indices. -/
theorem absorb_path_cover [Fintype J] (D : Digraph V) (d : ℕ)
    (s t : J → V) (q : J → ℕ) (ladder : ∀ j, Ladder D (s j) (t j) (q j))
    (index : ∀ j, Fin (q j+1) ↪ I)
    (hIndices : ∀ j k, j ≠ k → Disjoint (Set.range (index j)) (Set.range (index k)))
    (a b : I → V) (link : I → List V) (first : I) (rest : List I)
    (hDistinct : (first :: rest).Nodup) (hAll : ∀ i : I, i ∈ first :: rest)
    (hOrder : ((first :: rest) ++ [first]).IsChain
      (fun i j => Route D (b i) (a j) (link i ++ [a j])))
    (hA : ∀ j i, a (index j i) = (ladder j).spine (evenLeft i))
    (hB : ∀ j i, b (index j i) = (ladder j).spine (evenRight i))
    (hCover : ∀ x y, d ≤ (covering D s t x y).card)
    (body : I → List V) (hBody : ∀ j i, body (index j i) = (ladder j).middle i)
    (hRoutes : ∀ i, Route D (a i) (b i) (body i ++ [b i]))
    (hSimple : (word a b link body (first :: rest)).Nodup)
    (requests : List (PathRequest D)) (hSize : requests.length ≤ d)
    (hPair : requests.Pairwise (fun P Q => List.Disjoint P.vertices Q.vertices))
    (hOutside : ∀ P ∈ requests, List.Disjoint (word a b link body (first :: rest)) P.vertices) :
    ∃ newBody : I → List V,
      (word a b link newBody (first :: rest)).Perm
        (word a b link body (first :: rest) ++ requests.flatMap PathRequest.vertices) ∧
      (word a b link newBody (first :: rest)).Nodup ∧
      (word a b link newBody (first :: rest)).head? = some (a first) ∧
      (word a b link newBody (first :: rest) ++ [a first]).IsChain D.Adj := by
  classical
  let cycle := fun body => word a b link body (first :: rest)
  have main : ∀ (requests : List (PathRequest D)) (used : Finset J) (body : I → List V),
      used.card+requests.length ≤ d →
      (∀ j ∉ used, ∀ i, body (index j i) = (ladder j).middle i) →
      (∀ i, Route D (a i) (b i) (body i ++ [b i])) →
      (cycle body).Nodup →
      requests.Pairwise (fun P Q => List.Disjoint P.vertices Q.vertices) →
      (∀ P ∈ requests, List.Disjoint (cycle body) P.vertices) →
      ∃ newBody : I → List V, (cycle newBody).Perm
        (cycle body ++ requests.flatMap PathRequest.vertices) ∧
        (cycle newBody).Nodup ∧ ∀ i, Route D (a i) (b i) (newBody i ++ [b i]) := by
    intro requests
    induction requests with
    | nil =>
      intro used body _ _ hR hS _ _
      exact ⟨body, by simp, hS, hR⟩
    | cons P requests ih =>
      intro used body hBudget hOld hR hS hPairs hOut
      let C := covering D s t P.source P.target
      have hC : d ≤ C.card := hCover P.source P.target
      have hPos : 0 < (C \ used).card := by
        have h := card_le_card_sdiff_add_card (s := C) (t := used)
        simp only [List.length_cons] at hBudget
        omega
      obtain ⟨j, hj⟩ := card_pos.mp hPos
      obtain ⟨hjC, hjUsed⟩ := mem_sdiff.mp hj
      obtain ⟨hLeft, hRight⟩ := (mem_filter.mp hjC).2
      obtain ⟨body', hR', hSame, _, hPerm, hSimple', _, _⟩ :=
        (ladder j).absorb_into_rung_cycle (index j) a b link body first rest
          hDistinct hAll hOrder hR hS (hA j) (hB j) (hOld j hjUsed)
          P.vertices (P.extended_route hLeft hRight) P.simple (hOut P (by simp))
      have hRemain : ∀ k ∉ insert j used, ∀ i, body' (index k i) = (ladder k).middle i := by
        intro k hk i
        have hne : j ≠ k := fun h => hk (h ▸ mem_insert_self j used)
        have hRange : index k i ∉ Set.range (index j) := fun hc =>
          Set.disjoint_left.mp (hIndices j k hne) hc ⟨i, rfl⟩
        exact (hSame _ hRange).trans (hOld k (fun h => hk (mem_insert_of_mem h)) i)
      have hOut' : ∀ Q ∈ requests, List.Disjoint (cycle body') Q.vertices := by
        intro Q hQ x hx hqx
        change x ∈ word a b link body' (first :: rest) at hx
        rcases List.mem_append.mp (hPerm.mem_iff.mp hx) with hOldV|hPV
        · exact hOut Q (List.mem_cons_of_mem _ hQ) hOldV hqx
        · exact (List.pairwise_cons.mp hPairs).1 Q hQ hPV hqx
      obtain ⟨final, hFinal, hFinalSimple, hFinalRoutes⟩ :=
        ih (insert j used) body'
          (by rw [card_insert_of_notMem hjUsed]; simpa [List.length_cons, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using hBudget)
          hRemain hR' hSimple' hPairs.of_cons hOut'
      refine ⟨final, hFinal.trans ?_, hFinalSimple, hFinalRoutes⟩
      simpa only [List.flatMap_cons, List.append_assoc] using
        hPerm.append_right (requests.flatMap PathRequest.vertices)
  obtain ⟨final, hFinal, hFinalSimple, hFinalRoutes⟩ :=
    main requests ∅ body (by simpa using hSize) (fun j _ => hBody j)
      hRoutes hSimple hPair hOutside
  exact ⟨final, hFinal, hFinalSimple, closed_word D a b link final first rest hFinalRoutes hOrder⟩

end OverfullWork.DirectedAbsorbingLadder
