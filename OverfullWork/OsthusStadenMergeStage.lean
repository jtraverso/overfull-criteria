module

public import OverfullWork.OsthusStadenCorridors

@[expose] public section


/-! Apply the merging stage to a block from Osthus–Staden §5.11. -/
namespace OverfullWork.DirectedRobustExpansion
open Finset
open scoped Classical
universe u
variable {V : Type u}

/-- The two kinds of links used in §5.11. A winding link crosses a pair
of red clusters. An exceptional vertex links two reduced cycles. -/
inductive OsthusStadenLink {I : Type*} (σ : Equiv.Perm V) (S : I → Finset V) (i j : I) : Prop
  | winding (A : ℕ → Finset V) (n p : ℕ) (hp : p < n)
      (hStart : A 0 = (S i).image σ) (hEnd : A n = S j)
      (hOrdinary : ∀ l < n, l ≠ p → (A l).image σ = A (l+1))
      (hRed : ∃ x ∈ A p, σ x ∈ A (p+1))
      (hOff : ∀ l < n, ∀ x ∈ A l, ∀ c, x ∉ S c)
  | exceptional (x : V) (hPred : touchesCut σ (S i) (σ.symm x))
      (hNext : touchesCut σ (S j) (σ x))

theorem OsthusStadenLink.bridge [Fintype V] {I : Type*}
    {σ : Equiv.Perm V} {S : I → Finset V} {i j : I} (h : OsthusStadenLink σ S i j) :
    ∃ x y, touchesCut σ (S i) x ∧ touchesCut σ (S j) y ∧
      ∃ L : List V, x ∈ L ∧ y ∈ L ∧ L.IsChain (fun a b => (∀ c, a ∉ S c) ∧ σ a = b) := by
  cases h with
  | winding A n p hp hStart hEnd hOrdinary hRed hOff =>
    exact bridge_between_selected_pairs σ S i j A n p hp hStart hEnd hOrdinary hRed hOff
  | exceptional x hPred hNext =>
    exact bridge_of_exceptional_vertex σ S i j x hPred hNext

/-- A whole block of §5.11, from prepared intervals, red vertices,
connector paths and reserve bounds. -/
theorem exists_hamilton_batch_of_black_intervals (d ε ν τ γ : ℝ) (hν : 0 < ν)
    (hWidth : ε+ν ≤ τ) (hε : 0 ≤ ε) (hτγ : 16*τ ≤ γ) (hγ : γ ≤ 1) (hd : 0 < d) :
    ∃ N : ℕ, ∀ {W : Type u} [Fintype W] {k n : ℕ} (σ : Fin k → Equiv.Perm W)
      (A : Fin n → ℕ → Finset W) (len q : Fin n → ℕ),
      let S := fun i => A i (q i)
      ∀ (D : ∀ i, Digraph (↑(S i)))
        (target : ∀ i, ↑(S i) ↪ W) (p : ∀ i, Fin k → Equiv.Perm (↑(S i)))
        (r : Fin n → Fin n → Prop) (i₀ : Fin n) (black redIn redOut : Set W),
      (∀ i, q i ≤ len i) →
      (∀ v ∈ black, ∃ i j, j ≤ len i ∧ v ∈ A i j) →
      (∀ f i j, j < len i → (A i j).image (σ f) = A i (j+1)) →
      (∀ f v, v ∈ redIn → σ f v ∈ black) →
      (∀ f v, v ∈ redOut → (σ f).symm v ∈ black) →
      (∀ f v, v ∉ black → v ∉ redIn → v ∉ redOut →
        σ f v ∈ black ∨ σ f v ∈ redIn ∨ σ f v ∈ redOut) →
      (∀ i j (x : S i), σ j x.val = target i (p i j x)) →
      (∀ f g, f ≠ g → ∀ v, σ f v ≠ σ g v) →
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
      (∀ i, (S i).Nonempty ∧ N ≤ (S i).card) →
      (∀ i, (k:ℝ)+ν*((S i).card:ℝ) ≤ d*τ*((S i).card:ℝ)) →
      (∀ i, γ*((S i).card:ℝ)+(k:ℝ) ≤ d*((S i).card:ℝ)) →
      (∀ i, ∀ X Y : Finset (↑(S i)), ε*((S i).card:ℝ) ≤ (X.card:ℝ) →
        ε*((S i).card:ℝ) ≤ (Y.card:ℝ) →
        d*(X.card:ℝ)*(Y.card:ℝ) ≤ (incidences (D i) X Y:ℝ)) →
      (∀ i v, d*((S i).card:ℝ) ≤ (inDegree (D i) v:ℝ)) →
      (∀ i v, d*((S i).card:ℝ) ≤ (outDegree (D i) v:ℝ)) →
      (∀ i, Relation.EqvGen r i₀ i) →
      (∀ f i j, r i j → OsthusStadenLink (σ f) S i j) →
      ∃ ρ : Fin k → Equiv.Perm W, (∀ f, HasSpanningCycle (fun x y => ρ f x = y)) ∧
        (∀ f g, f ≠ g → ∀ v, ρ f v ≠ ρ g v) ∧
        (∀ f x, (∀ i, x ∉ S i) → ρ f x = σ f x) ∧
        ∀ i, ∃ M : Fin k → Equiv.Perm (↑(S i)),
          (∀ f x, (D i).Adj x (M f x)) ∧ ∀ f (x : S i), ρ f x.val = target i (M f x) := by
  obtain ⟨N,hN⟩ := exists_hamilton_batch_of_merge_reserves.{u} d ε ν τ γ hν hWidth hε hτγ hγ hd
  refine ⟨N,?_⟩
  intro W _ k n σ A len q S D target p r i₀ black redIn redOut
    hq hBlack hCells hRedIn hRedOut hEx hTarget hOriginal hDis hn hCost hDeg hRect hIn hOut hConn hLink
  apply hN σ S D target p r i₀ hTarget hOriginal hDis hn hCost hDeg hRect hIn hOut hConn
  · intro f
    apply cover_of_selected_black_intervals (σ f) A len q hq (hCells f)
    intro v
    obtain ⟨w,hw,hvw⟩ := every_orbit_hits_black (σ f) black redIn redOut
      (hRedIn f) (hRedOut f) (hEx f) v
    exact ⟨w,hvw,hBlack w hw⟩
  · exact fun f i j h => (hLink f i j h).bridge

end OverfullWork.DirectedRobustExpansion
