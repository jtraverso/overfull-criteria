module

public import OverfullWork.EndpointBootstrapCounting

@[expose] public section


/-! # Construct alternating layers and find a large layer

The advancing operator has proved subset, growth and predecessor
properties. Its iterates are actual finite sets. A bounded growth
argument constructs a layer large enough for the terminal meeting.
-/
namespace OverfullWork.PairedRoutes
open SimpleGraph Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option maxHeartbeats 24000000

structure LayerSystem (τ : Equiv.Perm V) (F : SimpleGraph V) (U A : Finset V)
    (m cutoff g q : ℕ) where
  card_part : A.card=m
  card_compl : Aᶜ.card=m
  involutive : ∀ x, τ (τ x)=x
  closed : ∀ x ∈ U, τ x ∈ U
  same_side : ∀ x ∈ U, (x ∈ A ↔ τ x ∈ A)
  advance : Finset V → Finset V → Finset V
  subset : ∀ D, (D=A ∨ D=Aᶜ) → ∀ X, X ⊆ D ∩ U → advance D X ⊆ Dᶜ ∩ U
  growth : ∀ D, (D=A ∨ D=Aᶜ) → ∀ X, X ⊆ D ∩ U → cutoff ≤ X.card → X.card+cutoff ≤ m →
    X.card+g ≤ (advance D X).card
  predecessors : ∀ D, (D=A ∨ D=Aᶜ) → ∀ X, X ⊆ D ∩ U → ∀ z ∈ advance D X,
    q ≤ (X.filter (fun x => F.Adj (τ x) z)).card

namespace LayerSystem
variable {τ : Equiv.Perm V} {F : SimpleGraph V} {U A : Finset V} {m cutoff g q : ℕ}

def side (D : Finset V) : ℕ → Finset V
  | 0 => D
  | n+1 => (side D n)ᶜ

theorem side_choice (D : Finset V) (hD : D=A ∨ D=Aᶜ) (n : ℕ) : side D n=A ∨ side D n=Aᶜ := by
  induction n with
  | zero => exact hD
  | succ n ih =>
    rcases ih with ih|ih
    · exact Or.inr (by rw [side,ih])
    · exact Or.inl (by rw [side,ih,compl_compl])

theorem side_card (s : LayerSystem τ F U A m cutoff g q) (D : Finset V) (hD : D=A ∨ D=Aᶜ) : D.card=m := by
  rcases hD with rfl|rfl
  · exact s.card_part
  · exact s.card_compl

theorem mate_mem_side (s : LayerSystem τ F U A m cutoff g q) (D : Finset V) (hD : D=A ∨ D=Aᶜ)
    (x : V) (hxU : x ∈ U) (hxD : x ∈ D) : τ x ∈ D := by
  rcases hD with rfl|rfl
  · exact (s.same_side x hxU).mp hxD
  · exact mem_compl.mpr (fun hm => (mem_compl.mp hxD) ((s.same_side x hxU).mpr hm))

noncomputable def layers (s : LayerSystem τ F U A m cutoff g q) (D X : Finset V) : ℕ → Finset V
  | 0 => X
  | n+1 => s.advance (side D n) (s.layers D X n)

theorem layers_subset (s : LayerSystem τ F U A m cutoff g q) (D X : Finset V)
    (hD : D=A ∨ D=Aᶜ) (hX : X ⊆ D ∩ U) (n : ℕ) : s.layers D X n ⊆ side D n ∩ U := by
  induction n with
  | zero => exact hX
  | succ n ih => exact s.subset (side D n) (side_choice D hD n) (s.layers D X n) ih

theorem layers_card (s : LayerSystem τ F U A m cutoff g q) (D X : Finset V)
    (hD : D=A ∨ D=Aᶜ) (hX : X ⊆ D ∩ U) (n : ℕ) : (s.layers D X n).card ≤ m := by
  have hs := (s.layers_subset D X hD hX n).trans inter_subset_left
  have hh := card_le_card hs
  rwa [s.side_card _ (side_choice D hD n)] at hh

theorem exists_large (s : LayerSystem τ F U A m cutoff g q) (D X : Finset V)
    (hD : D=A ∨ D=Aᶜ) (hX : X ⊆ D ∩ U) (hLow : cutoff ≤ X.card) (hg : 0 < g) :
    ∃ j ≤ m/g+1, m < (s.layers D X j).card+cutoff := by
  apply exists_large_layer (s.layers D X) m cutoff g hg hLow (s.layers_card D X hD hX)
  intro j hj hWindow
  exact s.growth (side D j) (side_choice D hD j) (s.layers D X j) (s.layers_subset D X hD hX j) hj hWindow

theorem layers_predecessors (s : LayerSystem τ F U A m cutoff g q) (D X : Finset V)
    (hD : D=A ∨ D=Aᶜ) (hX : X ⊆ D ∩ U) (j : ℕ) (z : V) (hz : z ∈ s.layers D X (j+1)) :
    q ≤ ((s.layers D X j).filter (fun x => F.Adj (τ x) z)).card :=
  s.predecessors (side D j) (side_choice D hD j) (s.layers D X j) (s.layers_subset D X hD hX j) z hz

end LayerSystem
end OverfullWork.PairedRoutes
